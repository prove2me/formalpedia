-- Prove2me | Definitions.Def_DirectedGlobalMincut_Sampling_MaxFlow
-- name    : DirectedGlobalMincut_Sampling_MaxFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:00.998293+00:00
-- url     : https://prove2.me/theorems/d261c75d-eb4f-44f4-b1a0-d2ba448317af
-- title:
--   Maximum-flow oracle, encodings and integral auxiliary translation
-- statement:
--   A maximum-flow query has enumerated vertices and arc identities, distinct source and sink, and finite nonnegative capacities. A feasible source-to-sink flow is nonnegative, obeys its arc capacities, and has zero net inflow at every nonterminal vertex. It is maximum when
--
--   $$\operatorname{value}(g)\le\operatorname{value}(f)\quad\text{for every feasible }g.$$
--
--   Real-capacity and integral-capacity oracle interfaces return an actual maximum flow in a fixed edge-list format. Integral queries return integral maximum flows. Incorrectly encoded queries have the fixed empty answer. No mincut or arborescence algorithm is a primitive.
--
--   For positive cut value $C$, the integral auxiliary translation constructs the compressed network at $q_e=5w_e/(4C)$, replaces infinite capacities by $n-1$, adds supersource and supersink demand arcs, and scales by $4C$. Source-arc capacities become $5w_e$, demand-arc capacities $4C$, and the remaining capacities $4C(n-1)$. Vertices and arc identities of this concrete network are enumerated. Division at $C=0$ is total only as a data definition; the algorithm must handle zero cuts before normalization.
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), §2 maximum-flow reduction and §4.4 auxiliary feasibility, pp.2–3,8–10, p. 3 (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_Compression
import Definitions.Def_CongruencyTU_Machine

namespace DirectedGlobalMincut.Sampling

/-- A maximum-flow instance with an explicit list of arc identities and finite capacities. -/
structure MFProblem (C : Type) where
  n : ℕ
  m : ℕ
  graph : Graph n m
  source : Fin n
  sink : Fin n
  capacity : Fin m → C

def MFProblem.ValidR (Q : MFProblem ℝ) : Prop :=
  Q.source ≠ Q.sink ∧ AllArcs Q.graph ∧ ∀ e, 0 ≤ Q.capacity e

def MFProblem.ValidI (Q : MFProblem ℕ) : Prop :=
  Q.source ≠ Q.sink ∧ AllArcs Q.graph

def MFProblem.real (Q : MFProblem ℕ) : MFProblem ℝ :=
  ⟨Q.n, Q.m, Q.graph, Q.source, Q.sink, fun e => Q.capacity e⟩

noncomputable def MFProblem.net (Q : MFProblem ℝ) : Network (Fin Q.n) (Fin Q.m) :=
  ⟨Q.graph, fun e => ENNReal.ofReal (Q.capacity e), fun _ => 0⟩

def STFlow (Q : MFProblem ℝ) (f : Fin Q.m → ℝ) : Prop :=
  (∀ e, 0 ≤ f e ∧ f e ≤ Q.capacity e) ∧
    ∀ v, v ≠ Q.source → v ≠ Q.sink → balance Q.net f v = 0

noncomputable def flowValue (Q : MFProblem ℝ) (f : Fin Q.m → ℝ) : ℝ :=
  - balance Q.net f Q.source

def MaximumFlow (Q : MFProblem ℝ) (f : Fin Q.m → ℝ) : Prop :=
  STFlow Q f ∧ ∀ g, STFlow Q g → flowValue Q g ≤ flowValue Q f

/-- Fixed edge-list serialization, used by both machines. -/
def encGraphI {n m : ℕ} (G : Graph n m) : List ℤ :=
  [n, m] ++ (List.ofFn (fun e : Fin m => [(G.tail e).val, (G.head e).val])).flatten

def encGraphR {n m : ℕ} (G : Graph n m) : List ℝ :=
  (encGraphI G).map (fun z => z)

def MFProblem.encI (Q : MFProblem ℕ) : List ℤ :=
  [Q.n, Q.m, Q.source.val, Q.sink.val] ++
    (List.ofFn (fun e : Fin Q.m =>
      [(Q.graph.tail e).val, (Q.graph.head e).val, Q.capacity e])).flatten

def MFProblem.encR (Q : MFProblem ℝ) : List ℝ :=
  ([Q.n, Q.m, Q.source.val, Q.sink.val] : List ℝ) ++
    (List.ofFn (fun e : Fin Q.m =>
      ([(Q.graph.tail e).val, (Q.graph.head e).val, Q.capacity e] : List ℝ))).flatten

def AnswerI (Q : MFProblem ℕ) (xs : List ℤ) : Prop :=
  ∃ f : Fin Q.m → ℕ, xs = List.ofFn (fun e => (f e : ℤ)) ∧
    MaximumFlow Q.real (fun e => (f e : ℝ))

def AnswerR (Q : MFProblem ℝ) (xs : List ℝ) : Prop :=
  ∃ f : Fin Q.m → ℝ, xs = List.ofFn f ∧ MaximumFlow Q f

/-- The oracle is permitted to solve only maximum flow. Invalid requests have a fixed empty answer. -/
def IsMFOracleI (O : CongruencyTU.Oracle) : Prop :=
  (∀ Q : MFProblem ℕ, Q.ValidI → AnswerI Q (O Q.encI)) ∧
    ∀ xs, (¬ ∃ Q : MFProblem ℕ, Q.ValidI ∧ xs = Q.encI) → O xs = []

def IsMFOracleR (O : List ℝ → List ℝ) : Prop :=
  (∀ Q : MFProblem ℝ, Q.ValidR → AnswerR Q (O Q.encR)) ∧
    ∀ xs, (¬ ∃ Q : MFProblem ℝ, Q.ValidR ∧ xs = Q.encR) → O xs = []

/-- The integer auxiliary query used on a positive cut value C. Root-entering arcs are still
present in G but have zero projection in the auxiliary problem. -/
noncomputable def normalizedQ {m : ℕ} (C : ℕ) (w : Fin m → ℕ) (e : Fin m) : ℝ :=
  5 * (w e : ℝ) / (4 * (C : ℝ))

noncomputable def auxiliaryDemandNodes {n m : ℕ} (G : Graph n m) (r : Fin n)
    (T : Finset (Fin m)) (C : ℕ) (w : Fin m → ℕ) :
    Finset (CompressedNode G r T) := by
  classical
  exact Finset.univ.filter (fun v => (compressedNetwork G r T (normalizedQ C w)).demand v ≠ 0)

abbrev IntegralAuxVertex {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :=
  Option (Option (CompressedNode G r T))

abbrev IntegralAuxArc {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m))
    (C : ℕ) (w : Fin m → ℕ) :=
  ↥((compressedNetwork G r T (normalizedQ C w)).graph.arcs) ⊕
    ↥(auxiliaryDemandNodes G r T C w)

/-- Enumerates the actual compressed arcs, adds supersource/supersink demand arcs, caps all
infinite auxiliary arcs by n-1, and scales everything by 4C. Validity requires C>0 at use. -/
noncomputable def integralAuxiliaryQuery {n m : ℕ} (G : Graph n m) (r : Fin n)
    (T : Finset (Fin m)) (C : ℕ) (w : Fin m → ℕ) : MFProblem ℕ := by
  classical
  let H := compressedNetwork G r T (normalizedQ C w)
  let V := IntegralAuxVertex G r T
  let A := IntegralAuxArc G r T C w
  let ev := Fintype.equivFin V
  let ea := Fintype.equivFin A
  let tails : A → V := fun a => match a with
    | .inl a => some (some a.val.1)
    | .inr v => if H.demand v.val < 0 then none else some (some v.val)
  let heads : A → V := fun a => match a with
    | .inl a => some (some a.val.2)
    | .inr v => if H.demand v.val < 0 then some (some v.val) else some none
  let caps : A → ℕ := fun a => match a with
    | .inl a => match a.val with
      | (.inl _, .inr (.inl e)) => 5 * w e
      | _ => 4 * C * (n - 1)
    | .inr _ => 4 * C
  exact ⟨Fintype.card V, Fintype.card A,
    ⟨fun e => ev (tails (ea.symm e)), fun e => ev (heads (ea.symm e)), Finset.univ⟩,
    ev none, ev (some none), fun e => caps (ea.symm e)⟩

end DirectedGlobalMincut.Sampling


