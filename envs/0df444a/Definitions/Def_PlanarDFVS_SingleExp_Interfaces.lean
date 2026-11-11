-- Prove2me | Definitions.Def_PlanarDFVS_SingleExp_Interfaces
-- name    : PlanarDFVS_SingleExp_Interfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:59.977267+00:00
-- url     : https://prove2.me/theorems/fd78b254-989a-473f-ba77-be3fd29eefb4
-- title:
--   §2–§5 — canonical inputs and uniform algorithm guarantees
-- statement:
--   The DFVS input is $n$, binary budget $k$, and the $n\times n$ directed adjacency-support bits, including diagonal loop bits. It contains no embedding, optimum or correctness certificate. Every multigraph is represented; duplicate arcs do not change directed cycles. Encoded input size counts binary values and cell delimiters. Outputs use a binary vertex-subset mask and a separate Fail flag.
--
--   For a plane protected instance, the input additionally contains $P$ and the inherited cyclic orders restricted to one representative of each directed parallel class. Removing incidences cannot increase alternation, so protection of all originally positive vertices remains sufficient; the theorem demands correctness for the original full multigraph. This compressed plane interface avoids charging an arbitrarily long duplicate list as $n$-polynomial. It is a representation convention, not a free compression instruction.
--
--   For weighted feedback arc sets, the full arc list is input. Finite real costs use arithmetic registers; rational costs have signed numerator/denominator binary encodings. A forbidden arc is represented separately from a finite cost. Legal sets contain no forbidden arc; an optimum minimizes the actual finite sum over all legal feedback arc sets, and infeasibility is a separate result.
--
--   Writing $N=\max(1,n)$, uniform randomized and deterministic guarantees require
--
--   $$T_R\le C_R(2+\sqrt5)^kN^{d_R},\quad T_D\le C_D(803/100)^kN^{d_D},\quad S_A\le S_A^0\ell^{e_A},$$
--
--   on every input, with constants and programs quantified outside the instance. The randomized program halts on every bit prefix, always returns a valid size-$k$ DFVS or Fail, and has success at least $1/2$ on every yes-instance. The deterministic program succeeds exactly on yes-instances. Protected optimization returns a minimum or reports infeasibility; real and rational weighted optimization retain the entire weighted problem. Only predicates are defined here: existence of all these programs and bounds is left to theorem items.
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), pp. 4–13 (PDF pp. 4–13), §2, Lemma 3.6, Theorems 3.5, 4.2, 5.2 and 1.1 (interface readings)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVS_SingleExp_Machine

namespace PlanarDFVS.SingleExp

noncomputable def mask {r : ℕ} (X : Finset (Fin r)) : ℕ := ∑ i ∈ X, 2^i.val

def decodeMask (r x : ℕ) : Finset (Fin r) := Finset.univ.filter fun i => x.testBit i.val

noncomputable def supportCode {n m : ℕ} (G : Graph n m) : ℕ :=
  ∑ u : Fin n, ∑ v : Fin n, if support G u v then 2^(u.val * n + v.val) else 0

noncomputable def supportList {n m : ℕ} (G : Graph n m) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => if support G u v then 1 else 0

noncomputable def dfvsInput {n m : ℕ} (G : Graph n m) (k : ℕ) : Configuration :=
  { memory := [n, k] ++ supportList G }

def inputBits (s : Configuration) : ℕ :=
  1 + (s.memory.map (fun x => 1 + Nat.size x)).sum + s.realMemory.length

/-- All parallel classes have one representative. This is a representation map,
    not an operation granted to the solver on an explicit duplicate arc list. -/
noncomputable def representativeArcs {n m : ℕ} (G : Graph n m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun e => ∀ e',
    G.tail e' = G.tail e → G.head e' = G.head e → e.val ≤ e'.val

/-- The compressed inherited rotation lists contain the two selected incidences of
    every retained arc. Order uses the drawing's initial rays, never face counts. -/
noncomputable def compressedRotation {n m : ℕ} {G : Graph n m} (E : Drawing G) : List ℕ := by
  classical
  let darts := Finset.univ.filter fun d : Dart m => d.1 ∈ representativeArcs G
  exact (List.finRange n).flatMap fun v =>
    let ds := ((darts.filter fun d => origin G d = v).toList).mergeSort
      (fun d e => decide ((E.ray d).arg ≤ (E.ray e).arg))
    ds.length :: ds.map (fun d => 2 * ((G.tail d.1).val * n + (G.head d.1).val) +
      if d.2 then 1 else 0)

noncomputable def protectedInput {n m : ℕ} {G : Graph n m}
    (E : Drawing G) (P : Finset (Fin n)) : Configuration :=
  { memory := [n, mask P] ++ supportList G ++ compressedRotation E }

def ValidVertexOutput {n m : ℕ} (G : Graph n m) (k : ℕ) (s : Configuration) : Prop :=
  s.result = some false ∨
    (s.result = some true ∧ s.reg 0 < 2^n ∧
      IsDFVS G (decodeMask n (s.reg 0)) ∧ (decodeMask n (s.reg 0)).card ≤ k)

/-- One uniform fair-bit program, common finite horizon on each input, actual
    charged work, and a maximum live-space bound on every random execution. -/
def RandomGuarantee (P : Program) (base C : ℝ) (d : ℕ) (S : ℝ) (e : ℕ) : Prop :=
  BinaryProgram P ∧
  ∀ (n m : ℕ) (G : Graph n m) (k : ℕ), Planar G → ∃ t : ℕ,
    (∀ ω : Fin t → Bool,
      BoundedRun P (bitStream ω) (dfvsInput G k) t
        (C * base^k * (max 1 n : ℕ)^d)
        (S * (inputBits (dfvsInput G k) : ℝ)^e) ∧
      ValidVertexOutput G k (runBinary P (bitStream ω) (dfvsInput G k) t)) ∧
    (Feasible G k → (1 / 2 : ℚ) ≤ successProbability P (dfvsInput G k) t)

def DeterministicGuarantee (P : Program) (base C : ℝ) (d : ℕ) (S : ℝ) (e : ℕ) : Prop :=
  BinaryProgram P ∧ Deterministic P ∧
  ∀ (n m : ℕ) (G : Graph n m) (k : ℕ), Planar G → ∃ t : ℕ,
    BoundedRun P (fun _ => false) (dfvsInput G k) t
      (C * base^k * (max 1 n : ℕ)^d)
      (S * (inputBits (dfvsInput G k) : ℝ)^e) ∧
    ValidVertexOutput G k (runBinary P (fun _ => false) (dfvsInput G k) t) ∧
    ((runBinary P (fun _ => false) (dfvsInput G k) t).result = some true ↔ Feasible G k)

/-- Infeasibility is distinct from a minimum of value zero. -/
def ProtectedOptimal {n m : ℕ} (G : Graph n m) (P : Finset (Fin n))
    (s : Configuration) : Prop :=
  let admissible := fun X : Finset (Fin n) => IsDFVS G X ∧ Disjoint X P
  (s.result = some false ∧ ¬ ∃ X, admissible X) ∨
    (s.result = some true ∧ s.reg 0 < 2^n ∧ admissible (decodeMask n (s.reg 0)) ∧
      ∀ X, admissible X → (decodeMask n (s.reg 0)).card ≤ X.card)

def ProtectedGuarantee (A : Program) (C : ℝ) (d : ℕ) : Prop :=
  BinaryProgram A ∧ Deterministic A ∧
  ∀ (n m : ℕ) (G : Graph n m) (E : Drawing G) (P : Finset (Fin n)),
    Loopless G → positive E ⊆ P → ∃ t,
      ((runBinary A (fun _ => false) (protectedInput E P) t).work : ℝ) ≤ C * (max 1 n : ℕ)^d ∧
      ProtectedOptimal G P (runBinary A (fun _ => false) (protectedInput E P) t)

noncomputable def graphList {n m : ℕ} (G : Graph n m) : List ℕ :=
  [n, m] ++ (List.finRange m).flatMap (fun e => [(G.tail e).val, (G.head e).val])

noncomputable def realWeightedInput {n m : ℕ} (G : Graph n m)
    (c : Fin m → Option ℝ) : Configuration :=
  { memory := graphList G ++ (List.finRange m).map (fun e => if (c e).isSome then 1 else 0)
    realMemory := (List.finRange m).map fun e => (c e).getD 0 }

/-- `none` is a forbidden arc; all finite values may have either sign. -/
def LegalFAS {n m : ℕ} {α : Type} (G : Graph n m) (c : Fin m → Option α)
    (A : Finset (Fin m)) : Prop := IsFAS G A ∧ ∀ e ∈ A, (c e).isSome

noncomputable def fasCost {m : ℕ} (c : Fin m → Option ℝ) (A : Finset (Fin m)) : ℝ :=
  ∑ e ∈ A, (c e).getD 0

def WeightedOptimal {n m : ℕ} (G : Graph n m) (c : Fin m → Option ℝ)
    (s : Configuration) : Prop :=
  (s.result = some false ∧ ¬ ∃ A, LegalFAS G c A) ∨
    (s.result = some true ∧ s.reg 0 < 2^m ∧ LegalFAS G c (decodeMask m (s.reg 0)) ∧
      ∀ A, LegalFAS G c A → fasCost c (decodeMask m (s.reg 0)) ≤ fasCost c A)

noncomputable def rationalWeightedInput {n m : ℕ} (G : Graph n m)
    (c : Fin m → Option ℚ) : Configuration :=
  { memory := graphList G ++ (List.finRange m).flatMap (fun e => match c e with
      | none => [0, 0, 0, 1]
      | some q => [1, if q.num < 0 then 1 else 0, q.num.natAbs, q.den]) }

def RealWeightedGuarantee (A : Program) (C : ℝ) (d : ℕ) : Prop :=
  Deterministic A ∧ ∀ (n m : ℕ) (G : Graph n m) (c : Fin m → Option ℝ),
    Planar G → ∃ t,
      ((run A (fun _ => false) (realWeightedInput G c) t).work : ℝ) ≤
        C * (inputBits (realWeightedInput G c) : ℝ)^d ∧
      WeightedOptimal G c (run A (fun _ => false) (realWeightedInput G c) t)

def RationalWeightedGuarantee (A : Program) (C : ℝ) (d : ℕ) : Prop :=
  BinaryProgram A ∧ Deterministic A ∧
  ∀ (n m : ℕ) (G : Graph n m) (c : Fin m → Option ℚ), Planar G → ∃ t,
      ((runBinary A (fun _ => false) (rationalWeightedInput G c) t).work : ℝ) ≤
        C * (inputBits (rationalWeightedInput G c) : ℝ)^d ∧
      WeightedOptimal G (fun e => (c e).map fun q => (q : ℝ))
        (runBinary A (fun _ => false) (rationalWeightedInput G c) t)

end PlanarDFVS.SingleExp


