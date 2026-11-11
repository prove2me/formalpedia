-- Prove2me | Definitions.Def_StochMatchQuery_Union_Round
-- name    : StochMatchQuery_Union_Round
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:08:48.340407+00:00
-- url     : https://prove2.me/theorems/89758c19-5b5e-4cf9-aedc-22afc3e3f020
-- title:
--   The exact cutting, conditional-table, and selection round
-- statement:
--   Compare a current matching $M$ and a conditionally independent reference matching $B$. Cut alternating paths by a uniform residue of their ordered green edges; cut long cycles by a uniform start and the offsets $0,L,2L,\ldots$, leaving short cycles intact. This defines $B'$. Candidates are all nonempty simple paths and cycles with at most $\ell$ edges, one per edge set. Local signatures determine feasibility and the signed exchange $\Delta_e(c)$. Define
--   $$\lambda_c=\Pr(c\text{ is a component of }M\triangle B'\mid\sigma_c),\quad\phi_c=\frac{\lambda_c}{2(d+1)},\quad P_c=\prod_{z\text{ conflicts with }c}(1-\phi_z).$$
--   A candidate is proposed when its uniform is below $\phi_c$, isolated when no conflicting candidate is proposed, and kept when a second independent uniform is below $1/(2P_c)$. The next matching toggles every kept edge set. The runtime map uses only the current graph, matching and fresh seeds; the reference and cuts enter its fixed tables through their law.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), §§3.1–3.2, pp.12–20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_LocalComputation

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Undirected walk representation, allowing a repeated initial vertex only for a cycle. -/
def Traverses (c : Realization G) (n : ℕ) (v : Fin (n+1) → V) : Prop :=
  (∀ i : Fin n, ∃ e ∈ c, (e : Sym2 V) = s(v i.castSucc, v i.succ)) ∧
  c = Finset.univ.biUnion (fun i : Fin n =>
    c.filter (fun e : Edge G => (e : Sym2 V) = s(v i.castSucc, v i.succ)))

def IsPiece (c : Realization G) : Prop :=
  ∃ n, 0 < n ∧ ∃ v : Fin (n+1) → V, Traverses G c n v ∧
    (Function.Injective v ∨ (3 ≤ n ∧ v 0 = v (Fin.last n) ∧
      Function.Injective (fun i : Fin n => v i.castSucc)))

def candidates (ell : ℕ) : Finset (Realization G) :=
  Finset.univ.filter (fun c => IsPiece G c ∧ c.card ≤ ell)

def component (S c : Realization G) : Prop :=
  c.Nonempty ∧ c ⊆ S ∧
  (∀ u ∈ vertices G c, ∀ v ∈ vertices G c, ∃ R, Reached G c u v R) ∧
  ∀ e ∈ S, (∃ v ∈ vertices G c, v ∈ (e : Sym2 V)) → e ∈ c

def components (S : Realization G) : Finset (Realization G) :=
  Finset.univ.filter (component G S)

def toggle (M c : Realization G) : Realization G := symmDiff M c

def feasible (F M c : Realization G) : Prop := c ⊆ F ∧ IsMatching G (toggle G M c)

def delta (F M c : Realization G) (e : Edge G) : ℝ :=
  if feasible G F M c then ind (e ∈ toggle G M c) - ind (e ∈ M) else 0

def signature (F M c : Realization G) : V → Realization G × Realization G :=
  fun v => if v ∈ vertices G c then (incident G F v, incident G M v) else (∅, ∅)

/-- A deterministic orientation and numbering, using choice only for a combinatorial
representation, never to assume any probabilistic or locality conclusion. -/
def traverse (c : Realization G) : List (Edge G) :=
  if hc : ∃ v : Fin (c.card+1) → V, Traverses G c c.card v ∧
      (Function.Injective v ∨ (v 0 = v (Fin.last c.card) ∧
        Function.Injective (fun i : Fin c.card => v i.castSucc))) then
    let v := Classical.choose hc
    (List.finRange c.card).filterMap (fun i =>
      (c.toList.find? (fun e => decide ((e : Sym2 V) = s(v i.castSucc, v i.succ)))))
  else []

def isCycle (c : Realization G) : Prop :=
  c.Nonempty ∧ ∀ v ∈ vertices G c, degree G c v = 2

/-- Green edges in their canonical path/cycle order. -/
def greenList (M B c : Realization G) : List (Edge G) :=
  (traverse G c).filter (fun e => decide (e ∈ B \ M))

/-- A cut coordinate is a continuous uniform. On paths it chooses one residue;
on cycles it chooses one starting green edge. Endpoints of the unit interval are
assigned by modulo, affecting no probability. -/
def deletedIn (L : ℕ) (M B c : Realization G) (u : ℝ) : Realization G :=
  let gs := greenList G M B c
  let m := gs.length
  let j := ⌊u * (if isCycle G c then m else L)⌋₊ % (if isCycle G c then m else L)
  ((List.range m).filter (fun i => decide (
    if isCycle G c then L ≤ m ∧ ∃ k, k*L < m ∧ i = (j+k*L)%m
    else (i+1)%L = j))).filterMap (fun i => gs[i]?) |>.toFinset

/-- Avoid an arbitrary edge default: intersecting with c discards malformed representations.
On actual alternating components every index is in range. -/
def cutMatching (L : ℕ) (M B : Realization G) (u : Realization G → ℝ) : Realization G :=
  B \ ((components G (toggle G M B)).biUnion (fun c => deletedIn G L M B c (u c) ∩ c))

def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)
def cutLaw : Measure (Realization G → ℝ) := Measure.pi (fun _ => uniform01)

def conflicts (c z : Realization G) : Prop := c ≠ z ∧ ¬Disjoint (vertices G c) (vertices G z)

variable {Ω : Type*} [MeasurableSpace Ω]

def lambda (μ : Measure Ω) (F M B' : Ω → Realization G) (c : Realization G) (ω : Ω) : ℝ :=
  fiberMean μ (fun η => signature G (F η) (M η) c)
    (fun η => ind (component G (toggle G (M η) (B' η)) c)) ω

def proposalRate (d : ℕ) (lam : Realization G → ℝ) (c : Realization G) : ℝ :=
  lam c / (2*((d : ℝ)+1))
def isolationProbability (ell d : ℕ) (lam : Realization G → ℝ) (c : Realization G) : ℝ :=
  ∏ z ∈ (candidates G ell).filter (conflicts G c), (1 - proposalRate G d lam z)
def selected (ell d : ℕ) (lam U U' : Realization G → ℝ) : Finset (Realization G) :=
  (candidates G ell).filter (fun c =>
    U c < proposalRate G d lam c ∧
    (∀ z ∈ candidates G ell, conflicts G c z → ¬ U z < proposalRate G d lam z) ∧
    U' c < 1/(2*isolationProbability G ell d lam c))
def update (M : Realization G) (S : Finset (Realization G)) : Realization G :=
  toggle G M (S.biUnion id)

/-- One round's input law. The reference is drawn conditionally on F, independently of M.
Uniform cuts and proposal seeds are generated in the explicit product laws below. -/
structure RoundInput where
  law : Measure (Realization G × Realization G × Realization G)
  probability : IsProbabilityMeasure law
  valid : ∀ z : Realization G × Realization G × Realization G, 0 < prob law (fun a => a = z) → z.2.1 ⊆ z.1 ∧ z.2.2 ⊆ z.1 ∧ IsMatching G z.2.1 ∧ IsMatching G z.2.2
  /-- Exact finite conditional independence, including zero-probability fibers. -/
  conditional : ∀ F M B,
    prob law (fun z => z = (F,M,B)) * prob law (fun z => z.1 = F) =
      prob law (fun z => z.1 = F ∧ z.2.1 = M) * prob law (fun z => z.1 = F ∧ z.2.2 = B)

attribute [instance] RoundInput.probability
/-- z=(F,M,B), cuts. -/
abbrev RoundBase := (Realization G × Realization G × Realization G) × (Realization G → ℝ)
def RoundInput.baseLaw (q : RoundInput G) : Measure (RoundBase G) := q.law.prod (cutLaw G)
def roundF (z : RoundBase G) := z.1.1
def roundM (z : RoundBase G) := z.1.2.1
def roundB (z : RoundBase G) := z.1.2.2
def roundB' (h : ℝ) (z : RoundBase G) := cutMatching G (cutPeriod h) (roundM G z) (roundB G z) z.2

def RoundInput.table (q : RoundInput G) (h : ℝ) (z : RoundBase G) (c : Realization G) : ℝ :=
  lambda G q.baseLaw (roundF G) (roundM G) (roundB' G h) c z

abbrev RoundOutcome := RoundBase G × ((Realization G → ℝ) × (Realization G → ℝ))
def RoundInput.fullLaw (q : RoundInput G) : Measure (RoundOutcome G) :=
  q.baseLaw.prod ((cutLaw G).prod (cutLaw G))
def RoundInput.kept (q : RoundInput G) (D : ℕ) (h : ℝ) (z : RoundOutcome G) :=
  selected G (pieceLength h) (conflictBound D h) (RoundInput.table G q h z.1) z.2.1 z.2.2
def RoundInput.next (q : RoundInput G) (D : ℕ) (h : ℝ) (z : RoundOutcome G) :=
  update G (roundM G z.1) (RoundInput.kept G q D h z)
/-- The runtime round reads F, the previous matching, and fresh uniforms only.
The B and cut coordinates below are dummy evaluation coordinates of a fixed table. -/
def roundStep (q : RoundInput G) (D : ℕ) (h : ℝ) (F M : Realization G)
    (U U' : Realization G → ℝ) : Realization G :=
  update G M (selected G (pieceLength h) (conflictBound D h)
    (RoundInput.table G q h ((F,M,∅), fun _ => 0)) U U')

def anchor (c : Realization G) : Option V :=
  let ids := (vertices G c).image (Fintype.equivFin V)
  if hc : ids.Nonempty then some ((Fintype.equivFin V).symm (ids.min' hc)) else none

def storedCoin {α : V → Type} (ξ : (v : V) → α v ×
    ((Realization G → ℝ) × (Realization G → ℝ))) (second : Bool) (c : Realization G) : ℝ :=
  match anchor G c with
  | none => 0
  | some v => max 0 (min 1 (if second then (ξ v).2.2 c else (ξ v).2.1 c))
end
end StochMatchQuery.Union


