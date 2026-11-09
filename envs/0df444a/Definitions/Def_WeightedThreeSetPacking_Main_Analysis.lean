-- Prove2me | Definitions.Def_WeightedThreeSetPacking_Main_Analysis
-- name    : WeightedThreeSetPacking_Main_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:25.540904+00:00
-- url     : https://prove2.me/theorems/3782c2f3-a5d9-4b71-9f02-5495b0ba38c0
-- title:
--   Charging quantities, witnessed exchange layers and real optimization
-- statement:
--   For finite weighted conflict graphs and independent families $A,O$, define inclusive neighborhoods, maximum-neighbor center assignments, claws $C_v$, the square and separation slacks $\Delta_v,\Psi_v$, positive claw gains $g_v$, and $G(A,O)=\sum_{v\in A}g_v$. Common vertices remain allowed.
--
--   The layer partition is computed by connectivity of witnessed multiarcs $(o,b,v)$, retaining multiplicities in edge sums. Its generic thresholds are ordered as in §3.2; the Section 4 specialization uses exact $a=5433/10000$, $c=773/1250$, and radicals. Final components are actual connected components of the remaining class, not arbitrary subsets. Only final pieces are represented here; this definition does not purport to define the full root/pendant contraction hierarchy.
--
--   For normalized singleton data, distinct blockers and incidence counts are separate. The value $\beta_{\min}(S)$ is the infimum of the genuine continuous feasible objective over $2m$ padded real coordinates. The associated theorem supplies attainment on the stated domain. No source inequality is assumed as a structure field.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, §§3–4, pp. 6–10, 14–20; Lemmas 3.1–3.2, pp. 7, 9; Lemmas 4.5–4.7, pp. 16–20; https://arxiv.org/abs/2610.10036v1

import Mathlib

namespace WeightedThreeSetPacking.Main
noncomputable section
open scoped BigOperators
open Classical

def a : ℝ := 5433 / 10000

def c : ℝ := 773 / 1250

def delta : ℝ := 1 - a

def q : ℝ := a ^ 2

def layerExchangeRadius (ell : ℕ) : ℕ :=
  (9 * ell)^3 * ∑ r ∈ Finset.range (2 * ell - 1), (3 * ell)^(2*r)

def s₀ : ℕ := layerExchangeRadius 7

def kappa : ℕ → ℝ
  | 0 => Real.sqrt (Real.sqrt a)
  | 1 => Real.sqrt a
  | 2 => a
  | _ => a ^ 2

def epsilon (i : ℕ) : ℝ := 1 - kappa i

def rho (e : ℝ) : ℝ := 3 * e - e / (1 - e)

/-- Finite weighted conflict graph. Common vertices of A and O remain single
vertices, not disjoint tagged copies. The lift need not be a set system. -/
structure Analysis (V : Type) [Fintype V] [DecidableEq V] where
  graph : SimpleGraph V
  w : V → ℝ
  A : Finset V
  O : Finset V
  center : V → V
  threshold : ℕ → ℝ := kappa
  cutoff : ℕ := 7

variable {V : Type} [Fintype V] [DecidableEq V]

def mass (D : Analysis V) (X : Finset V) : ℝ := ∑ v ∈ X, D.w v

def squareMass (D : Analysis V) (X : Finset V) : ℝ := ∑ v ∈ X, D.w v ^ 2

def independent (D : Analysis V) (X : Finset V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬ D.graph.Adj u v

/-- Inclusive neighborhood, including the intersection of the two families. -/
def neighbors (D : Analysis V) (X Y : Finset V) : Finset V :=
  Y.filter fun y => y ∈ X ∨ ∃ x ∈ X, D.graph.Adj x y

def claw (D : Analysis V) (v : V) : Finset V := D.O.filter fun o => D.center o = v

def clawNeighborhood (D : Analysis V) (v : V) : Finset V :=
  {v} ∪ (claw D v).biUnion (fun o => neighbors D {o} (D.A \ {v}))

def exchangeSlack (D : Analysis V) (v : V) : ℝ :=
  squareMass D (clawNeighborhood D v) - squareMass D (claw D v)

def separationSlack (D : Analysis V) (v : V) : ℝ :=
  ∑ o ∈ claw D v, ((D.w o - D.w v)^2 +
    D.w v * mass D (neighbors D {o} (D.A \ {v})) -
    squareMass D (neighbors D {o} (D.A \ {v})))

def residual (D : Analysis V) (v : V) : ℝ :=
  max (mass D (claw D v) - mass D (neighbors D (claw D v) D.A)) 0

def residualTotal (D : Analysis V) : ℝ := ∑ v ∈ D.A, residual D v

def jointClaw (D : Analysis V) (R : Finset V) : Finset V := R.biUnion (claw D)

def jointNeighborhood (D : Analysis V) (R : Finset V) : Finset V :=
  R.biUnion (clawNeighborhood D)

/-- Exactly the graph-side standing assumptions inherited from two rank-three
packings and maximum-weight center assignment; no slack or approximation fact. -/
def ValidAnalysis (D : Analysis V) : Prop :=
  (∀ v ∈ D.A ∪ D.O, 0 < D.w v) ∧ independent D D.A ∧ independent D D.O ∧
  (∀ o ∈ D.O, (neighbors D {o} D.A).card ≤ 3) ∧
  (∀ v ∈ D.A, (neighbors D {v} D.O).card ≤ 3) ∧
  (∀ o ∈ D.O, D.center o ∈ neighbors D {o} D.A ∧
    ∀ v ∈ neighbors D {o} D.A, D.w v ≤ D.w (D.center o))

def SquareLocal (D : Analysis V) (s : ℕ) : Prop :=
  ∀ X ⊆ Finset.univ \ D.A, independent D X → X.card ≤ 3 * s →
    squareMass D X ≤ squareMass D (neighbors D X D.A)

/-- Witnessed multiarcs (talon, secondary blocker, assigned center). -/
def arcs (D : Analysis V) : Finset (V × V × V) :=
  Finset.univ.filter fun e => e.2.2 ∈ D.A ∧ e.1 ∈ claw D e.2.2 ∧
    e.2.1 ∈ neighbors D {e.1} (D.A \ {e.2.2})

def arcLayer (D : Analysis V) (e : V × V × V) : ℕ :=
  if D.threshold 1 < D.w e.2.1 / D.w e.2.2 then 1 else
  if D.threshold 2 < D.w e.2.1 / D.w e.2.2 then 2 else
  if D.threshold 3 < D.w e.2.1 / D.w e.2.2 then 3 else 4

def internalArcs (D : Analysis V) (T : Finset V) (i : ℕ) : Finset (V × V × V) :=
  (arcs D).filter fun e => e.2.1 ∈ T ∧ e.2.2 ∈ T ∧ arcLayer D e ≤ i

/-- Orientation is suppressed only for reachability. Multiarcs remain in sums. -/
def linked (D : Analysis V) (i : ℕ) (I : Finset V) (u v : V) : Prop :=
  u ∈ I ∧ v ∈ I ∧ ∃ e ∈ arcs D, arcLayer D e ≤ i ∧
    ((e.2.1 = u ∧ e.2.2 = v) ∨ (e.2.1 = v ∧ e.2.2 = u))

def component (D : Analysis V) (i : ℕ) (I : Finset V) (v : V) : Finset V :=
  I.filter fun u => Relation.ReflTransGen (linked D i I) v u

/-- Remaining vertices, using both the induced and full components on each layer. -/
def remaining (D : Analysis V) : ℕ → Finset V
  | 0 => D.A
  | i + 1 =>
    let I := remaining D i
    I.filter fun v => (component D (i+1) I v).card < D.cutoff ∧
      (i = 0 ∨ component D (i+1) I v = component D (i+1) D.A v)

def layerClass (D : Analysis V) : ℕ → Finset V
  | 1 => D.A \ remaining D 1
  | 2 => remaining D 1 \ remaining D 2
  | 3 => remaining D 2 \ remaining D 3
  | 4 => remaining D 3
  | _ => ∅

def FinalComponent (D : Analysis V) (T : Finset V) : Prop :=
  ∃ v ∈ remaining D 3, T = component D 3 (remaining D 3) v

def layerCredit (D : Analysis V) (T : Finset V) : ℝ :=
  ∑ v ∈ T, ∑ o ∈ claw D v, ∑ i ∈ Finset.range 3,
    (1 - D.threshold i) * mass D (neighbors D {o} (layerClass D (i+2)))

def slackSum (D : Analysis V) (T : Finset V) : ℝ :=
  ∑ v ∈ T, (exchangeSlack D v / D.w v + separationSlack D v / D.w v)

def ConnectedSubtree (D : Analysis V) (T R : Finset V) : Prop :=
  R.Nonempty ∧ R ⊆ T ∧ ∀ u ∈ R, ∀ v ∈ R,
    Relation.ReflTransGen (linked D 4 R) u v

/-- The final pieces have at most six vertices, so girth > 12 suffices to
exclude all their conflict cycles and witnessed parallel-arc obstructions. -/
def FinalHighGirth (D : Analysis V) : Prop :=
  (2 * (D.cutoff - 1) : ℕ) < D.graph.egirth

def FixedParameters (D : Analysis V) : Prop :=
  D.cutoff = 7 ∧ ∀ i ≤ 3, D.threshold i = kappa i

/-- The imported framework requires the recurrence (Appendix A.3, pp. 30–31),
not just the ordered thresholds in the notation recap on p. 8. -/
def LayerParameters (D : Analysis V) : Prop :=
  2 ≤ D.cutoff ∧ (∀ i ≤ 3, 0 < D.threshold i ∧ D.threshold i < 1) ∧
  (∀ i < 3, D.threshold (i+1) = D.threshold i ^ 2)

def blockers (D : Analysis V) (v : V) : Finset V := neighbors D (claw D v) D.A \ {v}

def normalizedTalonMass (D : Analysis V) (v : V) : ℝ :=
  ∑ o ∈ claw D v, D.w o / D.w v

def normalizedBlocker (D : Analysis V) (v u : V) : ℝ := D.w u / D.w v

def incidence (D : Analysis V) (v u : V) : ℕ :=
  ((claw D v).filter fun o => D.graph.Adj o u).card

def blockerMass (D : Analysis V) (v : V) : ℝ :=
  ∑ u ∈ blockers D v, normalizedBlocker D v u

def requiredSquareMass (m : ℕ) (x : ℝ) : ℝ := max (x^2 / m - 1) 0

/-- Genuine continuous optimization; padded real coordinates, not a formula. -/
def cappedFeasible (m : ℕ) (S : ℝ) (z : Fin (2*m) → ℝ) : Prop :=
  (∀ i, 0 ≤ z i ∧ z i ≤ q) ∧ S ≤ ∑ i, z i ^ 2

def betaMinimum (m : ℕ) (S : ℝ) : ℝ :=
  sInf {b | ∃ z : Fin (2*m) → ℝ, cappedFeasible m S z ∧ b = ∑ i, z i}

end
end WeightedThreeSetPacking.Main


