-- Prove2me | Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_TreeModel
-- name    : RiskAverseSDDP_Subdiff_Supplement_TreeModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:31:19.031025+00:00
-- url     : https://prove2.me/theorems/591748a6-6fac-4faa-9be2-2762250d278b
-- title:
--   (6.43)–(6.46), (H2) — finite node-dependent convex models and independent scenario sampling
-- statement:
--   A finite scenario tree has a unique first-stage node, levels $V_s$ corresponding to stages $s+1$, and parent maps $V_{s+1}\to V_s$. The fictitious root carries the fixed decision $x_0$. Each node has its realization-dependent convex cost, nonlinear constraints, equality matrices and right-hand side; the compact decision sets depend on the stage. A node's children have positive conditional transition probabilities and a nonempty convex risk-density set, with nonnegative densities normalized against those probabilities. Thus its coherent risk measure is the supremum of weighted child values, as in (6.43).
--
--   `TreeModel.feas` gives the constraints at a node; `H2` copies all of (H2), including one positive epsilon, full Euclidean history fattenings and the relative-interior qualification. `Q` implements (6.43)–(6.44), with zero leaf values, and `Q1` gives the separate deterministic first-stage optimum. `IsFirstStageOptimal` includes feasibility and attainment. The type of a sampled path contains exactly the $T$ actual stage nodes. `Sampling` requires measurable independent path-valued samples, parent consistency, the unique first-stage node, and the conditional tree law. Independence is across whole scenarios and does not impose independence within any scenario.
--
--   **Formalization Note** The independent-scenario condition follows the opening prose of Theorem 6.1 and corrects its identically-one selected-leaf indicator test; it excludes repeated correlated scenarios with correct marginals. The source's parameter measurability is automatic on finite supports. The types $V_s$ are arbitrary finite sets, so branching may vary by node. Values are in `EReal`; costs and constraints respect the source codomain $\mathbb R\cup\{+\infty\}$. Node indices start at zero in Lean and stage indices in the mathematics start at one.
-- source:
--   Guigues, arXiv:1408.4439v4, pp. 18–20, (6.43)–(6.46), Theorem 6.1, with (H2), pp. 6–7

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_LinModel

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The finite node-dependent model (6.43)-(6.46), pp. 18-19. `V s` is the set of
nodes of stage `s+1`; the fictitious root is represented by `x0`. In particular `V 0`
is a singleton. Finite branching can vary by node. The cost and constraint data at a
node include its realization, so no interstage independence is imposed. -/
structure TreeModel (T n q p : ℕ) (V : ℕ → Type*) where
  first : V 0
  first_unique : ∀ ν : V 0, ν = first
  parent : (s : ℕ) → V (s + 1) → V s
  x0 : EuclideanSpace ℝ (Fin n)
  Xc : ℕ → Set (EuclideanSpace ℝ (Fin n))
  f : (s : ℕ) → V s → Hist n (s + 1) → EReal
  g : (s : ℕ) → V s → Hist n (s + 1) → Fin p → EReal
  A : (s : ℕ) → V s → Fin (s + 2) →
    (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))
  b : (s : ℕ) → V s → EuclideanSpace ℝ (Fin q)
  Φ : (s : ℕ) → (ν : V s) → {m : V (s + 1) // parent s m = ν} → ℝ
  Prisk : (s : ℕ) → (ν : V s) → Set ({m : V (s + 1) // parent s m = ν} → ℝ)

namespace TreeModel

variable {T n q p : ℕ} {V : ℕ → Type*} (D : TreeModel T n q p V)

abbrev Child (s : ℕ) (ν : V s) := {m : V (s + 1) // D.parent s m = ν}

/-- The source feasible set for the realization at a node of stage `s+1`. -/
def feas (s : ℕ) (ν : V s) (x : Hist n s) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | y ∈ D.Xc (s + 1) ∧ (∀ i, D.g s ν (x.snoc y) i ≤ 0) ∧
    ∑ τ : Fin (s + 2), D.A s ν τ
      (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) D.x0 (fun i => (x.snoc y) i) τ) = D.b s ν}

def prodSet (s : ℕ) : Set (Hist n s) := {x | ∀ i : Fin s, x i ∈ D.Xc (i.val + 1)}

/-- (H2), pp. 6-7, interpreted at every possible node realization, as §6 explicitly
requires. One common positive epsilon, Euclidean fattenings, and the full relative-interior
qualification are retained. The constraint functions never take -infinity (their source
codomain is R union {+infinity}). -/
def H2 (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ s, s < T →
    ((D.Xc (s + 1)).Nonempty ∧ Convex ℝ (D.Xc (s + 1)) ∧ IsCompact (D.Xc (s + 1))) ∧
    ∀ ν : V s,
      (EProper (D.f s ν) ∧ EConvex (D.f s ν) ∧ LowerSemicontinuous (D.f s ν)) ∧
      (∀ i, (∀ z, D.g s ν z i ≠ ⊥) ∧ EConvex (fun z => D.g s ν z i) ∧
        LowerSemicontinuous (fun z => D.g s ν z i)) ∧
      (∀ x ∈ Metric.cthickening ε (D.prodSet s), ∀ y ∈ D.Xc (s + 1), D.f s ν (x.snoc y) < ⊤) ∧
      (∀ x ∈ Metric.cthickening ε (D.prodSet s), (D.feas s ν x).Nonempty) ∧
      (1 ≤ s → ∃ xb : Hist n s, ∃ yb : EuclideanSpace ℝ (Fin n),
        xb ∈ D.prodSet s ∧ yb ∈ intrinsicInterior ℝ (D.Xc (s + 1)) ∧
        xb.snoc yb ∈ intrinsicInterior ℝ {z : Hist n (s + 1) | ∀ i, D.g s ν z i ≤ 0} ∧
        yb ∈ D.feas s ν xb)

variable [∀ s, Fintype (V s)]

noncomputable def wsum (s : ℕ) (ν : V s) (a : D.Child s ν → ℝ)
    (Z : D.Child s ν → EReal) : EReal := by
  classical
  exact ∑ m, ((a m * D.Φ s ν m : ℝ) : EReal) * Z m

noncomputable def rho (s : ℕ) (ν : V s) (Z : D.Child s ν → EReal) : EReal :=
  ⨆ a ∈ D.Prisk s ν, D.wsum s ν a Z

/-- Conditional probabilities and coherent node risk sets from (6.43), including the
implicit nonempty dual set. Children of nonleaf nodes are nonempty. -/
def Standing : Prop := by
  classical
  exact ∀ s, s + 1 < T → ∀ ν : V s,
    Nonempty (D.Child s ν) ∧ (∀ m, 0 < D.Φ s ν m) ∧ (∑ m, D.Φ s ν m) = 1 ∧
    (D.Prisk s ν).Nonempty ∧ Convex ℝ (D.Prisk s ν) ∧
    ∀ a ∈ D.Prisk s ν, (∀ m, 0 ≤ a m) ∧ ∑ m, a m * D.Φ s ν m = 1

noncomputable def stageVal (s : ℕ) (ν : V s) (W : Hist n (s + 1) → EReal)
    (x : Hist n s) : EReal :=
  ⨅ y ∈ D.feas s ν x, D.f s ν (x.snoc y) + W (x.snoc y)

/-- Node recursion (6.43)-(6.44); a node's value is the risk of the next-stage child
subproblems, whereas the fictitious root has a separate deterministic first-stage problem. -/
noncomputable def Qaux : ℕ → (s : ℕ) → V s → Hist n (s + 1) → EReal
  | 0, _, _, _ => 0
  | r + 1, s, ν, x => D.rho s ν (fun m => D.stageVal (s + 1) m.val (Qaux r (s + 1) m.val) x)

noncomputable def Q (s : ℕ) (ν : V s) : Hist n (s + 1) → EReal := D.Qaux (T - (s + 1)) s ν

noncomputable def Q1 : EReal := D.stageVal 0 D.first (D.Q 0 D.first) (Hist.empty n)

def IsFirstStageOptimal (y : EuclideanSpace ℝ (Fin n)) : Prop :=
  y ∈ D.feas 0 D.first (Hist.empty n) ∧
    D.f 0 D.first ((Hist.empty n).snoc y) + D.Q 0 D.first ((Hist.empty n).snoc y) = D.Q1

/-- A sampled path contains precisely the T actual stage nodes. -/
abbrev Path (_D : TreeModel T n q p V) := (s : Fin T) → V s.val

/-- The intended independent-scenario reading of Theorem 6.1, p. 20. Samples are
independent path-valued random variables, with the finite tree law fixed by the conditional
transition probabilities. This corrects the printed indicator of the already-selected leaf,
which is identically one. No independence within a scenario is imposed. -/
def Sampling {Ω : Type*} [MeasurableSpace Ω] [∀ s, MeasurableSpace (V s)]
    (hT : 1 ≤ T) (P : Measure Ω) (ξ : ℕ → Ω → D.Path) : Prop :=
  (∀ k, Measurable (ξ (k + 1))) ∧ iIndepFun (fun k : ℕ => ξ (k + 1)) P ∧
  (∀ k ω, ξ (k + 1) ω ⟨0, hT⟩ = D.first) ∧
  (∀ k ω s (hs : s + 1 < T),
    D.parent s (ξ (k + 1) ω ⟨s + 1, hs⟩) = ξ (k + 1) ω ⟨s, by omega⟩) ∧
  (∀ k s (hs : s + 1 < T) (m : V (s + 1)),
    P {ω | ξ (k + 1) ω ⟨s + 1, hs⟩ = m} =
      ENNReal.ofReal (D.Φ s (D.parent s m) ⟨m, rfl⟩) *
        P {ω | ξ (k + 1) ω ⟨s, by omega⟩ = D.parent s m})

end TreeModel

end RiskAverseSDDP.Subdiff.Supplement


