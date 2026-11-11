-- Prove2me | Definitions.Def_MultiwayGap2325_Main_RandomCuts
-- name    : MultiwayGap2325_Main_RandomCuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:54.310826+00:00
-- url     : https://prove2.me/theorems/c5af92af-40a8-4ac0-9aff-673e7a17e732
-- title:
--   Jointly measurable random non-opposite cuts of the full real simplex
-- statement:
--   Let $\Delta_q=\{x\in\mathbb R_{\ge0}^q:\sum_i x_i=1\}$. A non-opposite cut labels $\Delta_q$ by the $q$ terminal labels and an extra label $\ast$, fixes every vertex $e_i$, and assigns terminal label $i$ only where $x_i>0$. On a measurable sample space $(\Xi,\mathcal F)$ with measure $P$, a random cut is a jointly measurable map $C:\Xi\times\Delta_q\to[q]\cup\{\ast\}$ whose every realization is non-opposite. Uses as a random probability law additionally require $P(\Xi)=1$.
--
--   An approximation factor is a real number $\alpha$ satisfying, at every pair of real simplex points,
--   $$
--   P\{\xi:C(\xi,x)\ne C(\xi,y)\}\le\alpha\,\tfrac12\sum_i|x_i-y_i|.
--   $$
--   This provides the full continuous model for the non-opposite reduction, including the joint measurability convention needed in the analytic arguments.
--
--   **Formalization Note** The simplex has its induced Borel structure and the finite label space has the discrete sigma algebra. The extra label is the separate option constructor, not an additional terminal. Measures are extended nonnegative real valued. For $q\ge2$ on a probability space, the displayed inequality at distinct vertices forces $\alpha\ge1$, so its conversion with $\operatorname{ofReal}$ is exact. No finite support, continuity of realizations, or rational coordinate restriction is imposed.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Definition 2.1 and equation (3), p. 3; §5 standing preamble, p. 11; Appendix A, p. 34

import Definitions.Def_MultiwayGap2325_Main_FiniteGap

noncomputable section

namespace MultiwayGap2325.Main

/-- The full real simplex, with its induced topology and Borel measurable structure. -/
abbrev Simplex (q : ℕ) := {x : Fin q → ℝ // x ∈ stdSimplex ℝ (Fin q)}

/-- `none` is the extra label ∗, and is not a terminal. -/
abbrev CutLabel (q : ℕ) := Option (Fin q)

instance cutLabelMeasurableSpace (q : ℕ) : MeasurableSpace (CutLabel q) := ⊤

/-- The simplex vertex at a terminal. -/
def simplexVertex {q : ℕ} (i : Fin q) : Simplex q :=
  ⟨Pi.single i 1, by
    constructor
    · intro j
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    · simp⟩

/-- The paper's metric, not the norm metric on the function space. -/
def simplexDistance {q : ℕ} (x y : Simplex q) : ℝ :=
  MultiwayCut.halfL1 x.val y.val

/-- Definition 2.1: every point is labeled in its positive support or by ∗. -/
def IsNonOpposite {q : ℕ} (C : Simplex q → CutLabel q) : Prop :=
  (∀ i : Fin q, C (simplexVertex i) = some i) ∧
  (∀ x : Simplex q, ∀ i : Fin q, C x = some i → 0 < x.val i)

/-- Definition 2.1 with the standing joint measurability assumption of §5, p.11.
No restriction on the probability space, support of its law, or realized cut geometry. -/
structure RandomNonOppositeCut (q : ℕ) (Ξ : Type*) [MeasurableSpace Ξ]
    (P : MeasureTheory.Measure Ξ) where
  labeling : Ξ × Simplex q → CutLabel q
  jointlyMeasurable : Measurable labeling
  nonOpposite : ∀ ξ : Ξ, IsNonOpposite (fun x => labeling (ξ, x))

/-- Equation (3), required at every pair of real simplex points. -/
def HasApproximationFactor {q : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {P : MeasureTheory.Measure Ξ} (C : RandomNonOppositeCut q Ξ P) (α : ℝ) : Prop :=
  ∀ x y : Simplex q,
    P {ξ | C.labeling (ξ, x) ≠ C.labeling (ξ, y)} ≤
      ENNReal.ofReal (α * simplexDistance x y)

end MultiwayGap2325.Main


