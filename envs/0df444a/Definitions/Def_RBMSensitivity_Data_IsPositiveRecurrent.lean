-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsPositiveRecurrent
-- name    : RBMSensitivity_Data_IsPositiveRecurrent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:08.745589+00:00
-- url     : https://prove2.me/theorems/7714e65d-68f0-4c40-9311-440f1a579824
-- title:
--   Positive recurrence of the RBM
-- statement:
--   The RBM $Z^\alpha$ is **positive recurrent** if for every starting point $x\in G$ and every closed set $A\subseteq G$ of positive Lebesgue measure, the hitting time $\tau_A$ of $A$ by $Z^{\alpha,x}$ has finite expectation.
--
--   It is the recurrence property that drives the repeated visits to every face in §6.
--
--   **Formalization Note** The paper does not define the term; this is the sense of Dupuis and Williams, its cited source for Theorem 3.5.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.5, p.10

import Mathlib
import Definitions.Def_RBMSensitivity_hittingTime
import Definitions.Def_RBMSensitivity_SimpleCone_G
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `Z^α` is positive recurrent, as in Theorem 3.5: arXiv:1907.00472v2, p.10.

**Formalization Note.** The paper does not define the term. This is the Dupuis–Williams sense, the
paper's cited source [14]: `E[τ_A] < ∞` for every start `x ∈ G` and every closed `A ⊆ G` of positive
Lebesgue measure. -/
def Data.IsPositiveRecurrent {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (D : Data J)
    (P : Measure Ω) (Z : ℝ → E J → ℝ≥0 → Ω → E J) (α : ℝ) : Prop :=
  ∀ x ∈ D.G, ∀ A : Set (E J), IsClosed A → A ⊆ D.G → 0 < volume A →
    ∫⁻ ω, hittingTime (Z α x) A ω ∂P < ⊤

end RBMSensitivity


