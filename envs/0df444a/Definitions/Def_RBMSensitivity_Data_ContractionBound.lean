-- Prove2me | Definitions.Def_RBMSensitivity_Data_ContractionBound
-- name    : RBMSensitivity_Data_ContractionBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:58.877724+00:00
-- url     : https://prove2.me/theorems/95ab6b37-e09c-40e0-a6e7-9320c87ae739
-- title:
--   The contraction bound (4.12) on $U_0$
-- statement:
--   A constant $\delta_0$ satisfies the **contraction bound** on $U_0$ if whenever $\alpha\in U_0$, $K\in\mathbb N$ and $\{x_k\}_{k=1,\dots,K}$ is a finite sequence in $\partial G$ with $\mathcal I=\bigcup_{k=1,\dots,K}\mathcal I(x_k)$, then for all $y\in\mathbb R^J$,
--   $$\|\mathcal L^\alpha_{x_K}\cdots\mathcal L^\alpha_{x_1}y\|_{B^\alpha}\le\delta_0\|y\|_{B^\alpha}.$$
--   Here $\|y\|_{B^\alpha}:=\min\{r\ge 0:y\in rB^\alpha\}$.
--
--   Lemma 4.20 provides such a $\delta_0<1$. Its later statements are phrased for any such constant.
--
--   **Formalization Note** $\|\cdot\|_{B^\alpha}$ is the Minkowski gauge of $B^\alpha$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Lemma 4.20, (4.12), p.15

import Mathlib
import Definitions.Def_RBMSensitivity_Data_IsDerivProj
import Definitions.Def_RBMSensitivity_composeProj
import Definitions.Def_RBMSensitivity_SimpleCone_G
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `δ₀` satisfies the bound (4.12) on `U₀`: arXiv:1907.00472v2, Lemma 4.20, p.15. If `α ∈ U₀`, `K ∈ ℕ`
and `{x_k}` is a finite sequence in `∂G` with `I = ⋃_k I(x_k)`, then for all `y`,
`‖L^α_{x_K} ⋯ L^α_{x_1} y‖_{B^α} ≤ δ₀ ‖y‖_{B^α}`.

**Formalization Note.** `‖·‖_{B^α}` of (4.10) is `gauge (B α)`, since `B^α` is compact, convex and
symmetric with `0` in its interior. -/
def Data.ContractionBound {J : ℕ} (D : Data J) (B : ℝ → Set (E J)) (U₀ : Set ℝ) (δ₀ : ℝ) : Prop :=
  ∀ α ∈ U₀, ∀ (K : ℕ) (x : Fin K → E J), (∀ k, x k ∈ frontier D.G) →
    (⋃ k, D.I (x k)) = Set.univ →
    ∀ L : Fin K → E J → E J, (∀ k, D.IsDerivProj α (x k) (L k)) →
      ∀ y, gauge (B α) (composeProj L y) ≤ δ₀ * gauge (B α) y

end RBMSensitivity


