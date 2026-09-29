-- Prove2me | Definitions.Def_LogRegretOCO_EWOO_ewooPoint
-- name    : LogRegretOCO_EWOO_ewooPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:42:43.268234+00:00
-- url     : https://prove2.me/theorems/7b0b10ff-940f-4c4a-b637-6394b000b2d2
-- title:
--   The Exponentially Weighted Online Optimization point x_t (Fig. 4)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$, let $\alpha \in \mathbb{R}$, and let $f_1, f_2, \dots : \mathbb{R}^n \to \mathbb{R}$ be the cost functions of an online convex optimization game, with rounds numbered $t = 1, 2, \dots$. **Exponentially Weighted Online Optimization** (EWOO) defines the weights
--
--   $$
--   w_t(x) = \exp\Bigl(-\alpha \sum_{\tau=1}^{t-1} f_\tau(x)\Bigr),
--   $$
--
--   so that $w_1 \equiv 1$, and on round $t$ it plays the $w_t$-weighted mean of $P$ under Lebesgue measure:
--
--   $$
--   x_t = \frac{\int_P x\, w_t(x)\, dx}{\int_P w_t(x)\, dx}.
--   $$
--
--   In particular $x_1$ is the centroid of $P$. The point $x_t$ depends only on $f_1, \dots, f_{t-1}$, so the algorithm is deterministic and well defined against adaptive adversaries.
--
--   This is the algorithm whose regret Theorem 7 bounds; it is the online-convex-optimization analogue of Cover's universal portfolio algorithm.
--
--   **Formalization Note** The definition is a total function of $(P, \alpha, f, t)$. It is the paper's point when $P$ has positive finite volume and $w_t$ and $x \mapsto x\,w_t(x)$ are integrable on $P$; the theorems that use it assume $P$ closed, bounded, convex, of positive volume, and each $f_t$ continuous on $P$, which guarantees this. The integral is the Bochner integral in `EuclideanSpace ℝ (Fin n)` with respect to its Lebesgue (Haar) measure `volume`. The paper's randomized variant (sampling $x_t$ with density proportional to $w_t$) is not formalized.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 186, Fig. 4 (EXPONENTIALLY WEIGHTED ONLINE OPTIMIZATION: "Define weights w_t(x) = exp(−α Σ_{τ=1}^{t−1} f_τ(x)). On period t play x_t = ∫_P x w_t(x)dx / ∫_P w_t(x)dx.")

import Mathlib

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- The EWOO weight of Fig. 4 (Hazan–Agarwal–Kale 2007, p. 186):
`w_t(x) = exp(-α ∑_{τ=1}^{t-1} f_τ(x))`. Rounds are 1-based; `w_1 ≡ 1`. -/
noncomputable def ewooWeight {n : ℕ} (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (t : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-α * ∑ τ ∈ Finset.Ico 1 t, f τ x)

/-- The point played by EXPONENTIALLY WEIGHTED ONLINE OPTIMIZATION in round `t` (Fig. 4,
p. 186): the `w_t`-weighted mean of `P` under Lebesgue measure,
`x_t = (∫_P x w_t(x) dx) / (∫_P w_t(x) dx)`. -/
noncomputable def ewooPoint {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (∫ x in P, ewooWeight α f t x)⁻¹ • ∫ x in P, ewooWeight α f t x • x

end LogRegretOCO.EWOO


