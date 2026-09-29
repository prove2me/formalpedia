-- Prove2me | Definitions.Def_BastaniBayati_LassoBandit_Constants
-- name    : BastaniBayati_LassoBandit_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:03:17.570921+00:00
-- url     : https://prove2.me/theorems/96ff06e0-eace-4d3d-93f9-f1125edb06cf
-- title:
--   Sparsity $s_0$ and the constants $C_1,\dots,C_5$, $q_0$, $\lambda_1$, $\lambda_{2,0}$
-- statement:
--   The explicit constants of Bastani and Bayati's regret analysis. The **sparsity parameter** $s_0\in[d]$ is the smallest integer $s_0\ge 1$ with $\|\beta_i\|_0\le s_0$ for all arms $i$. With $\sigma$, $x_{\max}$, $b$, $C_0$, $h$, $p_*$ as in the model and assumptions, and natural logarithms,
--   $$C_1(\phi)=\frac{\phi^4}{512\,s_0^2\sigma^2x_{\max}^2},\qquad C_2(\phi)=\min\Big(\frac12,\frac{\phi^2}{256\,s_0x_{\max}^2}\Big),$$
--   $$C_3=\frac{1024\,K C_0x_{\max}^2}{p_*^3C_1},\qquad C_4=\frac{8Kbx_{\max}}{1-\exp[-p_*^2C_2^2/32]},\qquad C_5=\min\{t\in\mathbb Z^+ : t\ge 24Kq\log t+4(Kq)^2\},$$
--   $$q_0=\max\Big\{\frac{20}{p_*},\frac{4}{p_*C_2^2},\frac{12\log d}{p_*C_2^2},\frac{1024\,x_{\max}^2\log d}{h^2p_*^2C_1}\Big\},$$
--   where in $C_3$, $C_4$, $q_0$ one takes $C_1=C_1(\phi_0)$, $C_2=C_2(\phi_0)$. The regularization parameters of the algorithm are
--   $$\lambda_1=\frac{\phi_0^2p_*h}{64\,s_0x_{\max}},\qquad \lambda_{2,0}=\frac{\phi_0^2}{2s_0}\sqrt{\frac{1}{p_*C_1}}.$$
--
--   These quantities appear in the hypotheses and the bound of Theorem 1.
--
--   **Formalization Note** Each constant is a function of its arguments; the values $C_1(\phi_0)$, $C_2(\phi_0)$ are passed to $C_3$, $C_4$, $q_0$, $\lambda_{2,0}$ as arguments. $C_5$ is the infimum of a set of natural numbers; the set is nonempty, so this is its minimum.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 280 (sparsity parameter), p. 283 (C1 in Proposition 1), pp. 284–285 (Theorem 1: λ1, λ2,0, C1–C5, q0)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic

open Finset

namespace BastaniBayati.LassoBandit

/-- The sparsity parameter `s₀ ∈ [d]` of §2.1, p. 280: the smallest integer `s₀ ≥ 1` with
`‖βᵢ‖₀ ≤ s₀` for every arm `i`, i.e. `max(1, maxᵢ |supp(βᵢ)|)`. -/
noncomputable def sparsity {d K : ℕ} (β : Fin K → Fin d → ℝ) : ℕ :=
  max 1 (Finset.univ.sup fun i => (supp (β i)).card)

/-- `C₁(φ) ≡ φ⁴ / (512 s₀² σ² x_max²)` (Proposition 1, p. 283; Theorem 1, p. 285). -/
noncomputable def C1 (s0 σ xmax φ : ℝ) : ℝ := φ ^ 4 / (512 * s0 ^ 2 * σ ^ 2 * xmax ^ 2)

/-- `C₂(φ) ≡ min(1/2, φ² / (256 s₀ x_max²))` (Theorem 1, p. 285). -/
noncomputable def C2 (s0 xmax φ : ℝ) : ℝ := min (1 / 2) (φ ^ 2 / (256 * s0 * xmax ^ 2))

/-- `C₃ ≡ 1024 K C₀ x_max² / (p_*³ C₁)` with `C₁ = C₁(φ₀)` (Theorem 1, p. 285). -/
noncomputable def C3 (K C0 xmax pstar c1 : ℝ) : ℝ := 1024 * K * C0 * xmax ^ 2 / (pstar ^ 3 * c1)

/-- `C₄ ≡ 8 K b x_max / (1 − exp[−p_*² C₂² / 32])` with `C₂ = C₂(φ₀)` (Theorem 1, p. 285). -/
noncomputable def C4 (K b xmax pstar c2 : ℝ) : ℝ :=
  8 * K * b * xmax / (1 - Real.exp (-(pstar ^ 2 * c2 ^ 2 / 32)))

/-- `C₅ ≡ min{t ∈ ℤ⁺ | t ≥ 24 K q log t + 4(Kq)²}` (Theorem 1, p. 285), natural logarithm.
The set is nonempty (its defining inequality holds for all large `t`), so the infimum is its
minimum. -/
noncomputable def C5 (K q : ℕ) : ℕ :=
  sInf {t : ℕ | 1 ≤ t ∧
    24 * (K : ℝ) * q * Real.log t + 4 * ((K : ℝ) * q) ^ 2 ≤ t}

/-- `q₀ ≡ max{20/p_*, 4/(p_* C₂²), 12 log d/(p_* C₂²), 1024 x_max² log d/(h² p_*² C₁)}`
with `C₁ = C₁(φ₀)`, `C₂ = C₂(φ₀)` (Theorem 1, p. 285). -/
noncomputable def q0 (d : ℕ) (xmax h pstar c1 c2 : ℝ) : ℝ :=
  max (max (20 / pstar) (4 / (pstar * c2 ^ 2)))
    (max (12 * Real.log d / (pstar * c2 ^ 2))
      (1024 * xmax ^ 2 * Real.log d / (h ^ 2 * pstar ^ 2 * c1)))

/-- The forced-sample regularization `λ₁ = φ₀² p_* h / (64 s₀ x_max)` (Theorem 1, p. 284). -/
noncomputable def lam1 (s0 xmax h pstar φ0 : ℝ) : ℝ := φ0 ^ 2 * pstar * h / (64 * s0 * xmax)

/-- The initial all-sample regularization `λ₂,₀ = [φ₀²/(2s₀)] √(1/(p_* C₁))` with `C₁ = C₁(φ₀)`
(Theorem 1, p. 284). -/
noncomputable def lam20 (s0 pstar φ0 c1 : ℝ) : ℝ := φ0 ^ 2 / (2 * s0) * Real.sqrt (1 / (pstar * c1))

end BastaniBayati.LassoBandit


