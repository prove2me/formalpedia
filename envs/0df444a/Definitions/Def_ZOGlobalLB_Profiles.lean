-- Prove2me | Definitions.Def_ZOGlobalLB_Profiles
-- name    : ZOGlobalLB_Profiles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:37.040227+00:00
-- url     : https://prove2.me/theorems/20a236ac-51b6-42bd-8426-4ebedc51c369
-- title:
--   Scalar profiles, cutoffs, the zero-chain $B_T$ and activations $g_i$
-- statement:
--   The scalar building blocks of the hard instance:
--
--   1. $\Psi(t)=0$ for $t\le 1/2$ and $\Psi(t)=\exp(1-(2t-1)^{-2})$ for $t>1/2$; $\Phi(t)=\sqrt e\int_{-\infty}^t e^{-u^2/2}\,du$.
--   2. The zero-chain on $w\in\mathbb R^T$: $b_1(w)=-\Phi(w_1)$, $b_i(w)=\Psi(-w_{i-1})\Phi(-w_i)-\Psi(w_{i-1})\Phi(w_i)$ for $i>1$, and $B_T=\sum_{i=1}^T b_i$.
--   3. The clamped quintic $S_5(u)=10u^3-15u^4+6u^5$ on $[0,1]$, $0$ below and $1$ above; $\Gamma(t)=S_5(4t-1)$ and the activations $g_i(w)=\Gamma(|w_i|)$.
--   4. The cutoffs $\tau(t)=1-S_5(2t/\rho_0-1)$ and $\chi(q)=1-S_5(\|q\|^2/\beta^2-1)$, the well $h(q)=4(\sqrt{1+\|q\|^2}-1)$, and the gate corrections $c_i(w)=b_i(w)\tau(\|g_{\ge i}(w)\|)$.
--   5. The constants $A=128$, $\beta=16$, $\rho_0=3/32$.
--
--   **Formalization Note.** Indices are 0-based (`Fin T`): $b_1$ is index $0$. Suffix norms $\|g_{\ge i}\|$ and $\|g_{>i}\|$ are square roots of finite sums.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Section 3.1, (15), (16), (21), (22), (24), (25), pp.9–13; Appendix B, p.36

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible

open MeasureTheory

namespace ZOGlobalLB

/-! # Scalar profiles, cutoffs and the zero-chain

Xia, Yuan, *On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*,
arXiv:2610.19652, Section 3.1, pp.9–13, (15), (16), (21), (22), (25), and Appendix B, p.36.

**Formalization Note.** Stages are 1-based in the paper and `Fin T` (0-based) here: the paper's
`b₁` is `chainB w 0`, and the paper's `b_i` for `i > 1` is `chainB w (i-1)`, which uses
`w_{i-1}` and `w_i`. Chain vectors `w ∈ ℝᵀ` live in `E T` (Euclidean norm). -/

/-- The displacement scale `A = 128` (p.13). -/
noncomputable def Acst : ℝ := 128

/-- The gate radius scale `β = 16` (p.13). -/
noncomputable def betaC : ℝ := 16

/-- The suffix-cutoff threshold `ρ₀ = 3/32` (p.13). -/
noncomputable def rho0 : ℝ := 3 / 32

/-- `Ψ(t) = 0` for `t ≤ 1/2` and `exp(1 - (2t-1)⁻²)` for `t > 1/2` (15), p.9; p.36.
The case split makes the value at `t = 1/2` the paper's `0`. -/
noncomputable def Psi (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then 0 else Real.exp (1 - ((2 * t - 1) ^ 2)⁻¹)

/-- `Φ(t) = √e ∫_{-∞}^t e^{-u²/2} du` (15), p.9. -/
noncomputable def PhiG (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * ∫ u in Set.Iic t, Real.exp (-u ^ 2 / 2)

/-- The clamped quintic `S₅`: `10u³ - 15u⁴ + 6u⁵` on `[0, 1]`, `0` for `u ≤ 0`, `1` for
`u ≥ 1` (p.11). -/
noncomputable def S5 (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if 1 ≤ u then 1 else 10 * u ^ 3 - 15 * u ^ 4 + 6 * u ^ 5

/-- `Γ(t) = S₅(4t - 1)` (21), p.11. -/
noncomputable def Gam (t : ℝ) : ℝ := S5 (4 * t - 1)

/-- The suffix cutoff `τ(t) = 1 - S₅(2t/ρ₀ - 1)` (25), p.12. -/
noncomputable def tauC (t : ℝ) : ℝ := 1 - S5 (2 * t / rho0 - 1)

/-- The spatial cutoff `χ(q) = 1 - S₅(‖q‖²/β² - 1)` (25), p.12. -/
noncomputable def chiC {m : ℕ} (q : E m) : ℝ := 1 - S5 (‖q‖ ^ 2 / betaC ^ 2 - 1)

/-- The workspace well `h(q) = 4(√(1 + ‖q‖²) - 1)` (22), p.11. -/
noncomputable def wellH {m : ℕ} (q : E m) : ℝ := 4 * (Real.sqrt (1 + ‖q‖ ^ 2) - 1)

/-- The zero-chain terms (16), p.9 (and p.36): `b₁(w) = -Φ(w₁)` and
`b_i(w) = Ψ(-w_{i-1})Φ(-w_i) - Ψ(w_{i-1})Φ(w_i)` for `i > 1`. 0-based: `chainB w 0 = b₁`. -/
noncomputable def chainB {T : ℕ} (w : E T) : Fin T → ℝ
  | ⟨0, _⟩ => -PhiG (w ⟨0, by omega⟩)
  | ⟨k + 1, hk⟩ =>
      Psi (-w ⟨k, by omega⟩) * PhiG (-w ⟨k + 1, hk⟩) - Psi (w ⟨k, by omega⟩) * PhiG (w ⟨k + 1, hk⟩)

/-- The length-`T` chain `B_T(w) = Σ_{i=1}^T b_i(w)` (16), p.9. -/
noncomputable def chainBT {T : ℕ} (w : E T) : ℝ := ∑ i, chainB w i

/-- The activations `g_i(w) = Γ(|w_i|)` (21), p.11. -/
noncomputable def gAct {T : ℕ} (w : E T) (i : Fin T) : ℝ := Gam |w i|

/-- The activation vector `g = (g_1, …, g_T) ∈ ℝᵀ` (Lemma B.1, p.37). -/
noncomputable def gVec {T : ℕ} (w : E T) : E T := WithLp.toLp 2 (fun i => gAct w i)

/-- The suffix norm `‖g_{≥i}(w)‖ = ‖(g_i, …, g_T)‖` (24), p.12. -/
noncomputable def sufGe {T : ℕ} (w : E T) (i : Fin T) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => i ≤ j), gAct w j ^ 2)

/-- The strict suffix norm `‖g_{>i}(w)‖ = ‖(g_{i+1}, …, g_T)‖` (34), p.19. -/
noncomputable def sufGt {T : ℕ} (w : E T) (i : Fin T) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => i < j), gAct w j ^ 2)

/-- The gate corrections `c_i(w) = b_i(w) τ(‖g_{≥i}(w)‖)` (24), p.12. -/
noncomputable def cCorr {T : ℕ} (w : E T) (i : Fin T) : ℝ := chainB w i * tauC (sufGe w i)

end ZOGlobalLB


