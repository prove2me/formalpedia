-- Prove2me | Definitions.Def_StaggeredRollout_TOpt_Quadratic
-- name    : StaggeredRollout_TOpt_Quadratic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:59:30.931355+00:00
-- url     : https://prove2.me/theorems/65969d58-0435-4267-8bab-35ef31398e43
-- title:
--   Lemma EC.1.2, (EC.1.7), (EC.2.6) — windows, P_{1_{Tℓ}}, the corrected b_ℓ, and the quadratic terms f_{j,1}, f_{j,X}, f_{j,U}
-- statement:
--   Objects of the separable quadratic representation of $\operatorname{tr}\operatorname{Prec}(\hat\tau)$ (Lemma EC.1.2, p. ec12) and of the relaxed problem in the proof of Theorem 3.1 (p. ec21).
--
--   Let $T_\ell=T-\ell$. For $j=1,\dots,\ell+1$ the *window* $j$ is the periods $j,\dots,j_\ell$ with $j_\ell=j+T_\ell-1$. For a path $\omega\in\mathbb R^T$ write $\omega_{j:j_\ell}=(\omega_j,\dots,\omega_{j_\ell})^\top$, and for a treatment array $z\in\mathbb R^{N\times T}$ write $\omega_t=\frac1N\sum_{i=1}^N z_{it}$ and $z_t=(z_{1t},\dots,z_{Nt})^\top$. Let
--   $$
--   P_{1_{T_\ell}}=I_{T_\ell}-\tfrac1{T_\ell}1_{T_\ell}1_{T_\ell}^\top,\qquad b_{\ell,t}=\frac{T_\ell+1-2t}{T_\ell}\quad(t=1,\dots,T_\ell).
--   $$
--   The three quadratic terms are
--   $$
--   f_{j,1}(\omega)=\omega_{j:j_\ell}^\top P_{1_{T_\ell}}\omega_{j:j_\ell}+2b_\ell^\top\omega_{j:j_\ell},
--   $$
--   $$
--   f_{j,X}(z)=\tfrac1N\,z_{j:j_\ell}^\top\big(P_{1_{T_\ell}}\otimes H_X\big)z_{j:j_\ell},\qquad
--   f_{j,U}(z)=\tfrac1N\,z_{j:j_\ell}^\top\big(P_{1_{T_\ell}}\otimes U(I_{d_u}+U^\top U)^{-1}U^\top\big)z_{j:j_\ell},
--   $$
--   where $z_{j:j_\ell}=(z_j^\top,\dots,z_{j_\ell}^\top)^\top$ and $H_X$ is the orthogonal projector onto the column space of $X$. Finally $f_1(\omega)=\sum_{j=1}^{\ell+1}f_{j,1}(\omega)$ is the objective of (EC.2.6).
--
--   Two of these differ from the printed page. The page prints $b_{\ell,t}=(T_\ell+2-2t)/T_\ell$, and the value $(T_\ell+1-2t)/T_\ell$ used here is the one of the display closing the proof of Lemma EC.1.2 (p. ec20) and of Example 3.2. The page prints $f_{j,X}=\sum_k(\omega^{x_k}_{j:j_\ell})^\top P_{1_{T_\ell}}\omega^{x_k}_{j:j_\ell}$ with $\omega^{x_k}_t=\frac1N\sum_iX_{ik}z_{it}$, which coincides with the form here only when $X^\top X=N\,I$. The theorem items that use these objects give counterexamples to the printed forms.
--
--   **Formalization Note** Windows are 0-based: window `j : Fin (ℓ+1)` covers the 0-based periods `j, …, j + T_ℓ − 1`. The centred cross-sections are $\hat z_s=z_{j+s}-\frac1{T_\ell}\sum_{s'}z_{j+s'}$, and the $X$-term is written without a pseudo-inverse as $f_{j,X}=\frac1N\sum_s\big(\|\hat z_s\|^2-\min_c\|\hat z_s-Xc\|^2\big)=\frac1N\sum_s\|H_X\hat z_s\|^2$, the minimum being a real infimum of a nonnegative quadratic that is attained. The $U$-term writes the Kronecker product blockwise, $\frac1N\sum_{s,s'}(P_{1_{T_\ell}})_{ss'}\,z_{j+s}^\top U(I+U^\top U)^{-1}U^\top z_{j+s'}$; $I+U^\top U$ is always invertible. $T_\ell$ is the natural number $T-\ell$ cast to $\mathbb R$.
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, p. ec12, Lemma EC.1.2 and (EC.1.7); p. ec20 (closing display of the proof of Lemma EC.1.2); p. ec21, (EC.2.6)

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting

namespace StaggeredRollout.TOpt
open Matrix

/-- The window period of Lemma EC.1.2: for the window `j` (0-based, the paper's `j + 1`) and the window
index `s : Fin (T − ℓ)`, the 0-based period `j + s`. Window `j` covers the paper's periods
`j + 1, …, j + T_ℓ` with `T_ℓ = T − ℓ`. -/
def win {T : ℕ} (ℓ : ℕ) (j : Fin (ℓ + 1)) (s : Fin (T - ℓ)) : Fin T :=
  ⟨j.val + s.val, by have := s.isLt; have := j.isLt; omega⟩

/-- The treated fraction (in ±1 units) `ω_t = (1/N) Σ_i z_it` of a treatment path `z`. -/
noncomputable def omegaBar {N T : ℕ} (z : Fin N → Fin T → ℝ) (t : Fin T) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, z i t

/-- The centring projector `P_{1_n} = I_n − (1/n) 1_n 1_nᵀ`. -/
noncomputable def Pone (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))

/-- The vector `b_ℓ ∈ ℝ^{T_ℓ}` of Lemma EC.1.2, corrected: `b_{ℓ,t} = (T_ℓ + 1 − 2t)/T_ℓ` for the
1-based window index `t = s + 1`. -/
noncomputable def bl (ℓ T : ℕ) : Fin (T - ℓ) → ℝ :=
  fun s => (((T - ℓ : ℕ) : ℝ) + 1 - 2 * ((s.val : ℝ) + 1)) / ((T - ℓ : ℕ) : ℝ)

/-- `f_{j,1}` of (EC.1.7) as a function of a path `ω : [T] → ℝ`:
`ω_{j:j_ℓ}ᵀ P_{1_{T_ℓ}} ω_{j:j_ℓ} + 2 b_ℓᵀ ω_{j:j_ℓ}`, with the corrected `b_ℓ`. -/
noncomputable def f1j (ℓ T : ℕ) (ω : Fin T → ℝ) (j : Fin (ℓ + 1)) : ℝ :=
  (fun s => ω (win ℓ j s)) ⬝ᵥ (Pone (T - ℓ) *ᵥ fun s => ω (win ℓ j s))
    + 2 * (bl ℓ T ⬝ᵥ fun s => ω (win ℓ j s))

/-- `f_1(ω) = Σ_{j=1}^{ℓ+1} f_{j,1}(ω)`, the objective of (EC.2.6) (with the window `t = j, …, j_ℓ`
in the linear term). -/
noncomputable def f1 (ℓ T : ℕ) (ω : Fin T → ℝ) : ℝ :=
  ∑ j : Fin (ℓ + 1), f1j ℓ T ω j

/-- The cross-section `z_{j+s}` of window `j`, centred over the window:
`ẑ_s = z_{j+s} − (1/T_ℓ) Σ_{s'} z_{j+s'}` (the `s`-th block of `(P_{1_{T_ℓ}} ⊗ I_N) z_{j:j_ℓ}`). -/
noncomputable def zCent {N T : ℕ} (ℓ : ℕ) (z : Fin N → Fin T → ℝ) (j : Fin (ℓ + 1))
    (s : Fin (T - ℓ)) : Fin N → ℝ :=
  fun i => z i (win ℓ j s) - ((T - ℓ : ℕ) : ℝ)⁻¹ * ∑ s', z i (win ℓ j s')

/-- The observed-covariate term of Lemma EC.1.2, corrected:
`f_{j,X}(Z) = (1/N) z_{j:j_ℓ}ᵀ (P_{1_{T_ℓ}} ⊗ H_X) z_{j:j_ℓ}` with `H_X` the orthogonal projector onto
the column space of `X`, written as `(1/N) Σ_s ‖H_X ẑ_s‖²` with
`‖H_X v‖² = ‖v‖² − min_c ‖v − X c‖²`. -/
noncomputable def fXj {N T dx : ℕ} (ℓ : ℕ) (X : Matrix (Fin N) (Fin dx) ℝ)
    (z : Fin N → Fin T → ℝ) (j : Fin (ℓ + 1)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ s : Fin (T - ℓ),
    (zCent ℓ z j s ⬝ᵥ zCent ℓ z j s
      - ⨅ c : Fin dx → ℝ, (zCent ℓ z j s - X *ᵥ c) ⬝ᵥ (zCent ℓ z j s - X *ᵥ c))

/-- The latent-covariate term of Lemma EC.1.2:
`f_{j,U}(Z) = (1/N) z_{j:j_ℓ}ᵀ M_U z_{j:j_ℓ}` with `M_U = P_{1_{T_ℓ}} ⊗ U (I_{du} + UᵀU)⁻¹ Uᵀ`, written
blockwise: `(1/N) Σ_{s,s'} (P_{1_{T_ℓ}})_{ss'} z_{j+s}ᵀ U (I + UᵀU)⁻¹ Uᵀ z_{j+s'}`. -/
noncomputable def fUj {N T du : ℕ} (ℓ : ℕ) (U : Matrix (Fin N) (Fin du) ℝ)
    (z : Fin N → Fin T → ℝ) (j : Fin (ℓ + 1)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ s : Fin (T - ℓ), ∑ s' : Fin (T - ℓ),
    Pone (T - ℓ) s s' *
      ((fun i => z i (win ℓ j s)) ⬝ᵥ
        ((U * (1 + Uᵀ * U)⁻¹ * Uᵀ) *ᵥ fun i => z i (win ℓ j s')))

end StaggeredRollout.TOpt


