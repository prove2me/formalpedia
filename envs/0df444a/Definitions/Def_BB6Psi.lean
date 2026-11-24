-- Prove2me | Definitions.Def_BB6Psi
-- name    : BB6Psi
-- status  : Definition
-- author  : @alon yuval
-- created : 2026-11-24T06:33:07.778122+00:00
-- url     : https://prove2.me/theorems/a8ecd56a-7ab7-4d09-95fb-120a52febf87
-- title:
--   Auxiliary determinants $\Psi_{\mathcal I}(x)$ of the Mignotte–Voutier kit (eqs. (3.5)–(3.8))
-- statement:
--   The auxiliary analytic determinants used in the proof of Proposition 3.7 of the Mignotte–Voutier kit (arXiv:2205.08899, Section 3.3), for positive-integer $\alpha_1,\alpha_2,\alpha_3$. Write $\Lambda=b_1\log\alpha_1+b_2\log\alpha_2-b_3\log\alpha_3$ and let $\Lambda'$ be as in `BB6Kit.lamPrime`. For a row $(k_i,m_i,\ell_i)$ and a column $(r_j,s_j,t_j)$ set:
--
--   - `lam`: $\lambda_i=\ell_i-\tfrac{L-1}{2}$;
--   - `eta`: $\eta_j=r_j+t_j\beta_1-\eta_0$, where $\beta_1=b'_1/b'_3$ and $\eta_0=(R-1)/2+\beta_1(T-1)/2$;
--   - `zeta`: $\zeta_j=s_j+t_j\beta_2-\zeta_0$, where $\beta_2=b''_2/b''_3$ and $\zeta_0=(S-1)/2+\beta_2(T-1)/2$;
--   - `theta`: $\theta_{i,j}=(\mathrm e^{-\lambda_i t_j\Lambda/b_3}-1)/\Lambda'$. Then $\alpha_3^{\lambda t}=\alpha_1^{\lambda t\beta_1}\alpha_2^{\lambda t\beta_2}(1+\theta\Lambda')$, as in (3.5) with this sign convention for $\Lambda$;
--   - `phi`: $\varphi_i(\eta,\zeta)=\dfrac{b_3'^{k_i}b_3''^{m_i}}{k_i!\,m_i!}\,\eta^{k_i}\zeta^{m_i}\alpha_1^{\lambda_i\eta}\alpha_2^{\lambda_i\zeta}$ over $\mathbb C$, as in (3.7).
--
--   For $\mathcal I\subseteq\{1,\dots,N\}$, `psi` is $$\Psi_{\mathcal I}(x)=\det\bigl(c_{i,j}\,\varphi_i(x\eta_j,x\zeta_j)\bigr)_{i,j},\qquad c_{i,j}=1\text{ if }i\in\mathcal I,\quad c_{i,j}=\theta_{i,j}\text{ otherwise},$$ as in (3.8). The determinant $\Delta$ of (2.6) expands as $\alpha^{M}\sum_{\mathcal I}(\Lambda')^{N-|\mathcal I|}\Psi_{\mathcal I}(1)$ (eq. (3.10)), and Schwarz's lemma is applied to each $\Psi_{\mathcal I}$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 3.3, eqs. (2.3), (2.4), (3.5)-(3.8).

import Mathlib
import Definitions.Def_BB6Kit

namespace BB6Psi

/-- `λ_i = ℓ_i - (L-1)/2` for a row `(k_i, m_i, ℓ_i)` (eq. (2.4)). -/
noncomputable def lam (L : ℕ) (p : ℕ × ℕ × ℕ) : ℝ := (p.2.2 : ℝ) - ((L : ℝ) - 1) / 2

/-- `η_j = r_j + t_j β₁ - η₀` with `β₁ = b′₁/b′₃`, `η₀ = (R-1)/2 + β₁(T-1)/2`. -/
noncomputable def eta (R T b1' b3' : ℕ) (q : ℕ × ℕ × ℕ) : ℝ :=
  (q.1 : ℝ) + (q.2.2 : ℝ) * ((b1' : ℝ) / b3') - (((R : ℝ) - 1) / 2 + (b1' : ℝ) / b3' * (((T : ℝ) - 1) / 2))

/-- `ζ_j = s_j + t_j β₂ - ζ₀` with `β₂ = b″₂/b″₃`, `ζ₀ = (S-1)/2 + β₂(T-1)/2`. -/
noncomputable def zeta (S T b2'' b3'' : ℕ) (q : ℕ × ℕ × ℕ) : ℝ :=
  (q.2.1 : ℝ) + (q.2.2 : ℝ) * ((b2'' : ℝ) / b3'') - (((S : ℝ) - 1) / 2 + (b2'' : ℝ) / b3'' * (((T : ℝ) - 1) / 2))

/-- `θ_{i,j} = (e^{-λ_i t_j Λ / b₃} - 1)/Λ′`, for `Λ = b₁ log α₁ + b₂ log α₂ - b₃ log α₃`
(so that `α₃^{λ t} = α₁^{λ t β₁} α₂^{λ t β₂} (1 + θ Λ′)`, eq. (3.5)). -/
noncomputable def theta (L T b3 : ℕ) (Λ : ℝ) (p q : ℕ × ℕ × ℕ) : ℝ :=
  (Real.exp (-(lam L p * (q.2.2 : ℝ) * Λ / (b3 : ℝ))) - 1) / BB6Kit.lamPrime L T b3 Λ

/-- `φ_i(η, ζ) = b′₃^{k} b″₃^{m} / (k! m!) · η^k ζ^m α₁^{λ_i η} α₂^{λ_i ζ}` (eq. (3.7)), over `ℂ`. -/
noncomputable def phi (b3' b3'' α1 α2 L : ℕ) (p : ℕ × ℕ × ℕ) (η ζ : ℂ) : ℂ :=
  ((b3' : ℂ) ^ p.1 * (b3'' : ℂ) ^ p.2.1 / ((p.1.factorial : ℂ) * (p.2.1.factorial : ℂ))) * η ^ p.1 * ζ ^ p.2.1 *
    Complex.exp ((lam L p : ℂ) * (η * (Real.log (α1 : ℝ) : ℂ) + ζ * (Real.log (α2 : ℝ) : ℂ)))

/-- `Ψ_ℐ(x) = det Φ_ℐ(x)` (eqs. (3.7), (3.8)): row `i` is `φ_i(x η_j, x ζ_j)` if `i ∈ ℐ`
and `θ_{i,j} φ_i(x η_j, x ζ_j)` otherwise. -/
noncomputable def psi (N L R S T b1' b3' b2'' b3'' b3 α1 α2 : ℕ) (Λ : ℝ) (kml rst : Fin N → ℕ × ℕ × ℕ)
    (I : Finset (Fin N)) (x : ℂ) : ℂ :=
  (Matrix.of fun i j =>
    (if i ∈ I then (1 : ℂ) else (theta L T b3 Λ (kml i) (rst j) : ℂ)) *
      phi b3' b3'' α1 α2 L (kml i) (x * (eta R T b1' b3' (rst j) : ℂ)) (x * (zeta S T b2'' b3'' (rst j) : ℂ))).det

end BB6Psi


