-- Prove2me | Definitions.Def_LowRankShifts_MatPoly_Fourier
-- name    : LowRankShifts_MatPoly_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:56:38.64728+00:00
-- url     : https://prove2.me/theorems/74b79e7b-c3e7-47fe-a9a0-e14582dfae3f
-- title:
--   The Fourier transform on F_p^{n×m} and the law of UVᵀ for uniform U, V
-- statement:
--   Let $p$ be a prime and $\mathbb F_p=\mathbb Z/p\mathbb Z$. For $W,X\in\mathbb F_p^{n\times m}$ the **Frobenius inner product** is $\langle W,X\rangle=\mathrm{Tr}(W^TX)=\sum_{i,j}W_{ij}X_{ij}\in\mathbb F_p$. With $\omega_p=e^{2\pi i/p}$, the **Fourier transform** of $f:\mathbb F_p^{n\times m}\to\mathbb C$ is
--
--   $$\hat f(W)=\sum_{X\in\mathbb F_p^{n\times m}} f(X)\,\omega_p^{-\langle W,X\rangle}.$$
--
--   For $r\ge 0$, the **law of $UV^T$** is the probability mass function
--   $$\mu(L)=\Pr_{U\sim\mathbb F_p^{n\times r},\,V\sim\mathbb F_p^{m\times r}}[UV^T=L]$$
--   for independent uniform $U$ and $V$.
--
--   **Formalization Note.** $\omega_p^{-z}$ for $z\in\mathbb F_p$ is $\exp(-2\pi i\,z.\mathrm{val}/p)$, where $z.\mathrm{val}\in\{0,\dots,p-1\}$ is the canonical representative (`omegaInvPow`). `frob`, `fourier` and `lowRankLaw` are the three objects; the probability is `unifProb` from the published `ZamirInversion581_Mult_Uniform`.
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), pp. 14–15 (PDF 17–18), §2.5; p. 16 (PDF 19), Claim 3.1

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform

open Matrix

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-!
# The Fourier transform on `F_p^{n×m}` and the law of `UVᵀ`

Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, *Worst-Case to Average-Case Reductions
for Linear Algebra: Optimal, Simple, and General*, STOC 2027 submission, §2.5 (pp. 14–15) and
Claim 3.1 (p. 16).

* `frob W X = Tr(Wᵀ X) = Σ_{i,j} W_{ij} X_{ij} ∈ F_p`, the Frobenius inner product.
* `fourier f W = Σ_{X ∈ F_p^{n×m}} f(X) ω_p^{−⟨W, X⟩}` with `ω_p = e^{2πi/p}`; the power
  `ω_p^{−z}` for `z ∈ F_p` is `exp(−2πi · z.val / p)`, where `z.val ∈ {0, …, p − 1}` is the
  canonical representative.
* `lowRankLaw n m r L = Pr_{U ∼ F_p^{n×r}, V ∼ F_p^{m×r}}[U Vᵀ = L]`, the probability mass function
  of `UVᵀ` for independent uniform `U` and `V`.
-/

variable {p : ℕ} [Fact p.Prime]

/-- The Frobenius inner product `⟨W, X⟩ = Tr(Wᵀ X) = Σ_{i,j} W_{ij} X_{ij}`. -/
def frob {n m : ℕ} (W X : Matrix (Fin n) (Fin m) (ZMod p)) : ZMod p :=
  ∑ i, ∑ j, W i j * X i j

/-- `ω_p^{−z} = exp(−2πi · z.val / p)` for `z ∈ F_p`, with `ω_p = e^{2πi/p}`. -/
noncomputable def omegaInvPow (z : ZMod p) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * (z.val : ℂ) / (p : ℂ)))

/-- The Fourier transform `f̂(W) = Σ_X f(X) ω_p^{−⟨W, X⟩}` of `f : F_p^{n×m} → ℂ`. -/
noncomputable def fourier {n m : ℕ} (f : Matrix (Fin n) (Fin m) (ZMod p) → ℂ)
    (W : Matrix (Fin n) (Fin m) (ZMod p)) : ℂ :=
  ∑ X, f X * omegaInvPow (frob W X)

/-- `µ(L) = Pr_{U ∼ F_p^{n×r}, V ∼ F_p^{m×r}}[U Vᵀ = L]`, for independent uniform `U`, `V`. -/
noncomputable def lowRankLaw (n m r : ℕ) (L : Matrix (Fin n) (Fin m) (ZMod p)) : ℝ :=
  ZamirInversion581.Mult.unifProb
    fun UV : Matrix (Fin n) (Fin r) (ZMod p) × Matrix (Fin m) (Fin r) (ZMod p) =>
      UV.1 * UV.2ᵀ = L

end LowRankShifts.MatPoly


