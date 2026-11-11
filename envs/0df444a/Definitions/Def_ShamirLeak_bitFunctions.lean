-- Prove2me | Definitions.Def_ShamirLeak_bitFunctions
-- name    : ShamirLeak_bitFunctions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:01.904295+00:00
-- url     : https://prove2.me/theorems/d368b138-7087-4f82-8019-f15fab9901b0
-- title:
--   One-bit leakage: $\theta_i$, $\mu_i$, and the centered bits $g_i$, $f_i$ (§3.4, §6.2.2)
-- statement:
--   Let $\tau_i:\mathbb F_p\to\{0,1\}$ and put $\theta_i=\mathbb E_x[\tau_i(x)]$ and $\mu_i=1-2\theta_i$. If $\tau_i$ is nonconstant, so that $0<\theta_i<1$, define
--
--   $$g_i(x)=\frac{\tau_i(x)-\theta_i}{\sqrt{\theta_i(1-\theta_i)}},\qquad f_i(x)=2(\tau_i(x)-\theta_i);$$
--
--   if $\tau_i$ is constant, put $g_i=f_i=0$. Write $g_A=(g_i)_{i\in A}$ and $f_A=(f_i)_{i\in A}$.
--
--   The averages $\Gamma_C(g_A)$ and $\Gamma_C(f_A)$ are the $L^2$ and $L^1$ sizes of the components of the one-bit leakage distance (Lemma 7).
--
--   **Formalization Note** Bits are `Bool` with `true` $=1$; the expectation is the average over the $p$ elements of $\mathbb F_p$. The functions are complex-valued with real values so that they can be fed to $\Gamma_C$ and to the Fourier transform.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §3.4, p.18 (PDF 20); §6.2.2, p.32 (PDF 34)

import Mathlib

namespace ShamirLeak

/-- The bit `b ∈ {0, 1}` as a real number (`true` = 1, `false` = 0). -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- The mean `θᵢ = E_x[τᵢ(x)]` of a one-bit leakage map `τᵢ : 𝔽_p → {0, 1}` (§3.4, p.18 (PDF p.20)),
the average of `τᵢ` over the `p` elements of `𝔽_p`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §3.4, p.18 (PDF p.20). -/
noncomputable def theta {p n : ℕ} [NeZero p] (τ : Fin n → ZMod p → Bool) (i : Fin n) : ℝ :=
  (∑ x : ZMod p, bitVal (τ i x)) / (p : ℝ)

/-- The bias `µᵢ = 1 − 2θᵢ` (§6.2.2, p.32 (PDF p.34)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §6.2.2, p.32. -/
noncomputable def mu {p n : ℕ} [NeZero p] (τ : Fin n → ZMod p → Bool) (i : Fin n) : ℝ :=
  1 - 2 * theta τ i

/-- The normalized centered bit `gᵢ(x) = (τᵢ(x) − θᵢ)/√(θᵢ(1 − θᵢ))` if `τᵢ` is nonconstant
(`0 < θᵢ < 1`), and `gᵢ = 0` if `τᵢ` is constant (§3.4, p.18 (PDF p.20)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §3.4, p.18.

**Formalization Note.** `0 < θᵢ < 1` holds exactly when `τᵢ` is nonconstant. The value is
complex (a real number) so that it can be fed to `Γ_C` and the Fourier transform. -/
noncomputable def gBit {p n : ℕ} [NeZero p] (τ : Fin n → ZMod p → Bool) (i : Fin n)
    (x : ZMod p) : ℂ :=
  if 0 < theta τ i ∧ theta τ i < 1 then
    (((bitVal (τ i x) - theta τ i) / Real.sqrt (theta τ i * (1 - theta τ i)) : ℝ) : ℂ)
  else 0

/-- The centered bit `fᵢ(x) = 2(τᵢ(x) − θᵢ)` if `τᵢ` is nonconstant (`0 < θᵢ < 1`), and `fᵢ = 0`
if `τᵢ` is constant (§3.4, p.18 (PDF p.20)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §3.4, p.18.

**Formalization Note.** For a constant map the formula `2(τᵢ − θᵢ)` is itself `0`, so the case
split only mirrors the paper's wording. Complex-valued, like `gBit`. -/
noncomputable def fBit {p n : ℕ} [NeZero p] (τ : Fin n → ZMod p → Bool) (i : Fin n)
    (x : ZMod p) : ℂ :=
  if 0 < theta τ i ∧ theta τ i < 1 then ((2 * (bitVal (τ i x) - theta τ i) : ℝ) : ℂ) else 0

end ShamirLeak


