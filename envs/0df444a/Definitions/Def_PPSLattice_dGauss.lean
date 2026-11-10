-- Prove2me | Definitions.Def_PPSLattice_dGauss
-- name    : PPSLattice_dGauss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:04.729473+00:00
-- url     : https://prove2.me/theorems/5831e717-503f-404c-9877-2f3867c7888c
-- title:
--   Discrete Gaussian $D_{\mathbb Z,\sigma}$
-- statement:
--   For a width parameter $\sigma>0$, $D_{\mathbb Z,\sigma}$ is the law on $\mathbb Z$ with
--   $$\Pr[x]=\frac{\rho_\sigma(x)}{\sum_{y\in\mathbb Z}\rho_\sigma(y)},\qquad \rho_\sigma(x)=e^{-x^2/(2\sigma^2)}.$$
--
--   It is the LWE error distribution of Assumption 3.4 and of skEnc in Construction 4.6.
--
--   **Formalization Note** The [Lyu12] width convention is used (the paper gives no formula). For $\sigma\le0$, where nothing is defined, the law is the point mass at $0$; every statement uses $\sigma>0$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Discrete Gaussian, p.16

import Mathlib
import Definitions.Def_PPSLattice_gaussW
set_option autoImplicit false

namespace PPSLattice

/-- The **discrete Gaussian** `D_{Z,σ}` on the integers: for `σ > 0`, the probability of `x ∈ Z` is
`ρ_σ(x) / Σ_{y ∈ Z} ρ_σ(y)` with `ρ_σ(x) = exp(−x²/(2σ²))` (`gaussW`).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Discrete Gaussian, p.16 ("We write D_{Z,σ} to denote the discrete gaussian distribution
with width parameter σ > 0"), in the convention of [Lyu12] under which Lemma 3.2 is stated.

**Formalization Note.** The paper gives no formula; the width convention `exp(−x²/(2σ²))` is the
one of [Lyu12], the source of Lemma 3.2. For `σ ≤ 0`, where the paper defines nothing, the law is
the point mass at `0`; every statement of the mission uses `σ > 0`. -/
noncomputable def dGauss (σ : ℝ) : PMF ℤ :=
  if hσ : 0 < σ then
    PMF.normalize (fun x => ENNReal.ofReal (gaussW σ x))
      (by
        rw [← ENNReal.ofReal_tsum_of_nonneg (f := gaussW σ) (fun x => (Real.exp_pos _).le) (gaussW_summable σ hσ)]
        refine (ENNReal.ofReal_pos.mpr ?_).ne'
        exact (gaussW_summable σ hσ).tsum_pos (fun x => (Real.exp_pos _).le) 0 (Real.exp_pos _))
      (by
        rw [← ENNReal.ofReal_tsum_of_nonneg (f := gaussW σ) (fun x => (Real.exp_pos _).le) (gaussW_summable σ hσ)]
        exact ENNReal.ofReal_ne_top)
  else PMF.pure 0

end PPSLattice


