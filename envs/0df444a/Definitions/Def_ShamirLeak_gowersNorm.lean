-- Prove2me | Definitions.Def_ShamirLeak_gowersNorm
-- name    : ShamirLeak_gowersNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:00.73065+00:00
-- url     : https://prove2.me/theorems/060dd1b6-7dc1-4277-b145-00cc7f15d352
-- title:
--   Gowers norms $\|f\|_{U^t}$ on $\mathbb F_p$ (Definition 8)
-- statement:
--   For a positive integer $t$ and $f:\mathbb F_p\to\mathbb C$,
--
--   $$\|f\|_{U^t}^{2^t}=\mathbb E_{x,h_1,\dots,h_t\in\mathbb F_p}\Big[\prod_{\omega\in\{0,1\}^t}\mathcal C^{|\omega|}f(x+\omega\cdot h)\Big],$$
--
--   where $h=(h_1,\dots,h_t)$, $\mathcal C$ is complex conjugation, $|\omega|=\omega_1+\dots+\omega_t$, and the $t+1$ averaging variables are independent and uniform. The conjugations make the average real and nonnegative.
--
--   The $U^3$ norm of a centered leakage bit (Lemma 16) is what makes the large supports small (Lemma 12, Corollary 3, Lemma 17).
--
--   **Formalization Note** `gowersAvg t f` is the cube average; `gowersNorm t f` takes the real $2^t$-th root of its real part. That the average is real and nonnegative is a fact, not an assumption. Only functions on $\mathbb F_p$ occur in the statements of this mission.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 8, p.13 (PDF 15)

import Mathlib

namespace ShamirLeak

/-- The Gowers cube average
`E_{x, h₁, …, h_t ∈ 𝔽_p} [∏_{ω ∈ {0,1}^t} 𝒞^{|ω|} f(x + ω · h)]` of `f : 𝔽_p → ℂ`
(Definition 8, p.13 (PDF p.15)); it is `‖f‖_{U^t}^{2^t}`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 8, p.13 (PDF p.15).

**Formalization Note.** `ω ∈ {0,1}^t` is `Fin t → Bool`, `|ω|` is the number of `true`
coordinates, `ω · h = ∑_{u : ω u} h_u`, and `𝒞^{|ω|}` is complex conjugation applied `|ω|` times
(the identity for even `|ω|`). The `t + 1` averaging variables range independently and uniformly
over `ZMod p`. -/
noncomputable def gowersAvg {p : ℕ} [NeZero p] (t : ℕ) (f : ZMod p → ℂ) : ℂ :=
  (∑ x : ZMod p, ∑ h : Fin t → ZMod p, ∏ ω : Fin t → Bool,
      (if Even (Finset.univ.filter (fun u => ω u = true)).card then
        f (x + ∑ u, if ω u then h u else 0)
      else star (f (x + ∑ u, if ω u then h u else 0)))) / ((p : ℂ) ^ (t + 1))

/-- The **Gowers norm** `‖f‖_{U^t}` of `f : 𝔽_p → ℂ` (Definition 8, p.13 (PDF p.15)): the
`2^t`-th root of the cube average `gowersAvg t f`.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 8, p.13.

**Formalization Note.** The paper notes (p.13) that the conjugations make the cube average real
and nonnegative; the definition reads off its real part and takes the real `2^t`-th root
(`Real.rpow` with exponent `1 / 2^t`). This is a fact about the average, not an assumption. Only
functions on `𝔽_p` occur in the statements of this mission. -/
noncomputable def gowersNorm {p : ℕ} [NeZero p] (t : ℕ) (f : ZMod p → ℂ) : ℝ :=
  (gowersAvg t f).re ^ ((1 : ℝ) / 2 ^ t)

end ShamirLeak


