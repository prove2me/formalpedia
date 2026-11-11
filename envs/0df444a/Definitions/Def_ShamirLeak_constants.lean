-- Prove2me | Definitions.Def_ShamirLeak_constants
-- name    : ShamirLeak_constants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:06.13973+00:00
-- url     : https://prove2.me/theorems/9a6ada84-b4a9-4a4a-b6e8-d3107caf410e
-- title:
--   The constants $\eta_Q$, $\kappa_0$, $\beta_0$ and the exponents $G(c,\zeta,\varepsilon)$, $H(c,\varepsilon)$
-- statement:
--   The explicit constants of the paper, all with natural logarithms:
--
--   1. $\eta_Q=\min\{(Q-1)/2,\ \cos^2(\pi/(8Q))\}$ (Lemma 9), so that $\eta_2=1/2$;
--   2. $\kappa_0=(3/4)^{1/8}$ and $\beta_0=(\log\kappa_0)^2/64$ (§6.2);
--   3. the small-support exponent of Lemma 15,
--   $$G(c,\zeta,\varepsilon)=(1-2c+\zeta)\log2+\log\frac1{2(c-\zeta)}-\frac{\varepsilon^2}2;$$
--   4. the large-support exponent of Proposition 4,
--   $$H(c,\varepsilon)=h(\varepsilon)+\max\Big\{\frac{3c-1}2\log\kappa_0+\sqrt{\beta_0},\ (1-2c)(\log2+1/2)-\frac{\beta_0}2\Big\},$$
--   with $h(t)=-t\log t-(1-t)\log(1-t)$, $h(0)=h(1)=0$.
--
--   Both exponents are negative at rate $1/2$ and cutoff close to $n$, which is what yields a rate below half.
--
--   **Formalization Note** $h$ is Mathlib's `Real.binEntropy`; since `Real.binEntropy 0 = 0`, `Hexp c 0` is already the continuous extension of $H$ to $\varepsilon=0$.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 9, p.20 (PDF 22); §6.2, p.31 (PDF 33); Lemma 15, p.30 (PDF 32); Proposition 4, p.31 (PDF 33); §2 preamble, p.10

import Mathlib

namespace ShamirLeak

/-- The decay constant `η_Q = min{(Q − 1)/2, cos²(π/(8Q))}` of Lemma 9 (p.20 (PDF p.22)); `η₂ = 1/2`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 9, p.20 (PDF p.22). -/
noncomputable def etaQ (Q : ℕ) : ℝ :=
  min (((Q : ℝ) - 1) / 2) (Real.cos (Real.pi / (8 * Q)) ^ 2)

/-- `κ₀ = (3/4)^{1/8}` (§6.2, p.31 (PDF p.33)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §6.2, p.31. -/
noncomputable def kappa0 : ℝ := (3 / 4 : ℝ) ^ ((1 : ℝ) / 8)

/-- `β₀ = (log κ₀)²/64` (§6.2, p.31 (PDF p.33)), natural logarithm.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §6.2, p.31. -/
noncomputable def beta0 : ℝ := Real.log kappa0 ^ 2 / 64

/-- The small-support exponent of Lemma 15 (p.30 (PDF p.32)):
`G(c, ζ, ε) = (1 − 2c + ζ) log 2 + log (1/(2(c − ζ))) − ε²/2`, natural logarithms.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 15, p.30. -/
noncomputable def Gexp (c ζ ε : ℝ) : ℝ :=
  (1 - 2 * c + ζ) * Real.log 2 + Real.log (1 / (2 * (c - ζ))) - ε ^ 2 / 2

/-- The large-support exponent of Proposition 4 (p.31 (PDF p.33)):
`H(c, ε) = h(ε) + max{((3c − 1)/2) log κ₀ + √β₀, (1 − 2c)(log 2 + 1/2) − β₀/2}`.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Proposition 4, p.31.

**Formalization Note.** `h` is the binary entropy with natural logarithms and `h(0) = h(1) = 0`
(§2, p.10), which is Mathlib's `Real.binEntropy`. Because `Real.binEntropy 0 = 0`, the formula
is already its continuous extension to `ε = 0`. -/
noncomputable def Hexp (c ε : ℝ) : ℝ :=
  Real.binEntropy ε + max ((3 * c - 1) / 2 * Real.log kappa0 + Real.sqrt beta0)
    ((1 - 2 * c) * (Real.log 2 + 1 / 2) - beta0 / 2)

end ShamirLeak


