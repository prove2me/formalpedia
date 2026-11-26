-- Prove2me | Definitions.Def_Arxiv2308_14427_Basic
-- name    : Arxiv2308_14427_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T13:11:42.312307+00:00
-- url     : https://prove2.me/theorems/02063177-02bf-424d-aff2-92ae6fe342e9
-- title:
--   Sampled baseband signals, discrete convolution and the PSF restoration filter
-- statement:
--   Objects of Section II and Section II.A of Shen, Lin, Li and Li (2023).
--
--   1. **Sample grid and signals.** Beamformed images are sampled on the grid $\mathbb{Z}\times\mathbb{Z}$ of (axial, lateral) sample positions. A signal is a complex-valued function $f:\mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$ that is nonzero at only finitely many samples. The tissue scatterer distribution $S$, the point spread functions $\mathrm{PSF}_{\mathrm{aberrated}}$ and $\mathrm{PSF}_{\mathrm{ideal}}$, the restoration filter $K$ and the baseband (IQ) data $R$ are all signals.
--   2. **Convolution.** For signals $f,g$,
--   $$(f\ast g)(x)=\sum_{a+b=x}f(a)\,g(b),\qquad x\in\mathbb{Z}\times\mathbb{Z},$$
--   a finite sum.
--   3. **Restoration filter (eq. 1).** $K$ is a restoration (reshaping) filter for $\mathrm{PSF}_{\mathrm{aberrated}}$ and $\mathrm{PSF}_{\mathrm{ideal}}$ if $\mathrm{PSF}_{\mathrm{ideal}}=\mathrm{PSF}_{\mathrm{aberrated}}\ast K$.
--   4. **Aberration-free data (eq. 3).** $R_{\mathrm{ideal}}=S\ast\mathrm{PSF}_{\mathrm{ideal}}$.
--
--   **Formalization Note** The paper does not say whether its convolution is continuous or discrete. The definitions use the discrete convolution of finitely supported sampled signals, which matches the finite arrays of beamformed baseband data, PSF patches and digital filters the method works with. Signals are Mathlib's additive monoid algebra $\mathbb{C}[\mathbb{Z}\times\mathbb{Z}]$, whose product is this convolution.
-- source:
--   Shen, Lin, Li and Li, Phase Aberration Correction with Adaptive Coherence-Weighted Point Spread Function Restoration Filtering Technique, arXiv:2308.14427v1 (2023), Section II (locally linear space-invariant model) and Section II.A, eq. (1) (PDF p. 1) and eqs. (2)-(3) (PDF p. 2)

import Mathlib

/-!
Shen, Lin, Li and Li, *Phase Aberration Correction with Adaptive Coherence-Weighted Point Spread
Function Restoration Filtering Technique*, arXiv:2308.14427v1 (2023): the sampled baseband
signals, the convolution operator and the PSF restoration filter of Section II and
Section II.A, eqs. (1)-(3).
-/

noncomputable section

namespace Arxiv2308_14427

/-- Section II: the grid of sample positions of a beamformed image, indexed by
(axial sample, lateral sample) in `ℤ × ℤ`. -/
abbrev SampleGrid := ℤ × ℤ

/-- Section II: a sampled baseband (IQ) signal on the sample grid, complex-valued and nonzero
at only finitely many samples. Scatterer distributions `S`, point spread functions, the filter
`K` and the beamformed data `R` are all signals. -/
abbrev Signal := AddMonoidAlgebra ℂ SampleGrid

/-- Section II.A, the operator `∗` of eqs. (1)-(6): the discrete convolution
`(f ∗ g).coeff x = ∑_{a + b = x} f.coeff a * g.coeff b` of two signals (Mathlib's product in
the additive monoid algebra, see `AddMonoidAlgebra.coeff_mul`). -/
def conv (f g : Signal) : Signal := f * g

/-- Section II.A, eq. (1), PDF p. 1: `K` is a restoration (reshaping) filter for the
phase-aberrated PSF `psfAb` and the ideal aberration-free PSF `psfId`, that is
`PSF_ideal = PSF_aberrated ∗ K`. -/
def IsRestorationFilter (psfAb psfId K : Signal) : Prop := psfId = conv psfAb K

/-- Section II.A, eq. (3), PDF p. 2: the aberration-free baseband data
`R_ideal = S ∗ PSF_ideal` of the scatterer distribution `S`. -/
def idealData (S psfId : Signal) : Signal := conv S psfId

end Arxiv2308_14427


