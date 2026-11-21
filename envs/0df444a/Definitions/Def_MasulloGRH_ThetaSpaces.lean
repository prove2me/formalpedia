-- Prove2me | Definitions.Def_MasulloGRH_ThetaSpaces
-- name    : MasulloGRH_ThetaSpaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:30:50.585353+00:00
-- url     : https://prove2.me/theorems/a5af6edd-fff0-4105-bed7-be248d4c66ce
-- title:
--   The spaces of adelic $\theta$-functions $H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbb A_F))$ and $H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbb A_{F,S}))$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places containing the Archimedean places.
--
--   1. $\ker\Phi_F\subset\mathcal S(\mathbb A_F)$ is the space of the Schwartz–Bruhat functions $f$ whose $\theta$-function $\Phi_F(f)(g)=\sum_{\xi\in F^\times}f(\xi g)$ vanishes identically.
--   2. The **space of global adelic $\theta$-functions** is
--   $$H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbb A_F))=\mathcal S(\mathbb A_F)/\ker\Phi_F ,$$
--   with the quotient topology.
--   3. $\ker\Phi_{F,S}\subset\mathcal S(\mathbb A_{F,S})$ is the space of the $f$ whose $S$-local $\theta$-function $\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times}f(\xi g)$ vanishes identically.
--   4. The **space of $S$-local adelic $\theta$-functions** is
--   $$H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbb A_{F,S}))=\mathcal S(\mathbb A_{F,S})/\ker\Phi_{F,S},$$
--   with the quotient topology.
--
--   These quotients are identified with the spaces of functions $\Phi_F(f)$ on $C_F$ and $\Phi_{F,S}(f)$ on $J_{F,S}$. They are the spaces on which the draft builds Schauder bases and computes traces.
--
--   **Formalization Note** The kernels are defined as the linear spans of the sets of $f$ with vanishing $\theta$-function; these sets are subspaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 5, §5.1.1, Definition 5.1.1.1(3), eq. (5.1.1.3), p. 223

import Definitions.Def_MasulloGRH_SLocalTheta
import Definitions.Def_MasulloGRH_ZetaIntegrals

/-!
# The spaces of global and S-local adelic θ-functions

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Chapter 5, §5.1.1,
Definition 5.1.1.1(3), eq. (5.1.1.3), p. 223.
-/

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The kernel `ker Φ_F` of the global θ-function operator: the `f ∈ S(𝔸_F)` with
`∑_{ξ ∈ Fˣ} f(ξ g) = 0` for every idele `g`. -/
def adelicThetaKernel : Submodule ℂ (AdelicSchwartz F) :=
  Submodule.span ℂ {f | ∀ g : IdeleGroup F, adelicTheta f g = 0}

/-- The space of global adelic θ-functions `H_{0,cont}(Fˣ, S(𝔸_F)) = S(𝔸_F) / ker Φ_F` (5.1.1.3),
with the quotient topology. -/
abbrev GlobalThetaSpace : Type _ := AdelicSchwartz F ⧸ adelicThetaKernel F

variable {F}

/-- The kernel `ker Φ_{F,S}` of the `S`-local θ-function operator. -/
def sLocalThetaKernel (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Submodule ℂ (SAdelicSchwartz F Sf) :=
  Submodule.span ℂ {f | ∀ g : SIdeleGroup F Sf, sLocalTheta f g = 0}

/-- The space of `S`-local adelic θ-functions
`H_{0,cont}(𝒪_{F,S}ˣ, S(𝔸_{F,S})) = S(𝔸_{F,S}) / ker Φ_{F,S}` (5.1.1.3), with the quotient
topology. -/
abbrev SLocalThetaSpace (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Type _ :=
  SAdelicSchwartz F Sf ⧸ sLocalThetaKernel Sf

end

end MasulloGRH


