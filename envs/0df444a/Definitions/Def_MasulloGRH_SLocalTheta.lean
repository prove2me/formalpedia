-- Prove2me | Definitions.Def_MasulloGRH_SLocalTheta
-- name    : MasulloGRH_SLocalTheta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:27:41.536097+00:00
-- url     : https://prove2.me/theorems/3ad4bb73-037c-46f8-be3c-3f7ffca2ecb4
-- title:
--   $\mathcal S(\mathbb A_{F,S})$ and the $S$-local adelic $\theta$-function $\Phi_{F,S}(f)$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing the Archimedean places.
--
--   1. $\mathcal S(\mathbb A_{F,S})$ is the Schwartz–Bruhat space of the additive group of the $S$-adele ring $\mathbb A_{F,S}=\prod_{v\in S}F_v$.
--   2. The **$S$-local adelic $\theta$-function** of $f\in\mathcal S(\mathbb A_{F,S})$ is
--   $$\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times}f(\xi g),\qquad g\in\mathrm{GL}_1(\mathbb A_{F,S}),$$
--   the sum of $f$ over the orbit of the $S$-idele $g$ under the group of $S$-units.
--
--   $\Phi_{F,S}(f)$ is invariant under $\mathcal O_{F,S}^\times$, hence a function on $J_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S})/\mathcal O_{F,S}^\times$. These functions are the $S$-local counterparts of the global $\theta$-functions $\Phi_F(f)$ on $C_F$.
--
--   **Formalization Note** The set $S$ is represented by its finite part $S_f$. The sum is an unconditional sum over the $S$-units.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.3, Definition 2.3.1.1, eqs. (2.3.1.1)–(2.3.1.2), pp. 99–100

import Definitions.Def_MasulloGRH_AdelicTheta

/-!
# S-local adelic θ-functions

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Chapter 2, §2.3,
Definition 2.3.1.1, eqs. (2.3.1.1)–(2.3.1.2), pp. 99–100.
-/

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The Schwartz–Bruhat space `S(𝔸_{F,S})` of the additive group of the `S`-adele ring. -/
abbrev SAdelicSchwartz (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Type _ :=
  SchwartzBruhat (Multiplicative (SAdeleRing F Sf))

variable {F}

/-- The value `f(x)` of `f ∈ S(𝔸_{F,S})` at an `S`-adele `x`. -/
def SAdelicSchwartz.eval {Sf : Finset (HeightOneSpectrum (𝓞 F))} (f : SAdelicSchwartz F Sf)
    (x : SAdeleRing F Sf) : ℂ :=
  f.toFun (Multiplicative.ofAdd x)

/-- Definition 2.3.1.1: the `S`-local adelic θ-function
`Φ_{F,S}(f)(g) = ∑_{ξ ∈ 𝒪_{F,S}ˣ} f(ξ g)` of `f ∈ S(𝔸_{F,S})`, a function of the `S`-idele `g`. -/
def sLocalTheta {Sf : Finset (HeightOneSpectrum (𝓞 F))} (f : SAdelicSchwartz F Sf)
    (g : SIdeleGroup F Sf) : ℂ :=
  ∑' ξ : SUnits Sf, f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))

end

end MasulloGRH


