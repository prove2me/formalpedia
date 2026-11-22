-- Prove2me | Definitions.Def_MasulloGRH_SIntegerFundamentalDomain
-- name    : MasulloGRH_SIntegerFundamentalDomain
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:20:28.229937+00:00
-- url     : https://prove2.me/theorems/ce2a8bbd-00fe-4889-af65-7a7b59f09a02
-- title:
--   Definition A.2.4.1 — the $S$-adelic fundamental domain $D_{F,S}=D_{F,\infty}\times\prod_{v\in S_f}\mathcal O_{F_v}$ for the $S$-integers
-- statement:
--   **The $S$-adelic fundamental domain $D_{F,S}$** (Definition A.2.4.1, eq. (A.2.4.1) of the source).
--
--   Let $F$ be a number field of degree $d=[F:\mathbb Q]$, $S$ a finite set of places of $F$ containing all archimedean places, $S_f$ the set of finite places in $S$, and
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v=\mathbb A_{F,S_\infty}\times\prod_{v\in S_f}F_v$$
--   the ring of $S$-adeles, where $\mathbb A_{F,S_\infty}=\prod_{v\mid\infty}F_v=F\otimes_{\mathbb Q}\mathbb R$. Fix a $\mathbb Z$-basis $a_1,\dots,a_d$ of the ring of integers $\mathcal O_F$. The file defines `sIntegerFundamentalDomain`:
--   $$D_{F,S}=D_{F,\infty}\times\prod_{v\in S_f}\mathcal O_{F_v}\subset\mathbb A_{F,S},\qquad D_{F,\infty}=\Big\{\sum_{i=1}^{d}x_ia_i:\ 0\le x_i<1\Big\}\subset\mathbb A_{F,S_\infty},$$
--   the set of $S$-adeles whose archimedean component lies in the half-open parallelepiped spanned by the integral basis and whose component at every finite place of $S$ is a local integer.
--
--   $D_{F,S}$ is a fundamental domain for the additive action of the ring of $S$-integers $\mathcal O_{F,S}$ on $\mathbb A_{F,S}$ (Lemma A.2.4.2); it is the $S$-local analogue of the adelic fundamental domain $D_F=D_{F,\infty}\times\widehat{\mathcal O}_F$ for $F$ acting on $\mathbb A_F$ (Definition A.2.1.1), and for $S=S_\infty$ it is the fundamental parallelepiped of the lattice $\mathcal O_F\subset F\otimes_{\mathbb Q}\mathbb R$. Since $D_{F,S}$ is a measurable set of representatives for $\mathbb A_{F,S}/\mathcal O_{F,S}$, the normalization $\bar\nu_S(\mathbb A_{F,S}/\mathcal O_{F,S})=1$ of the Tamagawa measure $\nu_S$ on $\mathbb A_{F,S}$ (Definition A.3.1.1 of the source; $\bar\nu_S$ is the measure induced on the quotient by $\nu_S$ and the counting measure on $\mathcal O_{F,S}$) is equivalent to $\nu_S(D_{F,S})=1$. The source introduces this set in §A.2.4 as the $S$-local analogue of $D_F$ and does not use it again; it must not be confused with the different subset of $\mathbb A_{F,S}$ that the source also denotes $D_{F,S}$ in Chapters 1 and 8 (eq. (8.2.0.5), p. 385).
--
--   **Deviation from the source.** Definition A.2.4.1 refers to the formula (A.2.1.1) for $D_{F,\infty}$, which as printed sums over only $r_1+r_2$ basis vectors and bounds absolute values; that set is not a fundamental domain (for $F=\mathbb Q$ it is $(-1,1)$). The half-open parallelepiped $\{\sum_{i\le d}x_ia_i:0\le x_i<1\}$ of the whole integral basis is used instead; it is the set the source itself uses in the proof of Lemma A.2.4.2 ("$D_{F,\infty}$ is sent homeomorphically onto $[0,1)^{[F:\mathbb Q]}$") and in Example A.2.1.3.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places (prime ideals of $\mathcal O_F$), and $\mathbb A_{F,S}$ is the platform's `MasulloGRH.SAdeleRing F Sf = InfiniteAdeleRing F × ((v : Sf) → v.adicCompletion F)`. $D_{F,\infty}$ is the platform's `RiemannMasullo.infiniteAdeleFundamentalDomain F b` (Mathlib's `ZSpan.fundamentalDomain` of the image of the integral basis `b : Module.Basis ι ℤ (𝓞 F)` in the mixed space, pulled back to `InfiniteAdeleRing F`), and $\mathcal O_{F_v}$ is `v.adicCompletionIntegers F`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 554, Definition A.2.4.1, eq. (A.2.4.1) (with Definition A.2.1.1, p. 545, corrected as in the proof of Lemma A.2.4.2, p. 554)

import Mathlib
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
import Definitions.Def_MasulloGRH_SAdeles

/-!
# The `S`-adelic fundamental domain `D_{F,S}` for the `S`-integers

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.2.4,
Definition A.2.4.1, eq. (A.2.4.1) (p. 554), with the archimedean domain `D_{F,∞}` of
Definition A.2.1.1 (p. 545) in the corrected form used in the proof of Lemma A.2.4.2 (p. 554):
the half-open parallelepiped `{∑ᵢ xᵢ aᵢ : 0 ≤ xᵢ < 1}` spanned by the whole integral basis.

As in `MasulloGRH.SAdeleRing`, a finite set `S` of places containing all archimedean places is
represented by the finite set `Sf` of its finite places.
-/

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The `S`-adelic fundamental domain `D_{F,S} = D_{F,∞} × ∏_{v ∈ S_f} 𝒪_{F_v} ⊂ 𝔸_{F,S}`
(Definition A.2.4.1): the `S`-adeles whose archimedean component lies in the half-open
parallelepiped `D_{F,∞} = {∑ᵢ xᵢ aᵢ : 0 ≤ xᵢ < 1}` of the integral basis `b = (aᵢ)` of `𝒪_F`
(inside `𝔸_{F,S_∞} = F ⊗_ℚ ℝ`), and whose component at every finite place of `S` is a local
integer. -/
def sIntegerFundamentalDomain {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Set (SAdeleRing F Sf) :=
  {x | x.1 ∈ RiemannMasullo.infiniteAdeleFundamentalDomain F b ∧
       ∀ v : Sf, x.2 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}

end

end MasulloGRH


