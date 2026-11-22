-- Prove2me | Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
-- name    : MasulloGRH_SLocalTamagawaMeasures
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:49:00.48018+00:00
-- url     : https://prove2.me/theorems/968a4f0e-99e3-4e18-891d-9dc58f631b03
-- title:
--   Definitions A.3.2.2 and A.3.4.1 — the local multiplicative Tamagawa measures $\mu_v$ on $F_v^\times$ and the $S$-local Tamagawa measures $\nu_S$, $\mu_S$
-- statement:
--   **Local multiplicative Tamagawa measures and $S$-local Tamagawa measures** (Definition A.3.2.2, Lemma A.3.2.3 and Definition A.3.4.1(1)–(2) of the source).
--
--   Let $F$ be a number field. For a place $v$ of $F$ let $F_v$ be the completion of $F$ at $v$ and $|\cdot|_v$ the normalized absolute value on $F_v$: the usual absolute value if $F_v\simeq\mathbb R$, its square if $F_v\simeq\mathbb C$, and the absolute value with $|\pi_v|_v=q_v^{-1}$ if $v$ is finite, where $\pi_v$ is a uniformizer of the ring of integers $\mathcal O_{F_v}$ and $q_v=N(\mathfrak p_v)$ is the cardinality of the residue field. The **local additive Tamagawa measure** $\nu_v$ on $F_v$ (Definition A.3.1.2 of the source) is: Lebesgue measure $dx$ if $F_v\simeq\mathbb R$; the measure $|dz\wedge d\bar z|=2\,dx\,dy$ if $F_v\simeq\mathbb C$; and, if $v$ is a finite place above the prime $p$, the Haar measure on $F_v$ with
--   $$\nu_v(\mathcal O_{F_v})=N(\mathfrak d_v)^{-1/2},\qquad N(\mathfrak d_v)=q_v^{d_v},$$
--   where $\mathfrak d_v=\mathfrak d_{F_v/\mathbb Q_p}$ is the local different and $d_v$ is the exponent of the prime $\mathfrak p_v$ in the different $\mathfrak d_{F/\mathbb Q}$ of $F$ (so $d_v=0$ unless $v$ is ramified over $\mathbb Q$, and $\prod_vN(\mathfrak d_v)=|d_F|$ is the absolute value of the discriminant of $F$).
--
--   Let $S$ be a finite set of places of $F$ containing all archimedean places and $S_f\subset S$ the set of its finite places. Write
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v,\qquad \mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times,\qquad |g|_{F,S}=\prod_{v\in S}|g_v|_v$$
--   for the ring of $S$-adeles (with the product topology), the group of $S$-ideles and the $S$-idelic norm, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   for the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$ as a discrete cocompact subgroup.
--
--   The file defines the following Haar measures.
--
--   1. `infiniteLocalMulTamagawa F w` — the **local multiplicative Tamagawa measure** $\mu_w=|\cdot|_w^{-1}\nu_w$ on $F_w^\times$ at an archimedean place $w$ (Definition A.3.2.2(1)):
--   $$\mu_w(B)=\int_B\frac{d\nu_w(x)}{|x|_w}\qquad(B\subset F_w^\times\ \text{Borel}),$$
--   that is $dx/|x|$ on $\mathbb R^\times$ and $2\,dx\,dy/|z|^2$ on $\mathbb C^\times$.
--
--   2. `finiteLocalMulTamagawa F v` — the **local multiplicative Tamagawa measure** $\mu_v$ on $F_v^\times$ at a finite place $v$ (Definition A.3.2.2(2)), given by the formula (A.3.2.3) of Lemma A.3.2.3:
--   $$\mu_v(B)=\frac{q_v}{q_v-1}\int_B\frac{d\nu_v(x)}{|x|_v}\qquad(B\subset F_v^\times\ \text{Borel}).$$
--   It is the Haar measure on $F_v^\times$ normalized by $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$, eq. (A.3.2.2).
--
--   3. `infiniteAdditiveTamagawa F` — the product measure $\nu_\infty=\bigotimes_{w\mid\infty}\nu_w$ on $\mathbb A_{F,S_\infty}=\prod_{w\mid\infty}F_w=F\otimes_{\mathbb Q}\mathbb R$.
--
--   4. `sAdditiveTamagawa F Sf` — the **$S$-local additive Tamagawa measure** (Definition A.3.4.1(1), eq. (A.3.4.1))
--   $$\nu_S=\bigotimes_{v\in S}\nu_v\quad\text{on }\mathbb A_{F,S}.$$
--
--   5. `sMultiplicativeTamagawa F Sf` — the **$S$-local multiplicative Tamagawa measure** (Definition A.3.4.1(2), eq. (A.3.4.2))
--   $$\mu_S=\bigotimes_{v\in S}\mu_v\quad\text{on }\mathrm{GL}_1(\mathbb A_{F,S}),\qquad d\mu_S(g)=\Big(\prod_{v\in S_f}\frac{q_v}{q_v-1}\Big)\frac{d\nu_S(g)}{|g|_{F,S}} .$$
--
--   These are the measures with respect to which the $S$-local Fourier transform, the $S$-local $\theta$-functions and the $S$-local zeta integrals of Chapters 2–3 of the source are formed; $\nu_S$ is self-dual for the standard additive character, and the global Tamagawa measures of $\mathbb A_F$ and $\mathrm{GL}_1(\mathbb A_F)$ restrict to $\nu_S\otimes\bigotimes_{v\notin S}\nu_v$ and $\mu_S\otimes\bigotimes_{v\notin S}\mu_v$ on the adeles, respectively ideles, that are integral, respectively units, outside $S$ (Lemmas A.3.1.3 and A.3.2.4).
--
--   **Formalization Note.** As in `MasulloGRH.SAdeleRing`, the set $S$ is represented by the finite set `Sf` of its finite places; $\mathbb A_{F,S}$ is `InfiniteAdeleRing F × ((v : Sf) → v.adicCompletion F)` and $\mathrm{GL}_1(\mathbb A_{F,S})$ is its unit group. The local additive measures $\nu_v$ are the platform definitions `RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure` and `RiemannMasullo.finiteLocalAdditiveTamagawaMeasure`; $N(\mathfrak d_v)$ is `Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))`. Measurable structures are provided as scoped instances of the namespace `MasulloGRH`: the Borel $\sigma$-algebra on every $F_v$, every $F_v^\times$ and on $\mathrm{GL}_1(\mathbb A_{F,S})$, and the product $\sigma$-algebra on $\mathbb A_{F,S_\infty}$ and $\mathbb A_{F,S}$ (which is the Borel $\sigma$-algebra, the factors being second countable). The measures on unit groups are `Measure.comap Units.val` of `withDensity` measures (the unit group is an open subset of the ring). At a finite place $\mu_v$ is defined by the formula (A.3.2.3) rather than by the normalization (A.3.2.2); the equivalence of the two is Lemma A.3.2.3 (`MasulloGRH.finiteLocalMulTamagawa_isHaarMeasure_and_units`). Likewise $\mu_S$ is defined by its density with respect to $\nu_S$; that it is the product of the $\mu_v$ is `MasulloGRH.sMultiplicativeTamagawa_isHaarMeasure_and_rectangle`. The measures of Definition A.3.4.1(3) on the norm-one $S$-ideles and on the quotients by $\mathcal O_{F,S}^\times$ are not part of this file.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 560, Definition A.3.2.2 and Lemma A.3.2.3, eqs. (A.3.2.2)–(A.3.2.3); p. 561, Definition A.3.4.1(1)–(2), eqs. (A.3.4.1)–(A.3.4.2)

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles
import Definitions.Def_RiemannMasullo_LocalAdditiveTamagawaMeasures

/-!
# Local multiplicative and `S`-local Tamagawa measures

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.3:
Definition A.3.2.2 and Lemma A.3.2.3, eqs. (A.3.2.2)–(A.3.2.3) (p. 560), and
Definition A.3.4.1(1)–(2), eqs. (A.3.4.1)–(A.3.4.2) (p. 561).

The local additive Tamagawa measures `ν_v` of Definition A.3.1.2 are the platform definitions
`RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure` and
`RiemannMasullo.finiteLocalAdditiveTamagawaMeasure`.

As in `MasulloGRH.SAdeleRing`, a finite set `S` of places containing all archimedean places is
represented by the finite set `Sf` of its finite places.

Measurable structures.  Every completion `F_v`, every unit group `F_vˣ` and the `S`-idele group
`GL₁(𝔸_{F,S})` carry their Borel σ-algebras.  The `S`-adele ring
`𝔸_{F,S} = ∏_{v ∈ S} F_v` carries the product of the Borel σ-algebras of its factors; since the
factors are second countable this is the Borel σ-algebra of `𝔸_{F,S}`.
-/

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The Borel σ-algebra of the completion `F_w` at an infinite place. -/
scoped instance tamagawaInfiniteCompletionMeasurableSpace (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _

scoped instance tamagawaInfiniteCompletionBorelSpace (w : InfinitePlace F) :
    BorelSpace w.Completion := ⟨rfl⟩

/-- The Borel σ-algebra of the completion `F_v` at a finite place. -/
scoped instance tamagawaAdicCompletionMeasurableSpace (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

scoped instance tamagawaAdicCompletionBorelSpace (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The Borel σ-algebra of the unit group `F_wˣ` at an infinite place. -/
scoped instance tamagawaInfiniteCompletionUnitsMeasurableSpace (w : InfinitePlace F) :
    MeasurableSpace w.Completionˣ := borel _

scoped instance tamagawaInfiniteCompletionUnitsBorelSpace (w : InfinitePlace F) :
    BorelSpace w.Completionˣ := ⟨rfl⟩

/-- The Borel σ-algebra of the unit group `F_vˣ` at a finite place. -/
scoped instance tamagawaAdicCompletionUnitsMeasurableSpace (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

scoped instance tamagawaAdicCompletionUnitsBorelSpace (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩

/-- The product σ-algebra on `𝔸_{F,S_∞} = ∏_{w ∣ ∞} F_w`. -/
scoped instance tamagawaInfiniteAdeleMeasurableSpace : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))

/-- The Borel σ-algebra of the `S`-idele group `GL₁(𝔸_{F,S})`. -/
scoped instance tamagawaSIdeleMeasurableSpace (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (SIdeleGroup F Sf) := borel _

scoped instance tamagawaSIdeleBorelSpace (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    BorelSpace (SIdeleGroup F Sf) := ⟨rfl⟩

/-- Definition A.3.2.2(1): the local multiplicative Tamagawa measure `μ_w = |·|_w⁻¹ ν_w` on
`F_wˣ` at an infinite place `w`, where `ν_w` is the local additive Tamagawa measure and
`|x|_w = ‖x‖ ^ mult w` is the normalized absolute value (the usual absolute value at a real
place, its square at a complex place):  `μ_w(B) = ∫_B dν_w(x) / |x|_w` for Borel `B ⊆ F_wˣ`. -/
def infiniteLocalMulTamagawa (w : InfinitePlace F) : Measure w.Completionˣ :=
  ((RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).withDensity
    (fun x => ((‖x‖₊ : ℝ≥0∞) ^ w.mult)⁻¹)).comap Units.val

/-- Definition A.3.2.2(2), in the form of Lemma A.3.2.3: the local multiplicative Tamagawa measure
`μ_v = q_v / (q_v - 1) · |·|_v⁻¹ ν_v` on `F_vˣ` at a finite place `v`, where `ν_v` is the local
additive Tamagawa measure, `q_v = N(𝔭_v)` is the cardinality of the residue field and `|·|_v` is
the normalized absolute value (`|π_v|_v = q_v⁻¹`).  It is the Haar measure on `F_vˣ` with
`μ_v(𝒪_vˣ) = ν_v(𝒪_v) = N(𝔡_v)^{-1/2}`. -/
def finiteLocalMulTamagawa (v : HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletion F)ˣ :=
  ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1)) •
    ((RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v).withDensity
      (fun x => (‖x‖₊ : ℝ≥0∞)⁻¹)).comap Units.val

/-- The archimedean additive Tamagawa measure `ν_∞ = ⊗_{w ∣ ∞} ν_w` on
`𝔸_{F,S_∞} = ∏_{w ∣ ∞} F_w`, the product of the local additive Tamagawa measures at the infinite
places (Lebesgue measure at a real place, twice Lebesgue measure at a complex place). -/
def infiniteAdditiveTamagawa : Measure (InfiniteAdeleRing F) :=
  Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)

/-- Definition A.3.4.1(1): the `S`-local additive Tamagawa measure `ν_S = ⊗_{v ∈ S} ν_v` on
`𝔸_{F,S} = ∏_{w ∣ ∞} F_w × ∏_{v ∈ S_f} F_v`, the product of the local additive Tamagawa
measures. -/
def sAdditiveTamagawa (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Measure (SAdeleRing F Sf) :=
  (infiniteAdditiveTamagawa F).prod
    (Measure.pi fun v : Sf =>
      RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F)))

/-- Definition A.3.4.1(2): the `S`-local multiplicative Tamagawa measure `μ_S = ⊗_{v ∈ S} μ_v` on
`GL₁(𝔸_{F,S}) = ∏_{v ∈ S} F_vˣ`, the product of the local multiplicative Tamagawa measures.  It
is given by the density
`dμ_S(g) = (∏_{v ∈ S_f} q_v / (q_v - 1)) · |g|_{F,S}⁻¹ dν_S(g)`,
where `|g|_{F,S} = ∏_{v ∈ S} |g_v|_v` is the `S`-idelic norm. -/
def sMultiplicativeTamagawa (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Measure (SIdeleGroup F Sf) :=
  (∏ v ∈ Sf, ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1))) •
    ((sAdditiveTamagawa F Sf).withDensity
      (fun x => ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
        ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹)).comap Units.val

end

end MasulloGRH


