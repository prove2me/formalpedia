-- Prove2me | Definitions.Def_MasulloGRH_SAdeles
-- name    : MasulloGRH_SAdeles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:20:38.541156+00:00
-- url     : https://prove2.me/theorems/46bbdcc2-6b94-4a8a-b0af-1f07d7b5faa7
-- title:
--   $S$-adeles, $S$-ideles, $S$-integers and their class groups
-- statement:
--   These are the objects attached to a finite set of places of a number field.
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all Archimedean places; $S_f$ is the set of finite places in $S$.
--
--   1. The **$S$-adele ring** is $\mathbb A_{F,S}=\prod_{v\in S}F_v$ with the product topology.
--   2. The **$S$-idele group** is $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$, the group of units of $\mathbb A_{F,S}$.
--   3. The **diagonal embedding** $F\to\mathbb A_{F,S}$ sends $\xi$ to $(\xi)_{v\in S}$.
--   4. The **ring of $S$-integers** is $\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\text{ for all }v\notin S\}$, and $\mathcal O_{F,S}^\times$ is its group of units, the **$S$-units**.
--   5. $\iota_S(\mathcal O_{F,S})\subset\mathbb A_{F,S}$ and $\mathcal O_{F,S}^\times\subset\mathrm{GL}_1(\mathbb A_{F,S})$ are the images under the diagonal embedding.
--   6. $J_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S})/\mathcal O_{F,S}^\times$, with the quotient topology.
--   7. The **$S$-idelic norm** is $|g|_{F,S}=\prod_{v\in S}|g_v|_v$, with the normalized absolute values.
--   8. $\mathrm{GL}_1(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})$ is the set of ideles whose coordinates at all finite places outside $S$ are units.
--   9. The **$S$-idele class group** is $C_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v})/\mathcal O_{F,S}^\times$. It is represented by its image in $C_F$, the set of classes of the ideles of item 8.
--
--   The $S$-local objects are the setting of the draft's $S$-local $\theta$-functions and zeta functions; statements for $C_F$ are obtained from them by enlarging $S$.
--
--   **Formalization Note** The set $S$ is represented by $S_f$. In item 9 the group $C_{F,S}$ maps injectively onto an open subgroup of $C_F$, and the quotient topology of $C_{F,S}$ is the subspace topology of the image; only the image is defined.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.5, eqs. (A.1.5.1)–(A.1.5.8), pp. 543–544; §3.1.2, eq. (3.1.2.1), p. 120

import Definitions.Def_MasulloGRH_IdeleNorm

/-!
# S-adeles, S-ideles, S-integers and their class groups

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.1.5
(pp. 543–544), eqs. (A.1.5.1)–(A.1.5.8), and §3.1.2, eq. (3.1.2.1) (p. 120).

Throughout, `S` is a finite set of places of the number field `F` containing all Archimedean
places.  It is represented by the finite set `Sf` of its finite places.
-/

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The `S`-adele ring `𝔸_{F,S} = ∏_{v ∈ S} F_v` (A.1.5.1), with the product topology: the product
of the completions at all infinite places and at the finite places in `Sf`. -/
abbrev SAdeleRing (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Type _ :=
  InfiniteAdeleRing F × ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)

/-- The `S`-idele group `GL₁(𝔸_{F,S}) = ∏_{v ∈ S} F_vˣ` (A.1.5.2): the units of `𝔸_{F,S}`. -/
abbrev SIdeleGroup (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Type _ := (SAdeleRing F Sf)ˣ

variable {F}

/-- The diagonal embedding `F → 𝔸_{F,S}`. -/
def sDiagonal (Sf : Finset (HeightOneSpectrum (𝓞 F))) : F →+* SAdeleRing F Sf :=
  RingHom.prod (algebraMap F (InfiniteAdeleRing F))
    (RingHom.pi fun v : Sf => algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

/-- The ring of `S`-integers `𝒪_{F,S} = {ξ ∈ F : ξ ∈ 𝒪_{F_v} for all v ∉ S}`. -/
abbrev SIntegers (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Subalgebra (𝓞 F) F :=
  (Sf : Set (HeightOneSpectrum (𝓞 F))).integer F

/-- The group of `S`-units `𝒪_{F,S}ˣ`, as a subgroup of `Fˣ`. -/
abbrev SUnits (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (Sf : Set (HeightOneSpectrum (𝓞 F))).unit F

/-- The image of `𝒪_{F,S}` under the diagonal embedding `ι_S : 𝒪_{F,S} → 𝔸_{F,S}` (A.1.5.3). -/
def sIntegerLattice (Sf : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (SAdeleRing F Sf) :=
  ((SIntegers Sf).toSubring.toAddSubgroup).map (sDiagonal Sf).toAddMonoidHom

/-- The image of the `S`-units in the `S`-idele group under the diagonal embedding. -/
def sUnitLattice (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (SIdeleGroup F Sf) :=
  (SUnits Sf).map (Units.map (sDiagonal Sf).toMonoidHom)

/-- The quotient `J_{F,S} = GL₁(𝔸_{F,S}) / 𝒪_{F,S}ˣ` (3.1.2.1), with the quotient topology. -/
abbrev SIdeleQuotient (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Type _ :=
  SIdeleGroup F Sf ⧸ sUnitLattice Sf

/-- The `S`-idelic norm `|g|_{F,S} = ∏_{v ∈ S} |g_v|_v` (A.1.5.6), the product of the normalized
absolute values at the places of `S`. -/
def sIdeleNorm (Sf : Finset (HeightOneSpectrum (𝓞 F))) (g : SIdeleGroup F Sf) : ℝ :=
  (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) *
    ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖

/-- The set of ideles all of whose coordinates at the finite places outside `S` are units:
`GL₁(𝔸_{F,S} × ∏_{v ∉ S} 𝒪_{F_v})`, viewed inside `GL₁(𝔸_F)`. -/
def sIntegralIdeles (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Set (IdeleGroup F) :=
  {g | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1}

/-- The subset of the idele class group `C_F` consisting of the classes of the ideles in
`GL₁(𝔸_{F,S} × ∏_{v ∉ S} 𝒪_{F_v})`.  It is the image in `C_F` of the `S`-idele class group
`C_{F,S} = GL₁(𝔸_{F,S} × ∏_{v ∉ S} 𝒪_{F_v}) / 𝒪_{F,S}ˣ` (A.1.5.7), which maps injectively to
`C_F`. -/
def sIdeleClasses (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Set (IdeleClassGroup F) :=
  (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' sIntegralIdeles Sf

end

end MasulloGRH


