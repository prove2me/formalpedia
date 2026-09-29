-- Prove2me | Definitions.Def_NumberField_BrauerLocalInvariantPresentation
-- name    : NumberField_BrauerLocalInvariantPresentation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/744a2002-ce76-50a2-9a9e-2c48ec19f490
-- title:
--   Brauer local invariant at a place via a presenting layer
-- statement:
--   For a natural number $p$, a finite set $S$ of rational primes, a number field $L\subset\overline{\mathbb{Q}}$ (an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$), a class $a$ in the submodule of elements annihilated by some power of $p$ inside `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)` — the level-$S$ second cohomology of $\Gamma_L=$ `L.fixingSubgroup` acting on the group of units of $\overline{\mathbb{Q}}$ that are, together with all their $\Gamma_L$-translates, integral and invertible at every valuation subring above a prime outside $S$ and contained in some subfield unramified outside $S$ — a prime $v$ of $\mathcal{O}_L$ lying above some prime of $S$, and $t\in\mathbb{Q}/\mathbb{Z}$ (realised as `AddCircle (1 : ℚ)`), the predicate `HasBrauerLocalInvAt` asserts the existence of a presentation of $a$ through a finite layer for which $t$ is the local invariant at $v$. Explicitly, it asserts the existence of: an intermediate field $F\supseteq L$, finite and normal over $\mathbb{Q}$, with $F/L$ Galois and $F$ unramified outside $S$ (every inertia subgroup at a prime outside $S$ lies in `F.fixingSubgroup`); a homomorphism $\iota$ from $\mathrm{Gal}(F/L)$ to $\Gamma_L/(\Gamma_F\cap\Gamma_L)$ splitting the restriction map `levelGal`; a bijective morphism $\varphi$ of representations from the $\Gamma_F$-invariants of the maximal $S$-units, restricted along $\iota$, to the $S$-unit representation of $F$ for the primes over $S$, compatible with the underlying elements of $\overline{\mathbb{Q}}$; an idèle Galois descent datum $D$ for $F/L$, a multiplicative action of $\mathrm{Gal}(F/L)$ on the units of the adele ring of $F$ agreeing with $D$, and a morphism $j$ given by the diagonal embedding of $F^\times$ into the idèles; and a $2$-cocycle $f$ of $\Gamma_L/(\Gamma_F\cap\Gamma_L)$ with values in the $\Gamma_F$-invariants whose inflation into the level-$S$ $H^2$ is $a$ — such that the image of $[f]$ under $\iota$ and under $\varphi$ followed by $j$ satisfies [`NumberField.IdeleLocalInv.HasLocalInv`](../def/NumberField_IdeleLocalInvariant.html#L14) at $v$ with value $t$, i.e. after localising at some prime $w$ of $F$ above $v$ the class becomes $n$ times a local fundamental class of the decomposition group and $t$ is the class of $n/\#D_w$ in $\mathbb{Q}/\mathbb{Z}$. The definition is thus a predicate on classes, quantifying existentially over all the presenting data.
--
--   **Relation to Mathlib.** Mathlib supplies the group cohomology apparatus used here (`cocycles₂`, `H2π`, `groupCohomology.map`), adele rings, height-one spectra and `AddCircle`; the level-$S$ continuous $H^2$, the representation on maximal $S$-units, the idèle Galois descent datum and the local-invariant predicate `HasLocalInv` are the project's own notions.
--
--   **Where it is used.** The predicate is the existential form of the data needed to read off a local invariant of a $p$-primary class in the $S$-Brauer group of $L$ through a finite Galois layer; it is the basis for stating that such invariants exist, are independent of the chosen layer and cocycle, and are additive. These invariants supply the class field theory input to the cohomological computations (Poitou–Tate duality, Selmer and class-group estimates) used in the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_BrauerLocalInvariantPresentation.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

namespace NumberField.LevelArith

def HasBrauerLocalInvAt (p : ℕ) (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))))
    (v : ↥(LevelArith.placesOverPrimes ↥L (S : Set Nat.Primes))) (t : AddCircle (1 : ℚ)) : Prop :=
  ∃
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : FiniteDimensional ℚ ↥F) (_ : Normal ℚ ↥F)
    (_ : IsGalois ↥L ↥(levelField L F hLF)) (hF : F.IsUnramifiedOutside S)

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (_ : Function.Bijective φ.hom)
    (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    (_ : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y)
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (_ : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (_ : (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) =
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f)),
    NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v.1 t

end NumberField.LevelArith


