-- Prove2me | Definitions.Def_NumberField_BrauerLocalInvariantChar
-- name    : NumberField_BrauerLocalInvariantChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/4344c271-82ef-5fb4-a9b0-acecfd3338d7
-- title:
--   Characterising local invariants on S-ramified H2 of S-units
-- statement:
--   Fix a natural number $p$, a finite set $S$ of rational primes and a number field $L\subset\overline{\mathbb{Q}}$ (an intermediate field of $\mathbb{Q}\subset\overline{\mathbb{Q}}$, finite over $\mathbb{Q}$). The module defines a predicate on a candidate invariant map, rather than constructing one. Its source is the $p$-primary part (the submodule annihilated by some power of $p$, `Submodule.torsion'` for the powers of $p$) of `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)`: here `sUnitsMaxRep S L` is the $\mathbb{Z}$-module of units $x$ of $\overline{\mathbb{Q}}$ all of whose $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$-translates lie in some subfield unramified outside $S$ and are units at every valuation subring over a prime $q\notin S$, with its $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$-action, and `continuousH2Sr` is the quotient of the $2$-cocycles that factor through a level unramified outside $S$ by the coboundaries of such level $1$-cochains. Its target is the functions from the finite places of $L$ lying over $S$ (height-one primes of $\mathcal{O}_L$ containing some $p\in S$) to $\mathbb{Q}/\mathbb{Z}$, realised as `AddCircle (1 : ℚ)`.
--
--   For a $\mathbb{Z}$-linear map `inv` between these, `IsBrauerLocalInv p S L inv` asserts the following for every choice of data: a finite layer $F\supseteq L$, normal over $\mathbb{Q}$ and unramified outside $S$ in the sense that inertia at every prime $q\notin S$ fixes $F$, with $F/L$ Galois; a homomorphism $\iota$ from $\mathrm{Gal}(F/L)$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/L)/\mathrm{Gal}(\overline{\mathbb{Q}}/F)$ compatible with the restriction map `levelGal`; a bijective morphism $\varphi$ identifying the $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$-invariants of the above module with the $S$-units of $F$, compatibly with the underlying elements of $\overline{\mathbb{Q}}$; an idèlic Galois descent datum $D$ for $\mathcal{O}_F$ whose unit action agrees with the ambient action, and a morphism $j$ realising the principal-idèle embedding on values; a $2$-cocycle $f$ of $\mathrm{Gal}(F/L)$ in the invariants whose inflation to $S$-ramified $H^2$ over $L$ is a given $p$-primary class $a$; and a place $v$ over $S$ together with $t\in\mathbb{Q}/\mathbb{Z}$. The conclusion is that whenever [`NumberField.IdeleLocalInv.HasLocalInv`](../def/NumberField_IdeleLocalInvariant.html#L14) holds for the image of the class of $f$ in $H^2(\mathrm{Gal}(F/L),\mathbb{A}_F^\times)$ under $\varphi$ followed by $j$, at the place $v$ and the value $t$ — that is, whenever the restriction of that class to a decomposition group at some $w\mid v$ is $n$ times a local fundamental class and $t=n/|D_w|$ — one has $\mathrm{inv}(a)(v)=t$.
--
--   **Relation to Mathlib.** Mathlib has no $S$-ramified (level-constant) cohomology of absolute Galois groups, no module of $S$-units of the maximal extension unramified outside $S$, and no Brauer local invariant maps; these, together with `IdeleGaloisDescent` and `HasLocalInv`, are the project's own notions built on Mathlib's `groupCohomology`, `Rep`, adèle rings and `AddCircle`.
--
--   **Where it is used.** The predicate isolates the local invariants $\mathrm{inv}_v\colon \mathrm{Br}(L_v)\to\mathbb{Q}/\mathbb{Z}$ of global class field theory, normalised so that a local fundamental class for $F_w/L_v$ has invariant $1/[F_w:L_v]$, on the $p$-primary part of $H^2$ of the $S$-units. Existence, injectivity (the Hasse principle), the reciprocity law and naturality are formulated as separate statements about maps satisfying it, and these feed the class-field-theoretic input to the Galois-cohomological computations with $S$-units and class groups used in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_BrauerLocalInvariantChar.lean

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

def IsBrauerLocalInv (p : ℕ) (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
      →ₗ[ℤ] (↥(LevelArith.placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))) : Prop :=
  ∀
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (_ : Function.Bijective φ.hom)
    (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y)
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (_ : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))))
    (_ : (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) =
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f))

    (v : ↥(LevelArith.placesOverPrimes ↥L (S : Set Nat.Primes))) (t : AddCircle (1 : ℚ)),
    NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v.1 t →
    inv a v = t

end NumberField.LevelArith


