-- Prove2me | Definitions.Def_ModularCurve_LevelOneGlueData
-- name    : ModularCurve_LevelOneGlueData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/98d211d9-86fc-540d-b3e7-bfde070dc814
-- title:
--   Level-one gluing data for good divisors on X0​(q)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with a ring homomorphism $\mathrm{red}\colon A\to k$, modular polynomial data `data` for $q$ with its Kronecker congruence `hKr`, integrality hypotheses $h\alpha,h\beta$ for the two degeneracy maps between levels $1$ and $1\cdot q$, and a place specialisation $P$ (the project's structure `PlaceSpecialization` at level $N=1$), whose component `P.sp` sends places of the level-one modular function field over $\overline{\mathbb Q}$ to places of `modularFunctionFieldC k 1`. For a place $W$ of the level-$(1\cdot q)$ function field over $\overline{\mathbb Q}$, `redFst W` is $P.\mathrm{sp}$ applied to the restriction of $W$ along `heckeAlphaBar` (the inclusion of the level-one field), and `redSnd W` is $P.\mathrm{sp}$ applied to the restriction along `heckeBetaBar` (the map induced by the substitution $q\mapsto q^{\,\ell}$ on Laurent expansions). Writing $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr`, the map on places induced by the $q$-power Frobenius endomorphism of `modularFunctionFieldC k 1`, the predicate `IsStrictTypeOne W` asserts $\varphi(\mathrm{redFst}\,W)=\mathrm{redSnd}\,W$ and $\varphi^2(\mathrm{redFst}\,W)\ne \mathrm{redFst}\,W$, and `IsStrictTypeTwo W` asserts $\mathrm{redFst}\,W=\varphi(\mathrm{redSnd}\,W)$ and $\varphi^2(\mathrm{redSnd}\,W)\ne\mathrm{redSnd}\,W$. A divisor is a good divisor when every place in its support satisfies one of these two conditions; `fstPart` and `sndPart` are the restrictions of a divisor (as a finitely supported function) to the places of strict type one, resp. two, and `branchDegrees` records the pair of their degrees.
--
--   For a finite set $S$ of pairs of places of `modularFunctionFieldC k 1`, `levelOneGlueData S D` is the element of the project's type `GluingData` given by the triple consisting of the pushforward of `fstPart D` along `redFst`, the pushforward of `sndPart D` along `redSnd`, and $0$ in the third (node-unit) component. Finally, `IsLevelOneGluedSpecialization S sp` is a specification on an additive map $sp$ from the inertia invariants `inertiaInvariants A (1 * q)` in $J_0(1\cdot q)$ to `GluedPic0 k (modularFunctionFieldC k 1) S`: for every degree-zero divisor $D$ whose class lies in those inertia invariants and every admissible gluing datum $x$, if $D$ is good and $x$ equals `levelOneGlueData S D`, then $sp$ of the class of $D$ equals `GluedPic0.mk S x`. Nothing is required of $sp$ on classes outside this range of data, so this is a constraint on $sp$ rather than a construction of it.
--
--   **Relation to Mathlib.** Divisors are Mathlib `Finsupp`s on places, and `Finsupp.filter`/`Finsupp.mapDomain` are used as such; the notions of place specialisation, of gluing data and glued degree-zero Picard group, and the strict-type conditions above have no Mathlib counterpart and are the project's own.
--
--   **Where it is used.** These definitions supply the explicit divisor-theoretic description of the reduction map at $q$ for $J_0(q)$, matching the Deligne–Rapoport picture of the special fibre of $X_0(q)$ as two copies of the $j$-line crossing at the supersingular points; the resulting glued specialisation is what feeds the `sp` component of the project's semistable specialisation data for $J_0(N q)$, used in the level-lowering step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneGlueData.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

def redFst (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Place k (modularFunctionFieldC k 1) :=
  P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)

def redSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Place k (modularFunctionFieldC k 1) :=
  P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ)

def IsStrictTypeOne (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W ∧
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
      ≠ P.redFst W

def IsStrictTypeTwo (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) ∧
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W))
      ≠ P.redSnd W

def IsGoodDivisor (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ W ∈ D.support, P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W

open Classical in

def fstPart (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) :=
  D.filter P.IsStrictTypeOne

open Classical in

def sndPart (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) :=
  D.filter P.IsStrictTypeTwo

def branchDegrees (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : ℤ × ℤ :=
  (Divisor.degree (P.fstPart D), Divisor.degree (P.sndPart D))

def levelOneGlueData
    (S : Finset (Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    GluingData k (modularFunctionFieldC k 1) S :=
  (Finsupp.mapDomain P.redFst (P.fstPart D), Finsupp.mapDomain P.redSnd (P.sndPart D), 0)

def IsLevelOneGluedSpecialization
    (S : Finset (Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)))
    (sp : ↥(inertiaInvariants A (1 * q)) →+ GluedPic0 k (modularFunctionFieldC k 1) S) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (1 * q))
    (x : ↥(GluingData.admissible S)),
    P.IsGoodDivisor (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) →
    (x : GluingData k (modularFunctionFieldC k 1) S) = P.levelOneGlueData S D →
      sp ⟨Pic0.mk D, hH⟩ = GluedPic0.mk S x

end PlaceSpecialization

end ModularCurve

end


