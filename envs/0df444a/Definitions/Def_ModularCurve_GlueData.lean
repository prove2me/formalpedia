-- Prove2me | Definitions.Def_ModularCurve_GlueData
-- name    : ModularCurve_GlueData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/0e580996-16cb-53bd-8bde-35eea2e6eef7
-- title:
--   Gluing data attached to places of the level-Nq curve
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $N$ a nonzero level, $k$ a field of characteristic $q$ with a ring homomorphism $\mathrm{red} : A \to k$, `data` a `ModularPolynomialData q` satisfying `KroneckerCongruence q data`, and $h\alpha$, $h\beta$ the integrality hypotheses for the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the level-$N$ into the level-$Nq$ Laurent-series function field over $\overline{\mathbb Q}$; $P$ is a `PlaceSpecialization` for these data, whose field `sp` carries places of `modularFunctionFieldBar N` to places of `modularFunctionFieldC k N`.
--
--   For a place $W$ of `modularFunctionFieldBar (N * q)`, `reduceFst` and `reduceSnd` are the images under `P.sp` of the restrictions of $W$ along `heckeAlphaBar`, respectively `heckeBetaBar`. Writing $\varphi$ for the self-map `frobOnPlacesGeomLevel k N data hKr` of the places of `modularFunctionFieldC k N`, the predicate `IsStrictFst W` asserts $\varphi(\mathrm{reduceFst}\,W) = \mathrm{reduceSnd}\,W$ together with $\varphi^2(\mathrm{reduceFst}\,W) \neq \mathrm{reduceFst}\,W$, and `IsStrictSnd W` asserts $\mathrm{reduceFst}\,W = \varphi(\mathrm{reduceSnd}\,W)$ together with $\varphi^2(\mathrm{reduceSnd}\,W) \neq \mathrm{reduceSnd}\,W$. A divisor $D$ on the level-$Nq$ curve over $\overline{\mathbb Q}$ is `IsGoodDiv` if every place in its support satisfies one of the two; `fstDiv D` and `sndDiv D` are the restrictions of $D$ (as a finitely supported function) to the places of the first, respectively second, kind. For a finite set $S$ of pairs of places of `modularFunctionFieldC k N`, `glueData P S D` is the element of `GluingData k (modularFunctionFieldC k N) S` given by the triple consisting of the pushforward of `fstDiv D` along `reduceFst`, the pushforward of `sndDiv D` along `reduceSnd`, and $0$ in the remaining component.
--
--   `IsGluedSpecialization S sp`, for an additive map $sp$ from the classes in `JZero (N * q)` fixed by every element of the inertia subgroup `A.inertiaSubgroupIn ℚ` to `GluedPic0 k (modularFunctionFieldC k N) S`, asserts that whenever a degree-zero divisor $D$ is good, its class lies in those inertia invariants, and an admissible gluing datum $x$ equals `glueData P S D`, one has $sp$ of that class equal to `GluedPic0.mk S x`. `IsGoodClass S x` asserts that $x \in$ `JZero (N * q)` is the class of some good degree-zero divisor whose gluing datum is admissible. The accompanying lemmas record the degenerate case: `fstDiv`, `sndDiv` and `glueData` vanish on the zero divisor, the zero divisor is good, and the zero class is a good class.
--
--   **Relation to Mathlib.** Divisors are Mathlib finitely supported functions on the project's type of places, so the splitting `fstDiv`/`sndDiv` is `Finsupp.filter` and the two reductions of a divisor are `Finsupp.mapDomain`; the gluing data, their admissible subgroup and the glued degree-zero class group are project notions with no Mathlib counterpart.
--
--   **Where it is used.** These predicates give the explicit recipe by which a divisor class on $X_0(Nq)$ over $\overline{\mathbb Q}$ is specialised to the glued Picard group of the special fibre at $q$, two copies of $X_0(N)$ over $k$ crossed along the set $S$ of node pairs. They provide the vocabulary in which the semistable specialisation data for $J_0(Nq)$ at $q$ is constructed, which in turn feeds the level-lowering step of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_GlueData.lean

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

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

def reduceFst (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Place k (modularFunctionFieldC k N) :=
  P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)

def reduceSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Place k (modularFunctionFieldC k N) :=
  P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)

def IsStrictFst (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W ∧
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
      ≠ P.reduceFst W

def IsStrictSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) ∧
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W))
      ≠ P.reduceSnd W

def IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  ∀ W ∈ D.support, P.IsStrictFst W ∨ P.IsStrictSnd W

open Classical in

def fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
  D.filter P.IsStrictFst

open Classical in

def sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
  D.filter P.IsStrictSnd

def glueData
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    GluingData k (modularFunctionFieldC k N) S :=
  (Finsupp.mapDomain P.reduceFst (P.fstDiv D), Finsupp.mapDomain P.reduceSnd (P.sndDiv D), 0)

def IsGluedSpecialization
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (sp : ↥(inertiaInvariants A (N * q)) →+ GluedPic0 k (modularFunctionFieldC k N) S) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (N * q))
    (x : ↥(GluingData.admissible S)),
    P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
    (x : GluingData k (modularFunctionFieldC k N) S) = P.glueData S D →
      sp ⟨Pic0.mk D, hH⟩ = GluedPic0.mk S x

def IsGoodClass
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (x : JZero (N * q)) : Prop :=
  ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
    P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
      P.glueData S D ∈ GluingData.admissible S ∧ Pic0.mk D = x

theorem fstDiv_zero : P.fstDiv 0 = 0 := by
  ext W
  simp [fstDiv, Finsupp.filter_apply]

theorem sndDiv_zero : P.sndDiv 0 = 0 := by
  ext W
  simp [sndDiv, Finsupp.filter_apply]

theorem glueData_zero
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    P.glueData S 0 = 0 := by
  simp only [glueData, fstDiv_zero, sndDiv_zero, Finsupp.mapDomain_zero]
  rfl

theorem isGoodDiv_zero : P.IsGoodDiv 0 := fun W hW => absurd hW (by simp)

theorem isGoodClass_zero
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    P.IsGoodClass S 0 := by
  refine ⟨0, P.isGoodDiv_zero, ?_, rfl⟩
  rw [ZeroMemClass.coe_zero, glueData_zero]
  exact zero_mem _

example (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (h : ∀ W, ¬ P.IsStrictFst W ∧ ¬ P.IsStrictSnd W)
    (sp : ↥(inertiaInvariants A (N * q)) →+ GluedPic0 k (modularFunctionFieldC k N) S) :
    P.IsGluedSpecialization S sp := by
  intro D hH x hgood hx
  have hD : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = 0 := by
    ext W
    by_contra hW
    rcases hgood W (Finsupp.mem_support_iff.mpr hW) with h1 | h2
    · exact (h W).1 h1
    · exact (h W).2 h2
  have hD0 : D = 0 := Subtype.ext hD
  subst hD0
  have hx0 : (x : GluingData k (modularFunctionFieldC k N) S) = 0 := by
    rw [hx, ZeroMemClass.coe_zero, glueData_zero]
  have hx0' : x = 0 := Subtype.ext hx0
  subst hx0'
  have hmk : (⟨Pic0.mk (0 : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar (N * q))))), hH⟩ : ↥(inertiaInvariants A (N * q))) = 0 :=
    Subtype.ext rfl
  rw [hmk, map_zero, map_zero]

end PlaceSpecialization

end ModularCurve

end


