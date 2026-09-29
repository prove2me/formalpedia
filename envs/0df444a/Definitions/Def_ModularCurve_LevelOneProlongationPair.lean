-- Prove2me | Definitions.Def_ModularCurve_LevelOneProlongationPair
-- name    : ModularCurve_LevelOneProlongationPair
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/a2557405-6eca-5566-ae26-276879668b74
-- title:
--   Level-one prolongation pairs for X0​(q) modulo q
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb Q}$ with residue field $k_0$, $k$ a field of characteristic $q$ with a ring map $\mathrm{red}\colon A\to k$, and $P$ a `PlaceSpecialization` at level one attached to modular polynomial data satisfying the Kronecker congruence and to integrality data $h\alpha,h\beta$ for the two degeneracy maps. The ambient function field is `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot q$, realised inside $\overline{\mathbb Q}((\mathfrak q))$.
--
--   The structure `LevelOneProlongationPair P` packages: a factorisation $\overline{\mathrm{red}}\colon k_0\to k$ of $\mathrm{red}$ through the residue map of $A$; a ring map $\iota$ from the level-one field over $k_0$ to the level-one field over $k$ acting coefficientwise through $\overline{\mathrm{red}}$; and two regular prolongations $R_1,R_2$ of $A$ to the level-$q$ field with residue field the level-one field over $k_0$ (each a valuation subring meeting $\overline{\mathbb Q}$ exactly in $A$, with surjective residue map whose kernel is the maximal ideal, compatible with $A\to k_0$, and such that every nonzero element has a constant multiple with nonzero residue). Three further fields pin the pair down: $R_1$ contains every element whose $\mathfrak q$-expansion has all coefficients in $A$ and reduces it coefficientwise; $R_2$ is the Fricke transport of $R_1$, i.e. $f\in R_2$ iff $w_qf\in R_1$, with $\rho_2=\rho_1\circ w_q$; and $\iota\circ\rho_1$ agrees with the char-$q$ reduction homomorphism `modularRedLocHom` on the localised modular ring.
--
--   Auxiliary definitions name $j$ and $j\circ(\mathfrak q\mapsto\mathfrak q^{q})$ as elements `jFun`, `jqFun` of the level-$q$ field, the two uniformisers $t_\infty=j_q/j^{q}$, $t_0=j/j_q^{q}$, and predicates on places $W$: `IsCuspidal` ($\mathrm{ord}_W(j-a)\le 0$ for all $a\in A$, so $j$ has a pole), `IsCuspidal'` (same for $j_q$), `IsInftySide` (cuspidal, and $t_\infty$ has at $W$ a value in $A$ reducing to $1$), `IsZeroSide` (the analogue with $t_0$).
--
--   On a pair $R$, with $\rho_i$ composed with $\iota$ written `residue₁`, `residue₂`, four propositions are named, all for $f$ lying in both $R_1$ and $R_2$ with nonzero residues and $D$ the divisor of $f$: `DivisorLawFst` and `DivisorLawSnd` assert that, at a place $v$ of the level-one field over $k$ not fixed by the square of the geometric Frobenius, the pushforward along $P.\mathrm{redFst}$ (resp. $P.\mathrm{redSnd}$) of the part of $D$ supported on strictly type-one (resp. type-two) places equals $\mathrm{ord}_v$ of the corresponding residue of $f$; `CuspLawInfty` and `CuspLawZero` are the same equalities at the reductions of the cusps $\infty$ and $0$, with $D$ restricted to `IsInftySide`, resp. `IsZeroSide`, places. `OrderLawFixed` treats a place $v$ fixed by the square of Frobenius and distinct from the reduction of $\infty$: the full pushforward of $D$ along $P.\mathrm{redFst}$ at $v$ equals $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}_{\varphi v}$ of the second. `IsModel` is the conjunction of the first four laws.
--
--   Separately, `NodeValueLaw` is a predicate on $(q,\mathrm{red})$ alone: for $f$ in the level-$q$ field whose expansion lies in the localised modular ring, whose reduction lies in the level-one field over $k$ and is nonzero, with the same two conditions for $w_qf$, and for $a\in k$ supersingular in the sense of `ssJSet q k` (every elliptic curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $q$), provided no place in the support of the divisor of $f$ simultaneously has $j$ specialising to a lift of $a$ and $j_q$ to a lift of $a^{q}$, there is a single $c\ne 0$ in $k$ such that the place $\,$ attached to $a$ gives value $c$ to the reduction of $f$ and the place attached to $a^{q}$ gives the same value $c$ to the reduction of $w_qf$; these two places are the pair `frobNodePair q a`.
--
--   **Relation to Mathlib.** Mathlib supplies valuation subrings, Laurent series and `Finsupp` operations, but not the notions used here: the regular prolongation of a valuation of the constant field to a function field with prescribed residue field, the modular function fields realised inside Laurent series, and the places/divisors formalism are the project's own.
--
--   **Where it is used.** The pair $(R_1,R_2)$ is the pair of Gauss prolongations attached to the two components of the special fibre of $X_0(q)$ in characteristic $q$, the second obtained from the first by the Fricke involution; the divisor, cusp and order laws are what is needed to compute the specialisation of degree-zero divisor classes on $X_0(q)_{\overline{\mathbb Q}}$ into the glued Picard group of two copies of the $j$-line, and `NodeValueLaw` is the gluing condition at the supersingular nodes. These data underlie the Eichler–Shimura relation and component-group computations used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneProlongationPair.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

def LevelOneProlongationPair.NodeValueLaw (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) : Prop :=
  letI := Classical.decEq k
  ∀ (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (a : k) (ha : a ∈ ssJSet q k)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) -
              algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) -
              algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))),
    ∃ c : k, c ≠ 0 ∧
      (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (⟨_, h₂F⟩ : modularFunctionFieldC k 1) c

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 400000 in

structure LevelOneProlongationPair (P : PlaceSpecialization A q 1 data hKr k red hα hβ) where

  redBar : ResidueField A →+* k
  redBar_residue : ∀ a : A, redBar (IsLocalRing.residue A a) = red a

  ι : modularFunctionFieldFullC (ResidueField A) 1 →+* modularFunctionFieldC k 1
  ι_coe : ∀ x : modularFunctionFieldFullC (ResidueField A) 1,
    ((ι x : modularFunctionFieldC k 1) : LaurentSeries k) = coeffMap redBar (x : LaurentSeries (ResidueField A))

  R₁ : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1)

  R₂ : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1)

  residue₁_coeffMap : ∀ (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q)),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * q)) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
          LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y

  mem_integers₂_iff : ∀ f : modularFunctionFieldBar (1 * q),
    f ∈ R₂.integers ↔ frickeInvolutionBar (1 * q) f ∈ R₁.integers

  residue₂_eq : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R₂.integers),
    R₂.residue ⟨f, h⟩ = R₁.residue ⟨frickeInvolutionBar (1 * q) f, (mem_integers₂_iff f).mp h⟩

  residue₁_eq_modularRedLocHom : ∀ (f : modularFunctionFieldBar (1 * q))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
    ∃ h : f ∈ R₁.integers,
      ((ι (R₁.residue ⟨f, h⟩) : modularFunctionFieldC k 1) : LaurentSeries k) =
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨f, hf⟩

def jFun : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

def jqFun : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

def tInfty : modularFunctionFieldBar (1 * q) := jqFun (q := q) / jFun (q := q) ^ (1 * q)

def tZero : modularFunctionFieldBar (1 * q) := jFun (q := q) / jqFun (q := q) ^ (1 * q)

def IsCuspidal (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ a : A, W.ord (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

set_option linter.unusedVariables false in

def IsInftySide (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  P.IsCuspidal W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tInfty (q := q)) (τ : AlgebraicClosure ℚ)

set_option linter.unusedVariables false in
set_option linter.unusedVariables false in

def IsCuspidal' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ a : A, W.ord (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

set_option linter.unusedVariables false in

def IsZeroSide (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tZero (q := q)) (τ : AlgebraicClosure ℚ)

namespace LevelOneProlongationPair

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

def residue₁ : R.R₁.integers →+* modularFunctionFieldC k 1 := R.ι.comp R.R₁.residue

def residue₂ : R.R₂.integers →+* modularFunctionFieldC k 1 := R.ι.comp R.R₂.residue

@[simp] theorem residue₁_apply (f : R.R₁.integers) : R.residue₁ f = R.ι (R.R₁.residue f) := rfl
@[simp] theorem residue₂_apply (f : R.R₂.integers) : R.residue₂ f = R.ι (R.R₂.residue f) := rfl

open Classical in

def DivisorLawFst : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
        Finsupp.mapDomain P.redFst (D.filter P.IsStrictTypeOne) v = v.ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def DivisorLawSnd : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
        Finsupp.mapDomain P.redSnd (D.filter P.IsStrictTypeTwo) v = v.ord (R.residue₂ ⟨f, h₂⟩)

open Classical in

def CuspLawInfty : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      Finsupp.mapDomain P.redFst (D.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) =
        (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def CuspLawZero : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      Finsupp.mapDomain P.redSnd (D.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) =
        (P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨f, h₂⟩)

def OrderLawFixed : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        v ≠ P.redFst (cuspInftyBar (1 * q)) →
        Finsupp.mapDomain P.redFst D v =
          v.ord (R.residue₁ ⟨f, h₁⟩) + (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩)

def IsModel : Prop := R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end


