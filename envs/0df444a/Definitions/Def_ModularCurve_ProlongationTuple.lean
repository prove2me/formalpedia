-- Prove2me | Definitions.Def_ModularCurve_ProlongationTuple
-- name    : ModularCurve_ProlongationTuple
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/bd45144e-01ee-5f2d-b40b-3715adb6d310
-- title:
--   Prolongation tuples for reduction of level-Nq functions mod q
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, $N$ a nonzero level, $k$ a field of characteristic $q$, $\mathrm{red} : A \to k$ a ring homomorphism, and `data`, `hKr`, `hα`, `hβ` the modular-polynomial and Hecke-integrality data entering a place specialisation $P$. The auxiliary definitions fix the geometric objects used: `atkinLehnerBar N q` is the base change to $\overline{\mathbb{Q}}$ of the chosen partial Atkin–Lehner automorphism `atkinLehnerInvolutionFull N q` of the full level-$Nq$ function field; `jFun N q` and `jQFun N q` are the images under coefficientwise $\mathbb{Q} \to \overline{\mathbb{Q}}$ of the $q$-expansions $j$ and $j(\mathfrak q^q)$; $t_\infty = j(\mathfrak q^q)/j^q$ and $t_0 = j/j(\mathfrak q^q)^q$ are the two cuspidal charts. A place $W$ of the geometric level-$Nq$ field is `IsCuspidal` (resp. `IsCuspidal'`) when $\operatorname{ord}_W(j - a) \le 0$ (resp. for $j(\mathfrak q^q)$) for every $a \in A$, and `IsInftySide` (resp. `IsZeroSide`) when moreover $W$ takes at $t_\infty$ (resp. $t_0$) a value $\tau \in A$ with $\mathrm{red}\,\tau = 1$.
--
--   The structure `ProlongationTuple P` carries: a factorisation `redBar` of $\mathrm{red}$ through the residue field of $A$; a ring homomorphism `ι` from the full level-$N$ function field over that residue field into the level-$N$ field over $k$, acting coefficientwise by `redBar`; two regular prolongations `R₁`, `R₂` of $A$ to the geometric level-$Nq$ field with residue field the full level-$N$ field over the residue field of $A$ (a `RegularProlongation` is a valuation subring of the big field inducing $A$ on constants, with a surjective residue map whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element becomes a unit after scaling by a constant); and dictionary fields asserting that `R₁` integrality is membership in the localisation `CharPReduction.modularLocalized (N*q) A.toSubring red` of the $A$-modular ring of $q$-expansions at the kernel of coefficientwise reduction, that `R₂` integrality is the same condition for the Atkin–Lehner transform, that the residue map of `R₂` is that of `R₁` composed with Atkin–Lehner, that `R₁` prolongs the coefficientwise residue map on Laurent series with $A$-coefficients, and that `ι ∘ R₁.residue` agrees with `CharPReduction.modularRedLocHom`. The derived `residue₁`, `residue₂` are `ι` composed with the two residue maps, and `mem_integers₂_iff` restates the two integrality dictionaries.
--
--   The remaining declarations are named predicates on a tuple $R$, each quantified over functions $f$ integral for both prolongations with both residues nonzero and over a divisor $D$ equal to the divisor of $f$. `DivisorLawFst`/`DivisorLawSnd` assert that, at places $v$ of the level-$N$ field over $k$ not fixed by the square of `frobOnPlacesGeomLevel`, the pushforward along `P.reduceFst` (resp. `reduceSnd`) of the part of $D$ supported on `P.IsStrictFst` (resp. `IsStrictSnd`) places equals $\operatorname{ord}_v$ of the corresponding residue; `OrderLawFixed` asserts that at affine places fixed by that square the pushforward of all of $D$ equals the sum of $\operatorname{ord}_v$ of the first residue and the order of the second residue at the Frobenius image of $v$; `CuspLawInfty`/`CuspLawZero` are the analogous statements for the cuspidal families cut out by `IsInftySide`/`IsZeroSide`. `IsModel` is the conjunction of the two divisor laws and the two cusp laws (it does not include `OrderLawFixed`). For perfect $k$ and a finite set $W$ of places, `NodeValueLaw` requires, at each node pair $(w, \mathrm{Frob}\cdot w)$ with $w \in W$ avoided by the divisor of $f$, a common nonzero value of the two residues on the two branches; `RegularityLaw` requires nonnegativity of the branch orders, and existence of a common (possibly zero) branch value, under nonnegativity of $\operatorname{ord}_V f$ above the place in question. `SplitDatum W π E D₁ D₂ lam` collects: $\pi_w$ is a uniformiser at each $w \in W$; interlacing bounds for $D_1(v)$ and $D_2(\mathrm{Frob}\,v)$ between the pushforwards of the negative and positive parts of $E$; $\deg D_1 + \deg D_2 = \deg E$; nonvanishing of `lam` on $W$; agreement of $D_1, D_2$ with the pushforwards of `P.fstDiv E`, `P.sndDiv E` off the fixed locus; additivity $D_1(v) + D_2(\mathrm{Frob}\,v)$ on the affine fixed locus; the two cuspidal identities; and the requirement that the residues of any $f$ in the Riemann–Roch space of $E$ lie in those of $D_1$ and $D_2$ with matching leading values at every node pair up to the scalar $\mathrm{lam}$. `SplitLaw` asserts existence of such $D_1, D_2, \mathrm{lam}$ for every divisor $E$ invariant under the inertia subgroup of $A$ whose support avoids a bad set `Wbad`, and `SplitLawEff` the same for effective $E$. Finally `ExceptionalProlongations R w m` is a structure carrying $m$ further regular prolongations of $A$ to the geometric level-$Nq$ field with residue field the rational function field over the residue field of $A$, together with the requirement that any $f$ whose two residues are units at $w$ and at $\mathrm{Frob}\cdot w$ remain integral with nonzero residue for each of them.
--
--   **Relation to Mathlib.** `RegularProlongation`, places, divisors and Riemann–Roch spaces of function fields in this valuation-theoretic form, and the characteristic-$q$ reduction apparatus for modular $q$-expansions are the project's own notions; only the ambient `ValuationSubring`, `IsLocalRing.ResidueField`, `LaurentSeries` and `Finsupp` machinery is Mathlib's.
--
--   **Where it is used.** The tuples and their laws are the valuation-theoretic substitute for the Deligne–Rapoport description of the special fibre of $X_0(Nq)$ at $q$ as two copies of $X_0(N)$ glued at the supersingular points, with Atkin–Lehner interchanging the two branches. They feed the gluing data and the specialisation of degree-zero divisor classes used in the study of $J_0(Nq)$ in characteristic $q$, which underlies the level-lowering step of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ProlongationTuple.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

namespace ProlongationTuple

def atkinLehnerBar (N q : ℕ) [NeZero q] :
    modularFunctionFieldBar (N * q) ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar (N * q) :=
  geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)

def jFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩

def jQFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (N * q) (dvd_mul_left q N))⟩

def tInfty (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  jQFun N q / jFun N q ^ q

def tZero (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  jFun N q / jQFun N q ^ q

def IsCuspidal (_P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  ∀ a : A, W.ord (jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

def IsCuspidal' (_P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  ∀ a : A, W.ord (jQFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

def IsInftySide (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsCuspidal P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tInfty N q) (τ : AlgebraicClosure ℚ)

def IsZeroSide (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tZero N q) (τ : AlgebraicClosure ℚ)

end ProlongationTuple

set_option linter.unusedVariables false in

structure ProlongationTuple (P : PlaceSpecialization A q N data hKr k red hα hβ) where

  redBar : ResidueField A →+* k
  redBar_residue : ∀ a : A, redBar (IsLocalRing.residue A a) = red a

  ι : modularFunctionFieldFullC (ResidueField A) N →+* modularFunctionFieldC k N
  ι_coe : ∀ x : modularFunctionFieldFullC (ResidueField A) N,
    ((ι x : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffMap redBar (x : LaurentSeries (ResidueField A))

  R₁ : RegularProlongation A (modularFunctionFieldBar (N * q))
    (modularFunctionFieldFullC (ResidueField A) N)

  R₂ : RegularProlongation A (modularFunctionFieldBar (N * q))
    (modularFunctionFieldFullC (ResidueField A) N)

  residue₁_coeffMap : ∀ (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q)),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) N) :
          LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y

  mem_integersFst_iff : ∀ f : modularFunctionFieldBar (N * q),
    f ∈ R₁.integers ↔ (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red

  mem_integersSnd_iff : ∀ f : modularFunctionFieldBar (N * q),
    f ∈ R₂.integers ↔
      ((ProlongationTuple.atkinLehnerBar N q f : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red

  residue₂_eq : ∀ (f : modularFunctionFieldBar (N * q)) (h : f ∈ R₂.integers),
    R₂.residue ⟨f, h⟩ = R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q f,
      (mem_integersFst_iff (ProlongationTuple.atkinLehnerBar N q f)).mpr
        ((mem_integersSnd_iff f).mp h)⟩

  residue₁_eq_modularRedLocHom : ∀ (f : modularFunctionFieldBar (N * q))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
    ∃ h : f ∈ R₁.integers,
      ((ι (R₁.residue ⟨f, h⟩) : modularFunctionFieldC k N) : LaurentSeries k) =
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hf⟩

namespace ProlongationTuple

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem mem_integers₂_iff (f : modularFunctionFieldBar (N * q)) :
    f ∈ R.R₂.integers ↔ atkinLehnerBar N q f ∈ R.R₁.integers := by
  rw [R.mem_integersSnd_iff f, R.mem_integersFst_iff (atkinLehnerBar N q f)]

def residue₁ : R.R₁.integers →+* modularFunctionFieldC k N := R.ι.comp R.R₁.residue

def residue₂ : R.R₂.integers →+* modularFunctionFieldC k N := R.ι.comp R.R₂.residue

@[simp] theorem residue₁_apply (f : R.R₁.integers) : R.residue₁ f = R.ι (R.R₁.residue f) := rfl
@[simp] theorem residue₂_apply (f : R.R₂.integers) : R.residue₂ f = R.ι (R.R₂.residue f) := rfl

open Classical in

def DivisorLawFst : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v = v.ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def DivisorLawSnd : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) v = v.ord (R.residue₂ ⟨f, h₂⟩)

open Classical in

def OrderLawFixed : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
        Finsupp.mapDomain P.reduceFst D v =
          v.ord (R.residue₁ ⟨f, h₁⟩)
            + (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)

open Classical in

def CuspLawInfty : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsInftySide P c →
        Finsupp.mapDomain P.reduceFst (D.filter (IsInftySide P)) (P.reduceFst c) =
          (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def CuspLawZero : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsZeroSide P c →
        Finsupp.mapDomain P.reduceSnd (D.filter (IsZeroSide P)) (P.reduceSnd c) =
          (P.reduceSnd c).ord (R.residue₂ ⟨f, h₂⟩)

def IsModel : Prop := R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero

def NodeValueLaw [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N))) : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ ≠ 0 →
    ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), V.ord f ≠ 0 →
        ¬ (P.reduceFst V = s.1 ∧ P.reduceSnd V = s.2)) →
      ∃ c : k, c ≠ 0 ∧
        s.1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) c ∧
        s.2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) c

def RegularityLaw [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N))) : Prop :=
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (v : Place k (modularFunctionFieldC k N)),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.reduceFst V = v → 0 ≤ V.ord f) →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.reduceFst V = s.1 → 0 ≤ V.ord f) →
      ∃ c : k, s.1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) c ∧
               s.2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) c)

open Classical in

def SplitDatum [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N)))
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
    (lam : Place k (modularFunctionFieldC k N) → k) : Prop :=
  (∀ w ∈ W, w.ord (π w) = 1) ∧

  (∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      Finsupp.mapDomain P.reduceFst (E.filter fun V => E V < 0) v ≤ D₁ v ∧
      D₁ v ≤ Finsupp.mapDomain P.reduceFst (E.filter fun V => 0 < E V) v ∧
      Finsupp.mapDomain P.reduceFst (E.filter fun V => E V < 0) v
        ≤ D₂ (frobOnPlacesGeomLevel k N data hKr v) ∧
      D₂ (frobOnPlacesGeomLevel k N data hKr v)
        ≤ Finsupp.mapDomain P.reduceFst (E.filter fun V => 0 < E V) v) ∧

  D₁.degree + D₂.degree = E.degree ∧

  (∀ w ∈ W, lam w ≠ 0) ∧

  (∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      D₁ v = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v ∧
      D₂ v = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v) ∧

  (∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      D₁ v + D₂ (frobOnPlacesGeomLevel k N data hKr v) = Finsupp.mapDomain P.reduceFst E v) ∧

  (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsInftySide P c →
      D₁ (P.reduceFst c) =
        Finsupp.mapDomain P.reduceFst (E.filter (IsInftySide P)) (P.reduceFst c)) ∧
  (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsZeroSide P c →
      D₂ (P.reduceSnd c) =
        Finsupp.mapDomain P.reduceSnd (E.filter (IsZeroSide P)) (P.reduceSnd c)) ∧

  ∀ f : modularFunctionFieldBar (N * q), f ∈ riemannRochSpace E →
    ∀ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) ∈ riemannRochSpace D₁ ∧
      (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) ∈ riemannRochSpace D₂ ∧
      ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        ∃ c : k,
          s.1.HasValue (π s.1 ^ (D₁ s.1) * (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N))
            (lam s.1 * c) ∧
          s.2.HasValue ((arithFrobC q k N • π s.1) ^ (D₂ s.2)
              * (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N)) c

open Classical in

def SplitLaw [PerfectField k] (W Wbad : Finset (Place k (modularFunctionFieldC k N)))
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) : Prop :=
  ∀ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) →
    (∀ V ∈ E.support, ∀ w ∈ Wbad, ¬ (P.reduceFst V = w)) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
      (lam : Place k (modularFunctionFieldC k N) → k), R.SplitDatum W π E D₁ D₂ lam

open Classical in

def SplitLawEff [PerfectField k] (W Wbad : Finset (Place k (modularFunctionFieldC k N)))
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) : Prop :=
  ∀ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    (∀ V, 0 ≤ E V) →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) →
    (∀ V ∈ E.support, ∀ w ∈ Wbad, ¬ (P.reduceFst V = w)) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
      (lam : Place k (modularFunctionFieldC k N) → k), R.SplitDatum W π E D₁ D₂ lam

set_option linter.unusedVariables false in

structure ExceptionalProlongations [PerfectField k] (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (m : ℕ) where

  Rex : Fin m → RegularProlongation A (modularFunctionFieldBar (N * q))
    (RatFunc (ResidueField A))

  unit_compat : ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
      (h₂ : f ∈ R.R₂.integers),
    R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ ≠ 0 →
    w.ord (R.residue₁ ⟨f, h₁⟩) = 0 →
    (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩) = 0 →
    ∀ i : Fin m, ∃ h : f ∈ (Rex i).integers, (Rex i).residue ⟨f, h⟩ ≠ 0

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end


