-- Prove2me | Definitions.Def_ModularCurve_JHPlaceSpecialization
-- name    : ModularCurve_JHPlaceSpecialization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/f0ab4519-a102-501c-9474-03b002377802
-- title:
--   Place specialisation and prolongation data at p for XH​
-- statement:
--   Standing context: a prime $p$ dividing $M$, a subgroup $H\le(\mathbb Z/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $FM$ for the function field `xHFunctionFieldBar M H`, $FMp$ for the corresponding field at level $M/p$ with the subgroup `infSubgroup p M H hpM`, and $Fb$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for $\Gamma' =$ `ΓN p M H hpM`. The module defines data and predicates only; nothing is asserted. `inertiaInvariants` is the additive subgroup of $JH\,M\,H$ fixed by every element of `A.inertiaSubgroupIn ℚ`, and `PrimeToTorsion x` says $m\cdot x=0$ for some $m>0$ coprime to $p$. The structure `JHPlaceSpecialization` packages a map $sp$ from places of $FMp$ to places of $Fb$ together with a homomorphism `spPic0` of degree-zero class groups, and carries as fields: a $q$-expansion dictionary (`d0_qexp`) saying that if $f\in FMp$ has Laurent expansion with coefficients in $A$ and $g\in Fb$, $g\neq0$, has the coefficientwise residue expansion, then the pushforward along $sp$ of the divisor of $f$ is the divisor of $g$; surjectivity of $sp$; a principal-to-principal law (`d5`); invariance of $sp$ under the `arithmeticGalois` action of inertia elements; the rule that a Frobenius at $p$ acts through `qExpFrobeniusPlaceModL κ Γ′ p` after $sp$; and compatibility of `spPic0` with divisor pushforward.
--
--   Given integral $\overline{\mathbb Q}$-algebra maps $\alpha,\beta:FMp\to FM$ and a self-map $\delta$ of places of $Fb$, two readings of a place $W$ of $FM$ are defined: `reduceFst` $W=sp(W|_\alpha)$ and `reduceSnd` $W=\delta(sp(W|_\beta))$. Writing $\varphi$ for `qExpFrobeniusPlaceModL κ Γ′ p`, `Fixed δ v` means $\varphi(\delta(\varphi v))=v$; `IsStrictFst` asks $\delta(\varphi(\mathrm{reduceFst}\,W))=\mathrm{reduceSnd}\,W$ with `reduceFst W` not fixed, `IsStrictSnd` the mirror condition, and `TypeDichotomy` that one of the two equations always holds. A divisor is good (`IsGoodDiv`) when every place in its support is strict of one kind; `fstDiv`, `sndDiv` split it accordingly, and `glueData` is the triple consisting of the two pushforwards and $0$ in `GluingData κ Fb SS` for a finite set $SS$ of pairs of places. `IsGluedSpecialization` is the compatibility demanded of a homomorphism from `inertiaInvariants` to `GluedPic0 κ Fb SS` on good degree-zero divisors with admissible glue data, and `IsGoodClass` says a class of $JH\,M\,H$ is represented by such a divisor. `IsAffinePlace` picks out places of $Fb$ at which an element with $j$-expansion `jqModC` has a value in $\kappa$; `IsCuspidal` (resp. `IsCuspidal'`) says that at $W$ no element with expansion $j$ (resp. with expansion `qExpand … p (jqModC …)`) becomes congruent to a constant from $A$ to positive order, and `IsInftySide`, `IsZeroSide` strengthen these by requiring the chart $x'/x^p$, resp. $x/x'^p$, to take at $W$ a value in $A$ with residue $1$.
--
--   Finally, `ProlongationDatum P θ`, for an automorphism $\theta$ of $FM$ over $\overline{\mathbb Q}$, consists of two regular prolongations $R_1,R_2$ of $A$ to $FM$ with residue field $Fb$, a $q$-expansion pin for $R_1$ (elements obtained coefficientwise from Laurent series over $A$ lie in $R_1$'s valuation ring and reduce to the coefficientwise residue series), and the requirement that $R_2$ be the transport of $R_1$ along $\theta$, on both integers and residues. Its predicates are laws relating divisors of an $f$ lying in both rings with nonzero residues to divisors of those residues: `DivisorLawFst` and `DivisorLawSnd` at non-fixed places, `CuspLawInfty` and `CuspLawZero` along the two cusp families, `OrderLawFixed` expressing the order at a fixed affine place as a sum of the two residue orders, `NodeValueLaw` and `RegularityLaw` at the node pairs in $SS$, and `IsModel`, the conjunction of the two divisor laws and the two cusp laws.
--
--   **Relation to Mathlib.** Places of a function field, divisors, $\mathrm{Pic}^0$, gluing data and regular prolongations are the project's own notions ([`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22), `Divisor`, `Pic0`, `GluingData`, `RegularProlongation`); Mathlib supplies the ambient valuation subrings, inertia subgroups and Laurent series used to state them.
--
--   **Where it is used.** These definitions form the dictionary by which points of the Jacobian $J_H(M)$ over $\overline{\mathbb Q}$ are read off in the two components of the special fibre at $p$ of the Deligne–Rapoport model, with the second reading corrected by a reduced diamond operator; later modules assert the existence of such specialisation and prolongation data and use them in the component-group and level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JHPlaceSpecialization.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups
set_option quotPrecheck false

namespace ModularCurve

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
variable (A : ValuationSubring (AlgebraicClosure ℚ))

namespace JHPlaceSpecialization

def inertiaInvariants : AddSubgroup (JH M H) where
  carrier := {x | ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x}
  zero_mem' := fun σ _ => smul_zero σ
  add_mem' := by
    intro x y hx hy σ hσ
    rw [smul_add, hx σ hσ, hy σ hσ]
  neg_mem' := by
    intro x hx σ hσ
    rw [smul_neg, hx σ hσ]

def PrimeToTorsion (x : JH M H) : Prop := ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • x = 0

end JHPlaceSpecialization

variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Γ′" => ModularCurve.JHNeronObjectAtP.ΓN p M H hpM

namespace JHPlaceSpecialization

def IsAffinePlace (v : Place κ Fb) : Prop :=
  ∃ (x : Fb) (a : κ), ((x : Fb) : LaurentSeries κ) = jqModC κ ∧ v.HasValue x a

def Fixed (δ : Place κ Fb → Place κ Fb) (v : Place κ Fb) : Prop :=
  qExpFrobeniusPlaceModL κ Γ′ p (δ (qExpFrobeniusPlaceModL κ Γ′ p v)) = v

end JHPlaceSpecialization

structure JHPlaceSpecialization where

  sp : Place (AlgebraicClosure ℚ) FMp → Place κ Fb

  spPic0 : Pic0 (AlgebraicClosure ℚ) FMp →+ Pic0 κ Fb

  d0_qexp : ∀ (f : FMp) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = ((f : FMp) : LaurentSeries (AlgebraicClosure ℚ)) →
    ∀ g : Fb, ((g : Fb) : LaurentSeries κ) = coeffMap (IsLocalRing.residue ↥A) y → g ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FMp, (∀ v, D v = v.ord f) →
      ∀ v' : Place κ Fb, Finsupp.mapDomain sp D v' = v'.ord g

  d4 : Function.Surjective sp

  d5 : ∀ f : FMp, f ≠ 0 → ∀ D : Divisor (AlgebraicClosure ℚ) FMp, (∀ v, D v = v.ord f) →
    ∃ g : Fb, g ≠ 0 ∧ ∀ v' : Place κ Fb, Finsupp.mapDomain sp D v' = v'.ord g

  d6_inertia : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) FMp,
      sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w

  d6_frobenius : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
    ∀ w : Place (AlgebraicClosure ℚ) FMp,
      sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
        qExpFrobeniusPlaceModL κ Γ′ p (sp w)

  spPic0_compat : ∀ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := FMp),
    ∃ D' : Divisor.degZero (K := κ) (F := Fb),
      (D' : Divisor κ Fb) = Finsupp.mapDomain sp (D : Divisor (AlgebraicClosure ℚ) FMp) ∧ spPic0 (Pic0.mk D) = Pic0.mk D'

namespace JHPlaceSpecialization

variable {p M H hpM A}

def reduceFst (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (W : Place (AlgebraicClosure ℚ) FM) : Place κ Fb :=
  P.sp (W.restrictAlong α hα)

def reduceSnd (P : JHPlaceSpecialization p M H hpM A) (β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (W : Place (AlgebraicClosure ℚ) FM) : Place κ Fb :=
  δ (P.sp (W.restrictAlong β hβ))

def IsStrictFst (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  δ (qExpFrobeniusPlaceModL κ Γ′ p (P.reduceFst α hα W)) = P.reduceSnd β hβ δ W ∧ ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (P.reduceFst α hα W)

def IsStrictSnd (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  P.reduceFst α hα W = qExpFrobeniusPlaceModL κ Γ′ p (P.reduceSnd β hβ δ W) ∧ ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (P.reduceSnd β hβ δ W)

def TypeDichotomy (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ W : Place (AlgebraicClosure ℚ) FM,
    P.reduceFst α hα W = qExpFrobeniusPlaceModL κ Γ′ p (P.reduceSnd β hβ δ W) ∨
      δ (qExpFrobeniusPlaceModL κ Γ′ p (P.reduceFst α hα W)) = P.reduceSnd β hβ δ W

def IsGoodDiv (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (D : Divisor (AlgebraicClosure ℚ) FM) : Prop :=
  ∀ W ∈ D.support, P.IsStrictFst α β hα hβ δ W ∨ P.IsStrictSnd α β hα hβ δ W

open Classical in

def fstDiv (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor (AlgebraicClosure ℚ) FM :=
  D.filter (P.IsStrictFst α β hα hβ δ)

open Classical in

def sndDiv (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor (AlgebraicClosure ℚ) FM :=
  D.filter (P.IsStrictSnd α β hα hβ δ)

def glueData (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) (D : Divisor (AlgebraicClosure ℚ) FM) : GluingData κ Fb SS :=
  (Finsupp.mapDomain (P.reduceFst α hα) (P.fstDiv α β hα hβ δ D),
    Finsupp.mapDomain (P.reduceSnd β hβ δ) (P.sndDiv α β hα hβ δ D), 0)

def IsGluedSpecialization (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (hβ : β.IsIntegral) (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb))
    (spJ : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ GluedPic0 κ Fb SS) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)))
    (hI : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A) (x : ↥(GluingData.admissible SS)),
    P.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM) →
    (x : GluingData κ Fb SS) = P.glueData α β hα hβ δ SS D →
      spJ ⟨Pic0.mk D, hI⟩ = GluedPic0.mk SS x

def IsGoodClass (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) (x : JH M H) : Prop :=
  ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)),
    P.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM) ∧ P.glueData α β hα hβ δ SS D ∈ GluingData.admissible SS ∧ Pic0.mk D = x

def IsCuspidal (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  ∀ (x : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
    ∀ a : ↥A, W.ord (x - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0

def IsCuspidal' (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ∀ (x : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) →
    ∀ a : ↥A, W.ord (x - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0

def IsInftySide (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsCuspidal (M := M) (H := H) (A := A) W ∧
    ∃ (x x' : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) ∧
      ((x' : FM) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) ∧
      ∃ τ : ↥A, IsLocalRing.residue ↥A τ = 1 ∧ W.HasValue (x' / x ^ p) (τ : AlgebraicClosure ℚ)

def IsZeroSide (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsCuspidal' (p := p) (M := M) (H := H) (A := A) W ∧
    ∃ (x x' : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) ∧
      ((x' : FM) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) ∧
      ∃ τ : ↥A, IsLocalRing.residue ↥A τ = 1 ∧ W.HasValue (x / x' ^ p) (τ : AlgebraicClosure ℚ)

structure ProlongationDatum (P : JHPlaceSpecialization p M H hpM A) (θ : FM ≃ₐ[AlgebraicClosure ℚ] FM) where

  R₁ : RegularProlongation A FM Fb

  R₂ : RegularProlongation A FM Fb

  residue₁_coeffMap : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : FM) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : Fb) : LaurentSeries κ) = coeffMap (IsLocalRing.residue ↥A) y

  mem_integers₂_iff : ∀ f : FM, f ∈ R₂.integers ↔ θ f ∈ R₁.integers
  residue₂_eq : ∀ (f : FM) (h : f ∈ R₂.integers), R₂.residue ⟨f, h⟩ = R₁.residue ⟨θ f, (mem_integers₂_iff f).mp h⟩

namespace ProlongationDatum

variable {P : JHPlaceSpecialization p M H hpM A}
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}

def DivisorLawFst (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ v : Place κ Fb, ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
        Finsupp.mapDomain (P.reduceFst α hα) (P.fstDiv α β hα hβ δ D) v = v.ord (R.R₁.residue ⟨f, h₁⟩)

def DivisorLawSnd (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ v : Place κ Fb, ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
        Finsupp.mapDomain (P.reduceSnd β hβ δ) (P.sndDiv α β hα hβ δ D) v = v.ord (R.R₂.residue ⟨f, h₂⟩)

open Classical in

def CuspLawInfty (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) FM, IsInftySide (p := p) (M := M) (H := H) (A := A) c →
        Finsupp.mapDomain (P.reduceFst α hα) (D.filter (IsInftySide (p := p) (M := M) (H := H) (A := A))) (P.reduceFst α hα c) =
          (P.reduceFst α hα c).ord (R.R₁.residue ⟨f, h₁⟩)

open Classical in

def CuspLawZero (R : ProlongationDatum P θ) (β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) FM, IsZeroSide (p := p) (M := M) (H := H) (A := A) c →
        Finsupp.mapDomain (P.reduceSnd β hβ δ) (D.filter (IsZeroSide (p := p) (M := M) (H := H) (A := A))) (P.reduceSnd β hβ δ c) =
          (P.reduceSnd β hβ δ c).ord (R.R₂.residue ⟨f, h₂⟩)

def OrderLawFixed (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ v : Place κ Fb, Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v →
        Finsupp.mapDomain (P.reduceFst α hα) D v =
          v.ord (R.R₁.residue ⟨f, h₁⟩) + (δ (qExpFrobeniusPlaceModL κ Γ′ p v)).ord (R.R₂.residue ⟨f, h₂⟩)

def NodeValueLaw (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) FM, V.ord f ≠ 0 → ¬ (P.reduceFst α hα V = s.1 ∧ P.reduceSnd β hβ δ V = s.2)) →
      ∃ c : κ, c ≠ 0 ∧ s.1.HasValue (R.R₁.residue ⟨f, h₁⟩ : Fb) c ∧ s.2.HasValue (R.R₂.residue ⟨f, h₂⟩ : Fb) c

def RegularityLaw (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) : Prop :=
  (∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) (v : Place κ Fb),
      Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v →
      (∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = v → 0 ≤ V.ord f) →
      (R.R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.R₁.residue ⟨f, h₁⟩)) ∧
      (R.R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ (δ (qExpFrobeniusPlaceModL κ Γ′ p v)).ord (R.R₂.residue ⟨f, h₂⟩))) ∧
  (∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers), ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = s.1 → 0 ≤ V.ord f) →
      ∃ c : κ, s.1.HasValue (R.R₁.residue ⟨f, h₁⟩ : Fb) c ∧ s.2.HasValue (R.R₂.residue ⟨f, h₂⟩ : Fb) c)

def IsModel (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  R.DivisorLawFst α β hα hβ δ ∧ R.DivisorLawSnd α β hα hβ δ ∧ R.CuspLawInfty α hα ∧ R.CuspLawZero β hβ δ

end ProlongationDatum
end JHPlaceSpecialization

end ModularCurve

end


