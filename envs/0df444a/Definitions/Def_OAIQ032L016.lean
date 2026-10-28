-- Prove2me | Definitions.Def_OAIQ032L016
-- name    : OAIQ032L016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:54:25.340329+00:00
-- url     : https://prove2.me/theorems/94279df3-807b-467e-95b1-1bc65518a8a5
-- title:
--   Definitions bundle OAIQ032L016 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 25 definitions, 10 instances and 23 theorems. The definitions and types are `OAI.Lech.RootTower.expansionBasis`, `OAI.Lech.RootTower.expansionEquiv`, `OAI.Lech.RootTower.expansionMap`, `OAI.Lech.RootTower.expansionToFrobenius`, `OAI.Lech.RootTower.expansionToFrobeniusMap`, `OAI.Lech.RootTower.frobeniusBasis`, `OAI.Lech.SignedCech.divide`, `OAI.Lech.SignedCech.intersectionHomotopy`, `OAI.Lech.SignedCech.term`, `OAI.Lech.SignedFraction.divide`, `OAI.Lech.TensorConductor.ambientComplex`, `OAI.Lech.TensorConductor.complexInclusion`, `OAI.Lech.TensorConductor.complexRetreat`, `OAI.Lech.TensorConductor.conductor`, `OAI.Lech.TensorConductor.congrLeft`, `OAI.Lech.TensorConductor.inclusion`, `OAI.Lech.TensorConductor.mapLeft`, `OAI.Lech.TensorConductor.stageComplex`, `OAI.Lech.TensorIdeal.bicomplexQuotientNat`, `OAI.Lech.TensorIdeal.complexQuotientNat`, `OAI.Lech.TensorIdeal.fibreMap`, `OAI.Lech.TensorIdeal.quotientNat`, `OAI.Lech.TensorTotal.degreeMap`, `OAI.Lech.TensorTotal.tensorSingleQuotientIso`, `OAI.Lech.TwistedLocalization.pieceCongr`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCartierRange`, `Multiplicity_CompleteResidueExtension`, `Multiplicity_ComplexConductor`, `Multiplicity_ComplexReduction`, `Multiplicity_FibreSquare`, `Multiplicity_FrobeniusIntermediatePowerMap`, `Multiplicity_IdealGradedLengthPiece`, `Multiplicity_IdealQuotientFunctor`, `Multiplicity_LechCokernelComp`, `Multiplicity_RootTowerLengthEq`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_RootUlrichSpan`, `Multiplicity_SourceGradedCechHomology`, `Multiplicity_TensorConductor`, `Multiplicity_TensorPushout`, `Multiplicity_TensorTotalHomologyProperty`, `Multiplicity_TwistedLocalizationPieceMap`.
--
--   **Imports.** It imports the bundles `OAIQ032L000`, `OAIQ032L002`, `OAIQ032L003`, `OAIQ032L004`, `OAIQ032L005`, `OAIQ032L006`, `OAIQ032L007` and `OAIQ032L008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L023`; the statement `OAI.Lech.TensorIdeal.fibreMap_kernel_zero`; the proofs of `OAI.Lech.PowerSeries.finite_module_two_limits`, `OAI.Lech.PowerSeries.finite_module_two_limits_pos` and `OAI.Lech.TensorConductor.length_tendsto`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L007
import Definitions.Def_OAIQ032L008

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

def fibreMap : (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R]
    ((B ⊗[A] V) ⧸ (I • (⊤ : Submodule R (B ⊗[A] V)))) :=
  idealQuotientMap I (unitMap (B:=B) V)

end Square
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TwistedLocalizationPieceMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.TwistedLocalization
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

omit [GradedAlgebra G] in
 

def pieceCongr {q : A} {e : ℕ} (hq : f=q) (he : d=e) (t : ℕ) :
    piece G (f := f) (d := d) t ≃ₗ[R] piece G (f := q) (d := e) t := by
  subst q; subst e; exact LinearEquiv.refl R _

end Lech.TwistedLocalization


namespace Lech.TwistedLocalization
open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]

 

lemma pieceCongr_pieceTo {f f' q q' c c' : A} {d d' e e' k k' : ℕ}
    (hf : f ∈ G d) (hc : c ∈ G k) (hfc : f*c=q) (hdeg : d+k=e)
    (hf' : f' ∈ G d') (hc' : c' ∈ G k') (hfc' : f'*c'=q') (hdeg' : d'+k'=e')
    (hff' : f=f') (hqq' : q=q') (hdd' : d=d') (hee' : e=e') (t : ℕ)
    (x : piece G (f := f) (d := d) t) :
    pieceCongr G hqq' hee' t (pieceTo G hf hc hfc hdeg t x) =
      pieceTo G hf' hc' hfc' hdeg' t (pieceCongr G hff' hdd' t x) := by
  subst f'; subst q'; subst d'; subst e'
  apply Subtype.ext
  rfl
end Lech.TwistedLocalization


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealQuotientFunctor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)


def quotientNat : 𝟭 (ModuleCat.{u} R) ⟶ quotientFunctor I where
  app M := ModuleCat.ofHom (Submodule.mkQ (I • (⊤ : Submodule R M)))
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl


lemma mem_smul_pi_iff {ι : Type*} [Fintype ι] (M : ι → Type u)
    [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] (x : ∀ i,M i) :
    x ∈ I • (⊤ : Submodule R (∀ i,M i)) ↔ ∀ i,x i ∈ I • (⊤ : Submodule R (M i)) := by
  rw [←Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h i
    have he := congrArg (quotientPiEquiv I M) h
    rw [quotientPiEquiv_mk,map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun he i)
  · intro h
    apply (quotientPiEquiv I M).injective
    rw [quotientPiEquiv_mk,map_zero]
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h i)

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (J : Ideal R) {ι : Type} [Fintype ι]
  (M N : ι → Type u) [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)]
  [∀ i,AddCommGroup (N i)] [∀ i,Module R (N i)] (f : ∀ i,M i →ₗ[R] N i)
lemma piMap_range (hf : ∀ i,(f i).range=J • (⊤ : Submodule R (N i))) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).range =
      J • (⊤ : Submodule R (∀ i,N i)) := by
  ext x
  rw [mem_smul_pi_iff]
  constructor
  · rintro ⟨y,rfl⟩ i
    rw [←hf i]
    exact LinearMap.mem_range_self _ _
  · intro hx
    have hy (i : ι) : x i ∈ (f i).range := (hf i).symm ▸ hx i
    choose y hy using hy
    exact ⟨y,funext hy⟩
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRemainderExponent
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
namespace Lech.RootTower
variable {σ R : Type*} [Fintype σ] [CommRing R] (q : ℕ) [NeZero q]

instance expandedCommRing : CommRing (Expanded (σ := σ) (R := R) q) :=
  inferInstanceAs (CommRing (MvPowerSeries σ R))

noncomputable instance expandedAlgebra :
    Algebra (MvPowerSeries σ R) (Expanded (σ := σ) (R := R) q) :=
  (expand (σ := σ) (R := R) q (NeZero.ne q)).toRingHom.toAlgebra

noncomputable def expansionMap :
    ((σ → Fin q) → MvPowerSeries σ R) →ₗ[MvPowerSeries σ R]
      Expanded (σ := σ) (R := R) q where
  toFun f := ∑ r, expand q (NeZero.ne q) (f r) * monomial (remainderExponent q r) 1
  map_add' f g := by
    change (∑ r, expand q (NeZero.ne q) (f r + g r) * _) = _
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    rfl
  map_smul' a f := by
    change (∑ r, expand q (NeZero.ne q) (a * f r) * _) =
      expand q (NeZero.ne q) a *
        (∑ r, expand q (NeZero.ne q) (f r) * monomial (remainderExponent q r) 1)
    simp only [map_mul, mul_assoc, Finset.mul_sum]

lemma expansionMap_bijective : Function.Bijective (expansionMap (σ := σ) (R := R) q) := by
  constructor
  · intro f g hfg
    funext r
    ext d
    have hh := congrArg (coeff (q • d + remainderExponent q r)) hfg
    exact (coeff_sum_expansion q f d r).symm.trans
      (hh.trans (coeff_sum_expansion q g d r))
  · intro f
    exact ⟨fun r => extract q r f, sum_expansion_extract q f⟩

noncomputable def expansionEquiv :
    ((σ → Fin q) → MvPowerSeries σ R) ≃ₗ[MvPowerSeries σ R]
      Expanded (σ := σ) (R := R) q :=
  LinearEquiv.ofBijective (expansionMap q) (expansionMap_bijective q)

noncomputable def expansionBasis : Module.Basis (σ → Fin q) (MvPowerSeries σ R)
    (Expanded (σ := σ) (R := R) q) :=
  (Pi.basisFun (MvPowerSeries σ R) (σ → Fin q)).map (expansionEquiv q)

lemma expanded_free : Module.Free (MvPowerSeries σ R) (Expanded (σ := σ) (R := R) q) :=
  Module.Free.of_basis (expansionBasis q)

lemma expansion_flat : (expand (σ := σ) (R := R) q (NeZero.ne q)).toRingHom.Flat := by
  let := expanded_free (σ := σ) (R := R) q
  exact inferInstanceAs (Module.Flat (MvPowerSeries σ R) (Expanded (σ := σ) (R := R) q))

omit [NeZero q] in
lemma iterateFrobenius_flat (p n : ℕ) [Fact p.Prime] [CharP R p]
    [PerfectRing R p] : (iterateFrobenius (MvPowerSeries σ R) p n).Flat := by
  let : NeZero (p^n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  have hm : (MvPowerSeries.map (σ := σ) (iterateFrobenius R p n)).Flat :=
    RingHom.Flat.of_bijective (map_bijective_of_bijective _ (bijective_iterateFrobenius R p n))
  have he := (expansion_flat (σ := σ) (R := R) (p^n)).comp hm
  have hp : (MvPowerSeries.map (σ := σ) (iterateFrobenius R p n)).comp
      (expand (p^n) (NeZero.ne (p^n))).toRingHom =
      iterateFrobenius (MvPowerSeries σ R) p n := by
    ext f d
    exact congrArg (coeff d) (map_iterateFrobenius_expand p (Nat.Prime.ne_zero Fact.out) f n)
  exact hp ▸ he

end Lech.RootTower

open scoped TensorProduct
open IsLocalRing

open MvPowerSeries IsLocalRing
namespace Lech.RootTower
variable {σ k : Type*} [Fintype σ] [Field k]

variable (p n : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

instance frobeniusExpandedRing : CommRing (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  inferInstanceAs (CommRing (MvPowerSeries σ k))
instance frobeniusExpandedLocal : IsLocalRing (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries σ k))
instance frobeniusExpandedAlgebra :
    Algebra (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  (iterateFrobenius (MvPowerSeries σ k) p n).toAlgebra

def expansionToFrobeniusMap [NeZero (p^n)] :
    Expanded (σ := σ) (R := k) (p^n) →ₗ[MvPowerSeries σ k]
      FrobeniusExpanded (σ := σ) (k := k) p n where
  toFun x := MvPowerSeries.map (iterateFrobenius k p n) x
  map_add' := map_add _
  map_smul' a x := by
    refine (map_mul (MvPowerSeries.map (iterateFrobenius k p n))
      (expand (p^n) (NeZero.ne (p^n)) a) (show MvPowerSeries σ k from x)).trans ?_
    exact congrArg (fun f : MvPowerSeries σ k =>
      @Mul.mul (MvPowerSeries σ k) _ f (MvPowerSeries.map (iterateFrobenius k p n) x))
      (map_iterateFrobenius_expand p (Nat.Prime.ne_zero Fact.out) a n)

def expansionToFrobenius [NeZero (p^n)] :
    Expanded (σ := σ) (R := k) (p^n) ≃ₗ[MvPowerSeries σ k]
      FrobeniusExpanded (σ := σ) (k := k) p n :=
  LinearEquiv.ofBijective (expansionToFrobeniusMap (σ := σ) (k := k) p n)
    (map_bijective_of_bijective _ (bijective_iterateFrobenius k p n))

def frobeniusBasis [NeZero (p^n)] :
    Module.Basis (σ → Fin (p^n)) (MvPowerSeries σ k)
      (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  (expansionBasis (p^n)).map (expansionToFrobenius (σ := σ) (k := k) p n)

instance frobeniusExpandedLocalHom :
    IsLocalHom (algebraMap (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n)) where
  map_nonunit x hx := by
    change IsUnit (iterateFrobenius (MvPowerSeries σ k) p n x) at hx
    rw [iterateFrobenius_def] at hx
    exact (isUnit_pow_iff (pow_ne_zero n (Nat.Prime.ne_zero Fact.out))).mp hx

omit [Fintype σ] in
lemma frobenius_residue_surjective : Function.Surjective
    (ResidueField.map (algebraMap (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n))) := by
  intro x
  obtain ⟨f,rfl⟩ := residue_surjective x
  obtain ⟨c,hc⟩ := (bijective_iterateFrobenius k p n).2 (constantCoeff f)
  refine ⟨residue (MvPowerSeries σ k) (C c), ?_⟩
  rw [ResidueField.map_residue]
  change residue (MvPowerSeries σ k) (iterateFrobenius (MvPowerSeries σ k) p n (C c)) =
    residue (MvPowerSeries σ k) f
  rw [← RingHom.map_iterateFrobenius, hc]
  exact (residue_eq_constant f).symm

lemma frobenius_fiber_length :
    Module.length (FrobeniusExpanded (σ := σ) (k := k) p n)
      (FrobeniusExpanded (σ := σ) (k := k) p n ⧸
        (maximalIdeal (MvPowerSeries σ k)).map
          (algebraMap (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n))) =
        (p ^ (n * Fintype.card σ) : ℕ) := by
  let : NeZero (p^n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  rw [fiber_length_of_basis (frobeniusBasis (σ := σ) (k := k) p n)
    (frobenius_residue_surjective p n)]
  simp [← pow_mul]

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]


lemma rootMap_injective (n : ℕ) : Function.Injective (rootMap A p n) := by
  intro x y h
  exact (frobenius_inj A p).iterate n ((PerfectClosure.eq_iff A p _ _).mp h)

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]


variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G H : CochainComplex (ModuleCat.{u} R) ℤ}

 

def degreeMap (a : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    ((functor K).obj F).X i ⟶ ((functor K).obj G).X i :=
  mapBifunctorDesc (fun p q hpq =>
    ((curriedTensor (ModuleCat.{u} R)).map (a p)).app (K.X q) ≫
      ιMapBifunctor G K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)

end Lech.TensorTotal
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]



def tensorSingleQuotientIso (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSingle F (ModuleCat.of R (R ⧸ I)) ≅ (complexQuotient I (.up ℤ)).obj F :=
  (tensorSingleIso F (ModuleCat.of R (R ⧸ I))).symm ≪≫
    (NatIso.mapHomologicalComplex (termTensorQuotientIso I) (.up ℤ)).app F
end Lech.TensorTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedCechHomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)



variable {w z c : R} {d k : ℕ}
  (hw : w∈I^d) (hc : c∈I^k) (hwc : z*c=w) (hdk : k+1=d)

include hc hdk in
lemma inverseFactor_fraction (t : ℤ) (m n : ℕ) (a : ↥(I^(order d (t+(m:ℤ)) n))) :
    ∃ b : ↥(I^(order d t (n+m))),
      FilteredFraction.inverseFactor (w := w) (c := c) m * fraction I w d (t+(m:ℤ)) n a =
        fraction I w d t (n+m) b := by
  have hc' : c^m∈I^(m*k) := by
    simpa only [pow_mul,mul_comm m k] using Ideal.pow_mem_pow hc m
  have hb : c^m*(a:R)∈I^(order d t (n+m)) := by
    apply Ideal.pow_le_pow_right (order_divide_le hdk t m n)
    rw [pow_add]
    exact Ideal.mul_mem_mul hc' a.property
  refine ⟨⟨c^m*(a:R),hb⟩,?_⟩
  change Localization.mk (c^m) (⟨w^m,m,rfl⟩ : Submonoid.powers w) *
    Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w) =
      Localization.mk (c^m*(a:R)) (⟨w^(n+m),n+m,rfl⟩ : Submonoid.powers w)
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,Submonoid.coe_mul,pow_add]
  ring

include hw hc hdk in
lemma inverseFactor_mem (t : ℤ) (m : ℕ) (x : piece I w d (t+(m:ℤ))) :
    FilteredFraction.inverseFactor (w := w) (c := c) m*x.val∈piece I w d t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw (t+(m:ℤ)) x
  rw [←ha]
  obtain ⟨b,hb⟩ := inverseFactor_fraction I hc hdk t m n a
  rw [hb]
  exact fraction_mem I w d t (n+m) b

 
def divide (t : ℤ) (m : ℕ) : piece I w d (t+(m:ℤ)) →ₗ[R] piece I w d t where
  toFun x := ⟨FilteredFraction.inverseFactor (w := w) (c := c) m*x.val,
    inverseFactor_mem I hw hc hdk t m x⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

include hwc in
lemma smul_divide (t : ℤ) (m : ℕ) (x : piece I w d (t+(m:ℤ))) :
    z^m • divide I hw hc hdk t m x =
      Submodule.inclusion (antitone I w d (by omega : t≤t+(m:ℤ))) x := by
  apply Subtype.ext
  change z^m • (FilteredFraction.inverseFactor (w := w) (c := c) m*x.val)=x.val
  rw [Algebra.smul_def,←mul_assoc,FilteredFraction.inverseFactor_mul hwc,one_mul]
end Lech.SignedFraction


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hc hdeg in
lemma restriction_fraction (t : ℤ) (n : ℕ) (a : ↥(I^(order d t n))) :
    ∃ b : ↥(I^(order e t n)),
      TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)
        (fraction I w d t n a) = fraction I v e t n b := by
  have hp : c^n ∈ I^(n*k) := by
    simpa only [pow_mul,mul_comm n k] using Ideal.pow_mem_pow hc n
  have hb : (a:R)*c^n ∈ I^(order e t n) := by
    apply Ideal.pow_le_pow_right (order_restrict_le hdeg t n)
    rw [pow_add]
    exact Ideal.mul_mem_mul a.property hp
  exact ⟨⟨(a:R)*c^n,hb⟩,TwistedLocalization.ambientTo_mk hwc a n⟩

include hw hc hdeg in
lemma restriction_mem (t : ℤ) (x : piece I w d t) :
    TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩) x ∈
      piece I v e t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw t x
  obtain ⟨b,hb⟩ := restriction_fraction I hc hwc hdeg t n a
  rw [←ha,hb]
  exact fraction_mem I v e t n b
end Lech.SignedFraction


namespace Lech.SignedCech
section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

abbrev term (t : ℤ) (s : Finset (Fin h)) :
    Submodule R (LocalizationCech.ambient z s) :=
  SignedFraction.piece I (GradedChart.denominator z s) s.card t

include hz in
lemma restriction_mem (t : ℤ) {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : term I z t s) :
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd z hsv) x ∈ term I z t v :=
  SignedFraction.restriction_mem I (FilteredCech.denominator_mem I z hz s)
    (FilteredCech.denominator_mem I z hz (v\s)) (GradedChart.denominator_mul_sdiff z hsv)
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
def divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t : ℤ) (m : ℕ) :
    term I z (t+(m:ℤ)) s →ₗ[R] term I z t s := by
  classical
  exact SignedFraction.divide I (FilteredCech.denominator_mem I z hz s)
    (FilteredCech.denominator_mem I z hz (s.erase i)) (Finset.card_erase_add_one hi) t m

lemma smul_divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t : ℤ) (m : ℕ)
    (x : term I z (t+(m:ℤ)) s) :
    z i ^ m • divide I z hz i hi t m x =
      Submodule.inclusion (SignedFraction.antitone I _ _ (by omega : t ≤ t+(m:ℤ))) x := by
  classical
  apply SignedFraction.smul_divide
  exact Finset.mul_prod_erase s z hi
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

 

def intersectionHomotopy (t : ℤ) (n : ℕ) (hn : 0<n) (a : Fin n → Fin h) :
    Homotopy (termTensorMap F (ModuleCat.of R (term I z (t+(m:ℤ)) (ActualCech.intersection a)))
      (ModuleCat.ofHom (Submodule.inclusion (SignedFraction.antitone I _ _ (by omega : t ≤ t+(m:ℤ)))))) 0 := by
  let i : Fin h := a ⟨0,hn⟩
  have hi : i ∈ ActualCech.intersection a := (ActualCech.mem_intersection a i).mpr ⟨⟨0,hn⟩,rfl⟩
  apply tensorDivisionHomotopy F (z i ^ m)
    (ModuleCat.ofHom (divide I z hz i hi t m)) _ _ (H i)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact smul_divide I z hz i hi t m x

end Lech.SignedCech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]

instance perfectIntegral : Algebra.IsIntegral A (PerfectClosure A p) where
  isIntegral x := by
    obtain ⟨n,a,ha⟩ := IsPRadical.pow_mem (PerfectClosure.of A p) p x
    apply IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n)
    rw [← ha]
    exact isIntegral_algebraMap

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

lemma rootMap_shift (n d : ℕ) (a : A) :
    rootMap A p (n+d) a =
      (iterateFrobeniusEquiv (PerfectClosure A p) p d).symm (rootMap A p n a) := by
  apply (iterateFrobeniusEquiv (PerfectClosure A p) p d).injective
  rw [RingEquiv.apply_symm_apply,iterateFrobeniusEquiv_def,← map_pow]
  have ht := rootMap_transition A p n (n+d) (Nat.le_add_right n d) a
  simpa only [Nat.add_sub_cancel_left,iterateFrobenius_def] using ht

end Lech.RootTower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open CategoryTheory


namespace Lech.RootTower
open MvPowerSeries IsLocalRing
variable {σ k : Type*} [Fintype σ] [Field k] (q : ℕ) [NeZero q]
instance expandedLocal : IsLocalRing (Expanded (σ := σ) (R := k) q) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries σ k))
instance expandedLocalHom : IsLocalHom
    (algebraMap (MvPowerSeries σ k) (Expanded (σ := σ) (R := k) q)) :=
  expansion_local q

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CompleteResidueExtension
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech.ResidueCompletion
variable {T K : Type*} [CommRing T] [IsLocalRing T] [Field K]

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Algebra R T] [Module.Free R T]

lemma flat (hmax : (maximalIdeal R).map (algebraMap R T)=maximalIdeal T)
    (hNoeth : IsNoetherianRing (AdicCompletion (maximalIdeal T) T)) :
    Module.Flat R (AdicCompletion (maximalIdeal T) T) := by
  let S := AdicCompletion (maximalIdeal T) T
  have fg : (maximalIdeal T).FG := hmax ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _
  let := AdicCompletion.isLocalRing_of_fg fg
  let : IsNoetherianRing S := hNoeth
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' rfl
  have hmap : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
    calc
      (maximalIdeal R).map (algebraMap R S)=
          ((maximalIdeal R).map (algebraMap R T)).map (algebraMap T S) := by
            rw [Ideal.map_map]
            rfl
      _ = (maximalIdeal T).map (algebraMap T S) := congrArg (Ideal.map (algebraMap T S)) hmax
  apply Lech.AdicFlat.flat_of_free_dense (T:=T) (maximalIdeal R)
  · exact Lech.AdicFlat.completion_dense _ _ hmax fg
  · exact Lech.AdicFlat.completion_contract _ _ hmax fg
  · intro J
    let : Module.Finite R J := Module.Finite.iff_fg.mpr (Ideal.fg_of_isNoetherianRing J)
    let : Module.Finite S (S ⊗[R] J) := inferInstance
    exact IsHausdorff.of_map (I:=maximalIdeal R) (J:=maximalIdeal S) hmap.le
end Lech.ResidueCompletion

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorConductor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorConductor

section Map
variable {D R M N X : Type*} [CommRing D] [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup X]
  [Module D M] [Module D N] [Module D X]
  [Module R M] [Module R N] [SMulCommClass D R M] [SMulCommClass D R N]

def mapLeft (f : M →ₗ[D] N) (hf : ∀ (r : R) x, f (r • x) = r • f x) :
    M ⊗[D] X →ₗ[R] N ⊗[D] X where
  __ := (f.rTensor X).toAddHom
  map_smul' r t := by
    induction t using OAI.tensorInductionOn with
    | tmul m x => simp [TensorProduct.smul_tmul', hf]
    | add x y hx hy =>
      change (f.rTensor X) (r • (x + y)) = r • ((f.rTensor X) (x + y))
      rw [smul_add, map_add, map_add, smul_add]
      exact congrArg₂ (·+·) hx hy

@[simp] lemma mapLeft_tmul (f : M →ₗ[D] N) (hf : ∀ (r : R) x, f (r • x) = r • f x)
    (m : M) (x : X) : mapLeft f hf (m ⊗ₜ x) = f m ⊗ₜ x := rfl
end Map

section Conductor
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) (hf : ∀ d : D, algebraMap D C d ∈ B)

variable [Algebra D B] [IsScalarTower D B C]

variable (M : Type*) [AddCommGroup M] [Module D M]

def inclusion : B ⊗[D] M →ₗ[R] C ⊗[D] M :=
  mapLeft ((Algebra.linearMap B C).restrictScalars D)
    (fun _ _ => rfl)

@[simp] lemma inclusion_tmul (b : B) (m : M) :
    inclusion (D := D) B M (b ⊗ₜ m) = (b : C) ⊗ₜ m := rfl

def conductor (g : R) (hg : ∀ c : C, g • c ∈ B) :
    C ⊗[D] M →ₗ[R] B ⊗[D] M :=
  mapLeft ((Lech.Conductor.linearMap B g hg).restrictScalars D) (by
    intro r c
    apply Subtype.ext
    exact smul_comm g r c)

end Conductor
end Lech.TensorConductor

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorPushout
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open TensorProduct

namespace Lech.TensorConductor
variable {D R M N X : Type*} [CommRing D] [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup X]
  [Module D M] [Module D N] [Module D X]
  [Module R M] [Module R N] [SMulCommClass D R M] [SMulCommClass D R N]
def congrLeft (e : M ≃ₗ[D] N) (he : ∀ (r : R) x, e (r • x) = r • e x) :
    M ⊗[D] X ≃ₗ[R] N ⊗[D] X where
  __ := (TensorProduct.congr e (LinearEquiv.refl D X)).toAddEquiv
  map_smul' r x := (mapLeft e.toLinearMap he).map_smul r x
end Lech.TensorConductor

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexConductor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.TensorConductor
universe u
variable {D R C : Type u} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) [Algebra D B] [IsScalarTower D B C]

def stageComplex (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex _).obj
    (((ModuleCat.extendScalars (algebraMap D B)).mapHomologicalComplex _).obj F)

def ambientComplex (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).obj
    (((ModuleCat.extendScalars (algebraMap D C)).mapHomologicalComplex _).obj F)

def complexInclusion (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    stageComplex B F ⟶ ambientComplex (R := R) (C := C) F := by
  have hc := IsScalarTower.algebraMap_eq D B C
  let fB := algebraMap D B
  let fC := algebraMap D C
  letI : Algebra D B := fB.toAlgebra
  letI : Algebra D C := fC.toAlgebra
  letI : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' hc
  refine { f := fun i => ?_, comm' := ?_ }
  · let X := (stageComplex B F).X i
    let Y := (ambientComplex (R := R) (C := C) F).X i
    letI : Module R X := X.isModule
    letI : Module R Y := Y.isModule
    refine ModuleCat.ofHom (X := X) (Y := Y) (show X →ₗ[R] Y from
      { __ := (inclusion (D := D) B (F.X i)).toAddHom, map_smul' := ?_ })
    intro r x
    change B ⊗[D] (F.X i) at x
    change inclusion (D := D) B (F.X i) ((algebraMap R B r) • (x : B ⊗[D] (F.X i))) =
      (algebraMap R C r) • inclusion (D := D) B (F.X i) x
    simpa only [IsScalarTower.algebraMap_smul] using
      (inclusion (D := D) B (F.X i)).map_smul r x
  · intro i j hij
    apply ModuleCat.hom_ext
    ext x
    induction x using OAI.tensorInductionOn with
    | tmul b x => rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (·+·) hx hy).trans (map_add _ x y).symm)

def complexRetreat (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (g : R) (hg : ∀ c : C,g • c∈B) :
    ambientComplex (R := R) (C := C) F ⟶ stageComplex B F := by
  have hc := IsScalarTower.algebraMap_eq D B C
  let fB := algebraMap D B
  let fC := algebraMap D C
  letI : Algebra D B := fB.toAlgebra
  letI : Algebra D C := fC.toAlgebra
  letI : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' hc
  refine { f := fun i => ?_, comm' := ?_ }
  · let X := (ambientComplex (R := R) (C := C) F).X i
    let Y := (stageComplex B F).X i
    letI : Module R X := X.isModule
    letI : Module R Y := Y.isModule
    refine ModuleCat.ofHom (X := X) (Y := Y) (show X →ₗ[R] Y from
      { __ := (conductor (D := D) B (F.X i) g hg).toAddHom, map_smul' := ?_ })
    intro r x
    change C ⊗[D] (F.X i) at x
    change conductor (D := D) B (F.X i) g hg ((algebraMap R C r) • (x : C ⊗[D] (F.X i))) =
      (algebraMap R B r) • conductor (D := D) B (F.X i) g hg x
    simpa only [IsScalarTower.algebraMap_smul] using
      (conductor (D := D) B (F.X i) g hg).map_smul r x
  · intro i j hij
    apply ModuleCat.hom_ext
    ext x
    induction x using OAI.tensorInductionOn with
    | tmul c x => rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (·+·) hx hy).trans (map_add _ x y).symm)

end Lech.TensorConductor

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {ι : Type*} (c : ComplexShape ι)

def complexQuotientNat : 𝟭 (HomologicalComplex (ModuleCat.{u} R) c) ⟶
    (quotientFunctor I).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) c).inv ≫
    (quotientNat I).mapHomologicalComplex c

lemma complexQuotientNat_f (K : HomologicalComplex (ModuleCat.{u} R) c) (q : ι) :
    ((complexQuotientNat I c).app K).f q=(quotientNat I).app (K.X q) := by
  change (𝟙 (K.X q)) ≫ (quotientNat I).app (K.X q)=_
  exact Category.id_comp _

variable {κ : Type*} (d : ComplexShape κ)
def bicomplexQuotientNat :
    𝟭 (HomologicalComplex (HomologicalComplex (ModuleCat.{u} R) c) d) ⟶
      ((quotientFunctor I).mapHomologicalComplex c).mapHomologicalComplex d :=
  (Functor.mapHomologicalComplexIdIso (HomologicalComplex (ModuleCat.{u} R) c) d).inv ≫
    (complexQuotientNat I c).mapHomologicalComplex d

lemma bicomplexQuotientNat_f (K : HomologicalComplex (HomologicalComplex (ModuleCat.{u} R) c) d)
    (p : κ) (q : ι) :
    (((bicomplexQuotientNat I c d).app K).f p).f q=(quotientNat I).app ((K.X p).X q) := by
  change ((𝟙 (K.X p)) ≫ (complexQuotientNat I c).app (K.X p)).f q=_
  rw [Category.id_comp,complexQuotientNat_f]
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichSpan
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]



variable {n : ℕ} {f : R[X]}

instance powerIndexFintype (n : ℕ) : Fintype (PowerIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin (n+1) × PowerIndex n))



end Lech.UniversalSplitting

end

end OAI
end


