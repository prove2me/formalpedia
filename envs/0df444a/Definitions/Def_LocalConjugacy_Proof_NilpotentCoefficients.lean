-- Prove2me | Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
-- name    : LocalConjugacy_Proof_NilpotentCoefficients
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:41:09.454819+00:00
-- url     : https://prove2.me/theorems/ed93e667-6034-4ab8-948a-05e758afd917
-- title:
--   Primary factors of nilpotent coefficients
-- statement:
--   The Sylow primary factors of a finite nilpotent coefficient group, their characteristic property, their commuting product equivalence, and the induced continuous actions on the factors.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace NilpotentCoefficients

variable {N : Type*} [Group N] [Finite N] [Group.IsNilpotent N]

abbrev PrimeIndex (N : Type*) := {p : ℕ // p ∈ (Nat.card N).primeFactors}

instance primeFact (p : PrimeIndex N) : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩

noncomputable def primarySylow (p : PrimeIndex N) : Sylow p.val N := default

noncomputable abbrev Factor (N : Type*) [Group N] (p : PrimeIndex N) :=
  (primarySylow p).toSubgroup

instance factorCharacteristic (p : PrimeIndex N) : (Factor N p).Characteristic :=
  Sylow.characteristic_of_normal (primarySylow p) inferInstance

theorem factors_commute : Pairwise fun p q : PrimeIndex N =>
    ∀ x y : N, x ∈ Factor N p → y ∈ Factor N q → Commute x y := by
  intro p q hpq
  apply Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
  exact IsPGroup.disjoint_of_ne p.val q.val (fun he => hpq (Subtype.ext he)) _ _
    (primarySylow p).isPGroup' (primarySylow q).isPGroup'

/-- The finite nilpotent coefficient group is the product of its primary
subgroups. This follows Mathlib's `Sylow.directProductOfNormal` construction,
with one chosen Sylow per prime so the component action is explicit. -/
noncomputable def productEquiv : (∀ p : PrimeIndex N, Factor N p) ≃* N := by
  classical
  let φ := Subgroup.noncommPiCoprod (factors_commute (N := N))
  apply MulEquiv.ofBijective φ
  letI := Fintype.ofFinite N
  letI (p : PrimeIndex N) := Fintype.ofFinite (Factor N p)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order factors_commute
    intro p q hpq
    simpa only [Nat.card_eq_fintype_card] using IsPGroup.coprime_card_of_ne p.val q.val (fun he => hpq (Subtype.ext he)) _ _
      (primarySylow p).isPGroup' (primarySylow q).isPGroup'
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card (∀ p : PrimeIndex N, Factor N p) = ∏ p : PrimeIndex N, Nat.card (Factor N p) := Nat.card_pi
      _ = ∏ p : PrimeIndex N, p.val ^ (Nat.card N).factorization p.val := by
        congr 1 with p
        exact (primarySylow p).card_eq_multiplicity
      _ = ∏ p ∈ (Nat.card N).primeFactors, p ^ (Nat.card N).factorization p :=
        Finset.prod_finset_coe (fun p : ℕ => p ^ (Nat.card N).factorization p) (Nat.card N).primeFactors
      _ = (Nat.card N).factorization.prod (· ^ ·) := rfl
      _ = Nat.card N := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

variable {J : Type*} [Group J] [MulDistribMulAction J N]

@[instance_reducible] noncomputable def factorAction (p : PrimeIndex N) :
    MulDistribMulAction J (Factor N p) :=
  MulDistribMulAction.compHom (Factor N p)
    ((MulAut.characteristic (Factor N p)).comp (MulDistribMulAction.toMulAut J N))

attribute [local instance] factorAction



variable [TopologicalSpace J] [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul J N]

instance factorContinuousSMul (p : PrimeIndex N) : ContinuousSMul J (Factor N p) where
  continuous_smul := ((continuous_fst : Continuous (Prod.fst : J × Factor N p → J)).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

end NilpotentCoefficients



end LocalConjugacy

end LocalConjugacy.Proof

end


