-- Prove2me | Definitions.Def_OAIQ075A004
-- name    : OAIQ075A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:56:41.780575+00:00
-- url     : https://prove2.me/theorems/14623ec5-fb8f-4207-8faa-6d57868b9054
-- title:
--   Definitions bundle OAIQ075A004 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 484 declarations of OpenAI's Lean: 148 definitions, 17 inductive types or structures, 34 instances and 285 theorems. The definitions and types are `OAI.Generator.Tracial.algebraInclusion`, `OAI.Generator.bicommutantStar`, `OAI.Generator.bicommutantVonNeumann`, `OAI.HochschildCStarQuotient.StarClosed`, `OAI.HochschildCStarQuotient.starSubalgebra`, `OAI.HochschildDiffuse.NoMinimalProjections`, `OAI.HochschildDomination.PreHilbert`, `OAI.HochschildFinitePhase.character`, `OAI.HochschildFinitePhase.frequency`, `OAI.HochschildNormalPart.SharedHilbertFactor`, `OAI.HochschildPatching.BoundedWord`, `OAI.HochschildPatching.IntAtom`, `OAI.HochschildPatching.LinearLabel`, `OAI.HochschildPatching.ProductTaylor.differenceTerms`, `OAI.HochschildPatching.ProductTaylor.linearTerms`, `OAI.HochschildPatching.ProductTaylor.oldProduct`, `OAI.HochschildPatching.ProductTaylor.quadraticTerms`, `OAI.HochschildPatching.ProductTaylor.totalProduct`, `OAI.HochschildPatching.ShortTail`, `OAI.HochschildPatching.WordAtom`, `OAI.HochschildPatching.admissibleIntTail`, `OAI.HochschildPatching.admissibleTail`, `OAI.HochschildPatching.coeffNumber`, `OAI.HochschildPatching.evalSequence`, `OAI.HochschildPatching.expBudget`, `OAI.HochschildPatching.exponentCode`, `OAI.HochschildPatching.linearPower`, `OAI.HochschildPatching.mapAtom`, `OAI.HochschildPatching.mapUnitary`, `OAI.HochschildPatching.patchRate`, `OAI.HochschildPatching.patchTolerance`, `OAI.HochschildPatching.signedExponent`, `OAI.HochschildPatching.toIntAtom`, `OAI.HochschildPatching.wordCoeffNumber`, `OAI.HochschildPatching.wordProduct`, `OAI.HochschildRootPhase.character`, `OAI.HochschildUltrapower.constantSequence`, `OAI.HochschildUltrapower.sequenceTrace`, `OAI.IsUnital`, `OAI.IsUnital.toNormedRing` and 125 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_AlternatingMoments`, `BoundedHochschild_CStarQuotients`, `BoundedHochschild_DiffuseProjections`, `BoundedHochschild_FiniteMoments`, `BoundedHochschild_FinitePhases`, `BoundedHochschild_HarmonicSums`, `BoundedHochschild_IncrementalPatching`, `BoundedHochschild_MatrixSystems`, `BoundedHochschild_MixedWords`, `BoundedHochschild_PartialIsometries`, `BoundedHochschild_PartialUnitaries`, `BoundedHochschild_ProductTaylor`, `BoundedHochschild_RelativeQuantization`, `BoundedHochschild_TracialModulus`, `BoundedHochschild_UltrapowerMoments`, `BoundedHochschild_Ultrapowers`, `FactorGeneration_FunctionalLimits`, `FactorGeneration_MatrixSequence`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `KadisonSimilarity_Derivation_CyclicDecomposition`, `KadisonSimilarity_Derivation_CyclicFactorization`, `KadisonSimilarity_Derivation_RectangularDerivations`, `KadisonSimilarity_Derivation_TracialCornerCyclicity`, `KadisonSimilarity_FreeProduct_ActualArcCompression`, `KadisonSimilarity_FreeProduct_ArcFourier`, `KadisonSimilarity_FreeProduct_DihedralCutMoments`, `KadisonSimilarity_FreeProduct_DihedralFourier`, `KadisonSimilarity_FreeProduct_DihedralWordIsometries`, `KadisonSimilarity_FreeProduct_DihedralWordOrthogonality`, `KadisonSimilarity_FreeProduct_EvenAlternatingWords`, `KadisonSimilarity_FreeProduct_FreeDihedral`, `KadisonSimilarity_FreeProduct_FreeExpectation`, `KadisonSimilarity_FreeProduct_FreePairWords`, `KadisonSimilarity_FreeProduct_FreeProductAutomorphisms`, `KadisonSimilarity_FreeProduct_FreeProductMatrixExtension`, `KadisonSimilarity_FreeProduct_FreeWordHilbert`, `KadisonSimilarity_FreeProduct_FreeWordInnerProducts`, `KadisonSimilarity_FreeProduct_GeneratedWordDensity`, `KadisonSimilarity_FreeProduct_HaarCornerLetters`, `KadisonSimilarity_FreeProduct_OrthogonalWordLevels`, `KadisonSimilarity_FreeProduct_ReducedWordModel`, `KadisonSimilarity_FreeProduct_ScalarFreeMonotone`, `KadisonSimilarity_FreeProduct_SpectralArc`, `KadisonSimilarity_FreeProduct_SymmetryWordRange`, `KadisonSimilarity_FreeProduct_TracialDihedralColumns`, `KadisonSimilarity_FreeProduct_TracialSymmetryDilation`, `KadisonSimilarity_FreeProduct_TracialSymmetryExtraction`, `KadisonSimilarity_Hyperreflexivity`, `KadisonSimilarity_OperatorAlgebra`, `KadisonSimilarity_Representation_Amplification`, `KadisonSimilarity_Representation_CStarCorner`, `KadisonSimilarity_Representation_ClosedFamilySpan`, `KadisonSimilarity_Representation_DenseFamilyIsometry`, `KadisonSimilarity_Representation_GeneratedEmbeddings`, `KadisonSimilarity_Representation_OrthogonalColumns`, `KadisonSimilarity_Representation_SquareArrayPadding`, `KadisonSimilarity_Similarity_CompletelyBounded`, `KadisonSimilarity_Tensor_EndpointBounds`, `KadisonSimilarity_Tensor_EndpointTensors`, `KadisonSimilarity_Tensor_InvariantForms`, `KadisonSimilarity_Tensor_InvariantIntertwiners`, `KadisonSimilarity_Tensor_TensorDensity`, `KadisonSimilarity_Tensor_TensorPermutations`, `KadisonSimilarity_Tensor_TensorSlices`, `KadisonSimilarity_Tensor_TensorWords`, `KadisonSimilarity_Tracial_FullColumnTheorem`, `KadisonSimilarity_Tracial_FullColumns`, `KadisonSimilarity_Tracial_GNSTracialGeometry`, `KadisonSimilarity_Tracial_MatrixConjugateAutomorphism`, `KadisonSimilarity_Tracial_MatrixTracialGNS`, `KadisonSimilarity_Tracial_MatrixUnitFamilies`, `KadisonSimilarity_Tracial_TracialCornerExpectations`, `KadisonSimilarity_Tracial_TracialCornerTransport`, `KadisonSimilarity_Tracial_TracialExpectations`, `KadisonSimilarity_Tracial_TracialHalfProjectionData`, `KadisonSimilarity_Tracial_TracialInputTransport`, `KadisonSimilarity_Tracial_TracialMatrixRealization`, `KadisonSimilarity_Tracial_TracialMatrixTower`, `KadisonSimilarity_Tracial_TracialSubalgebraModels`, `KadisonSimilarity_Tracial_TracialUltrapowerHom`, `KadisonSimilarity_Tracial_UltrapowerConstants`, `NuclearUltrapower_HilbertUltraproduct`, `TracialCohomology_DominatedFactorization`, `TracialCohomology_HilbertFactorization`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A007`, `OAIQ075A009`, `OAIQ075A010`, `OAIQ075A011` and `OAIQ075A012`; the statement `OAI_KadisonSimilarity_TracialCornerGeometry_rightSupportInput_of_normal_range`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity

section
-- module Solutions.OAIQ075_KS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- d13f23b's `NonUnitalStarRingHom.ofClass`: the bundled hom of a hom class (Kadison commutator
FreeSymmetry10, oaiq-039). `StarRing` rather than bare `Star`, so the `Star` instances agree with those of
`NonUnitalStarRingHom.map_le_map_of_map_star` (MatrixVectorTrace, `CStarMatrix`). -/
def nonUnitalStarRingHomOfClass {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [StarRing R] [StarRing S] [FunLike F R S] [NonUnitalRingHomClass F R S] [StarHomClass F R S] (f : F) :
    R →⋆ₙ+* S :=
  { (f : R →ₙ+* S) with map_star' := map_star f }
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
/-- Mathlib d13f23b's `IsUnital`: a non-unital ring with a two-sided identity element (Kadison similarity,
oaiq-075). -/
class IsUnital (A : Type*) [NonUnitalRing A] : Prop where
  exists_one : ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a

/-- d13f23b's `IsUnital.toNormedRing`: a non-unital normed ring with an identity is a normed ring. -/
@[instance_reducible]
noncomputable def IsUnital.toNormedRing {A : Type*} [NonUnitalNormedRing A] [h : IsUnital A] :
    NormedRing A :=
  let e := h.exists_one.choose
  have he := h.exists_one.choose_spec
  letI : One A := ⟨e⟩
  letI : NatCast A := ⟨Nat.unaryCast⟩
  letI : IntCast A := ⟨Int.castDef⟩
  { ‹NonUnitalNormedRing A› with
    one_mul := fun a => (he a).1
    mul_one := fun a => (he a).2
    natCast_zero := rfl
    natCast_succ := fun n => rfl
    intCast_ofNat := fun n => rfl
    intCast_negSucc := fun n => rfl }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_HarmonicSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic sine estimates, Fourier windows, tracial Hilbert spaces and unitary power rigidity. -/

noncomputable section


namespace HochschildRigidity
open Finset


section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
lemma preGNS_norm_one (h1 : τ 1 = 1) : ‖τ.toPreGNS 1‖ = 1 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS 1))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at h
  nlinarith [norm_nonneg (τ.toPreGNS 1)]

open Finset
open scoped BigOperators

end TraceHilbertSpace

end HochschildRigidity
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CStarQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C-star quotients by star-closed ideals. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric

namespace HochschildCStarQuotient
variable {A : Type*} [CStarAlgebra A]

class StarClosed (I : Ideal A) : Prop where
  star_mem {x : A} : x ∈ I → star x ∈ I

variable (I : Ideal A) [I.IsTwoSided]

lemma norm_mk_le (x : A) : ‖Ideal.Quotient.mk I x‖ ≤ ‖x‖ :=
  Submodule.Quotient.norm_mk_le I x

lemma norm_mk_lt (x : A ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, Ideal.Quotient.mk I a = x ∧ ‖a‖ < ‖x‖ + ε :=
  QuotientAddGroup.exists_norm_mk_lt x hε

instance quotientSeminormedRing : SeminormedRing (A ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := norm_mk_lt I x h₁, norm_mk_lt I y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le I a]⟩
      ⟨by linarith, by linarith [norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (norm_mk_le I (a*b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance quotientNormedRing [IsClosed (I : Set A)] : NormedRing (A ⧸ I) :=
  { quotientSeminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

instance quotientNormedAlgebra : NormedAlgebra ℂ (A ⧸ I) :=
  { Submodule.Quotient.normedSpace I ℂ, Ideal.Quotient.algebra ℂ with }

variable [StarClosed I]

instance quotientStar : Star (A ⧸ I) where
  star := Quotient.map' star fun a b hab => by
    rw [Submodule.quotientRel_def] at hab ⊢
    simpa only [star_sub] using StarClosed.star_mem (I := I) hab

@[simp] lemma star_mk (a : A) : star (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a) := rfl

instance quotientStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_mul, star_mk, star_mul]
  star_add x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_add, star_mk, star_add]

instance quotientStarModule : StarModule ℂ (A ⧸ I) where
  star_smul r x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I (star (r • a)) = Ideal.Quotient.mk I (star r • star a)
    rw [star_smul]


def starSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  mul_mem' := fun _ hy => I.mul_mem_left _ hy
  smul_mem' := fun r x hx => by
    change r • x ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hx
  star_mem' := StarClosed.star_mem

instance starSubalgebra_closed [h : IsClosed (I : Set A)] :
    IsClosed (starSubalgebra I : Set A) := h

omit [I.IsTwoSided] in
 
lemma exists_cut [IsClosed (I : Set A)] (b : A) (hb : b ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : A, e ∈ I ∧ star e = e ∧ ‖1-e‖ ≤ 1 ∧ ‖b-b*e‖ < ε := by
  let oa := CStarAlgebra.spectralOrder A
  let osa := CStarAlgebra.spectralOrderedRing A
  let S := starSubalgebra I
  let os := CStarAlgebra.spectralOrder S
  let oss := CStarAlgebra.spectralOrderedRing S
  let b' : S := ⟨b,hb⟩
  have hi := CStarAlgebra.increasingApproximateUnit S
  have hd : ∀ᶠ e : S in CStarAlgebra.approximateUnit S, ‖b'-b'*e‖ < ε := by
    have ht := ((tendsto_const_nhds (x := b')).sub (hi.tendsto_mul_left b')).norm
    simpa only [sub_self, norm_zero] using ht.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hε))
  obtain ⟨e,he₀,he₁,he₂⟩ := (hi.eventually_nonneg.and (hi.eventually_norm.and hd)).exists
  have hepos : 0 ≤ (e:A) := by
    exact (@NonUnitalStarRingHom.map_le_map_of_map_star S A _ os _ oss _ oa _ osa
      (OAI.nonUnitalStarRingHomOfClass (NonUnitalStarSubalgebraClass.subtype S)) 0 e he₀)
  have henorm : ‖(e:A)‖ ≤ 1 := he₁
  have heone : (e:A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hepos).mp henorm
  refine ⟨e,e.property,hepos.isSelfAdjoint.star_eq,?_,he₂⟩
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1-(e:A)) (sub_nonneg.mpr heone)).mpr
    (sub_le_self _ hepos)

lemma quotient_cstar [IsClosed (I : Set A)] (x : A ⧸ I) :
    ‖x‖ * ‖x‖ ≤ ‖star x*x‖ := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [star_mk, ← map_mul]
  apply QuotientAddGroup.le_norm_iff.mpr
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb : t-star a*a ∈ I := (Ideal.Quotient.eq).mp ht
  obtain ⟨e,he,hes,hen,heb⟩ := exists_cut I (t-star a*a) hb hε
  have hqe : Ideal.Quotient.mk I e = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr he
  have hx : Ideal.Quotient.mk I (a*(1-e)) = Ideal.Quotient.mk I a := by
    simp only [map_mul,map_sub,map_one,hqe,sub_zero,mul_one]
  calc
    ‖Ideal.Quotient.mk I a‖ * ‖Ideal.Quotient.mk I a‖ ≤ ‖a*(1-e)‖ * ‖a*(1-e)‖ := by
      apply mul_self_le_mul_self (norm_nonneg _)
      rw [← hx]
      exact norm_mk_le I _
    _ = ‖(1-e)*(star a*a)*(1-e)‖ := by
      rw [← CStarRing.norm_star_mul_self]
      simp only [star_mul,star_sub,star_one,hes,mul_assoc]
    _ = ‖(1-e)*t*(1-e)-(1-e)*((t-star a*a)-(t-star a*a)*e)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖(1-e)*t*(1-e)‖ + ‖(1-e)*((t-star a*a)-(t-star a*a)*e)‖ := norm_sub_le _ _
    _ ≤ ‖t‖ + ε := by
      apply add_le_add
      · calc
          _ ≤ ‖1-e‖*‖t‖*‖1-e‖ := (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ 1*‖t‖*1 := by gcongr
          _ = _ := by ring
      · calc
          _ ≤ ‖1-e‖*‖(t-star a*a)-(t-star a*a)*e‖ := norm_mul_le _ _
          _ ≤ 1*‖(t-star a*a)-(t-star a*a)*e‖ :=
            mul_le_mul_of_nonneg_right hen (norm_nonneg _)
          _ ≤ ε := by simpa using heb.le

instance quotientCStarAlgebra [IsClosed (I : Set A)] : CStarAlgebra (A ⧸ I) where
  norm_mul_self_le := quotient_cstar I

end HochschildCStarQuotient
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TracialModulus
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded-ball continuity, tracial null spaces and quotient seminorms. -/

noncomputable section


namespace TracialUltrapower
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

section Modulus
variable {A E : Type*} [SeminormedAddCommGroup A] [SeminormedAddCommGroup E]


def BallModulus (q : A → E) (R : A → A) : Prop :=
  ∀ r : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
    ‖x‖ ≤ r → ‖q x‖ < δ → ‖q (R x)‖ < ε


theorem BallModulus.map_tendsto {q : A → E} {R : A → A} (h : BallModulus q R)
    {ι : Type*} {l : Filter ι} {x : ι → A} {r : ℝ}
    (hx : ∀ᶠ j in l, ‖x j‖ ≤ r)
    (hlim : Tendsto (fun j => ‖q (x j)‖) l (𝓝 0)) :
    Tendsto (fun j => ‖q (R (x j))‖) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := h r ε hε
  filter_upwards [hx, hlim.eventually_lt_const hδ] with j hj hjq
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hmod (x j) hj hjq

end Modulus

section NullSubmodule
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →ₗ[ℂ] E) (ω : Filter ℕ)

 

def nullSubmodule : Submodule ℂ (ℕ →ᵇ A) where
  carrier := {x | Tendsto (fun j => q (x j)) ω (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds (x := (0 : E))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, BoundedContinuousFunction.add_apply, map_add, add_zero] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, BoundedContinuousFunction.smul_apply, map_smul, smul_zero] using hx.const_smul c

@[simp] theorem mem_nullSubmodule (x : ℕ →ᵇ A) :
    x ∈ nullSubmodule q ω ↔ Tendsto (fun j => ‖q (x j)‖) ω (𝓝 0) := by
  change Tendsto (fun j => q (x j)) ω (𝓝 0) ↔ _
  exact tendsto_zero_iff_norm_tendsto_zero

theorem nullSubmodule_map_invariant (R : A →L[ℂ] A) (hR : BallModulus q R) :
    nullSubmodule q ω ≤ (nullSubmodule q ω).comap
      (R.compLeftContinuousBounded ℕ).toLinearMap := by
  intro x hx
  rw [Submodule.mem_comap, mem_nullSubmodule]
  exact hR.map_tendsto (Eventually.of_forall x.norm_coe_le_norm)
    ((mem_nullSubmodule q ω x).mp hx)

 

def quotientMap (R : A →L[ℂ] A) (hR : BallModulus q R) :
    ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) →ₗ[ℂ]
      ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) :=
  (nullSubmodule q ω).mapQ (nullSubmodule q ω)
    (R.compLeftContinuousBounded ℕ).toLinearMap (nullSubmodule_map_invariant q ω R hR)

@[simp] theorem quotientMap_mk (R : A →L[ℂ] A) (hR : BallModulus q R)
    (x : ℕ →ᵇ A) :
    quotientMap q ω R hR (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (R.compLeftContinuousBounded ℕ x) := rfl

end NullSubmodule

section ClosedNullSpace
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem isClosed_nullSubmodule (q : A →L[ℂ] E) (ω : Filter ℕ) :
    IsClosed (nullSubmodule q.toLinearMap ω : Set (ℕ →ᵇ A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change x ∈ nullSubmodule q.toLinearMap ω
  rw [mem_nullSubmodule]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : 0 < ‖q‖ + 1 := by positivity
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2 / (‖q‖ + 1))
    (by positivity)
  have hsmall : ‖q‖ * ‖x - y‖ < ε / 2 := by
    have hd : ‖x - y‖ < ε / 2 / (‖q‖ + 1) := by
      simpa only [dist_eq_norm] using hxy
    calc
      _ ≤ (‖q‖ + 1) * ‖x - y‖ := by gcongr; linarith
      _ < (‖q‖ + 1) * (ε / 2 / (‖q‖ + 1)) := mul_lt_mul_of_pos_left hd hc
      _ = _ := by field_simp
  have hy' := ((mem_nullSubmodule q.toLinearMap ω y).mp hy).eventually_lt_const
    (half_pos hε)
  filter_upwards [hy'] with j hj
  have hdiff : ‖q (x j) - q (y j)‖ < ε / 2 := by
    calc
      _ = ‖q ((x - y) j)‖ := by simp
      _ ≤ ‖q‖ * ‖(x - y) j‖ := q.le_opNorm _
      _ ≤ ‖q‖ * ‖x - y‖ := by gcongr; exact (x - y).norm_coe_le_norm j
      _ < _ := hsmall
  have hn := norm_le_norm_sub_add (q (x j)) (q (y j))
  simp only [dist_zero_right, Real.norm_eq_abs, abs_norm]
  change ‖q (x j)‖ < ε
  change ‖q (y j)‖ < ε / 2 at hj
  linarith

end ClosedNullSpace

section UltraSeminorm
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →L[ℂ] E) (ω : Ultrafilter ℕ)

 
def sequenceTwoNorm (x : ℕ →ᵇ A) : ℝ :=
  (ω : Filter ℕ).limUnder (fun j => ‖q (x j)‖)

theorem tendsto_sequenceTwoNorm (x : ℕ →ᵇ A) :
    Tendsto (fun j => ‖q (x j)‖) (ω : Filter ℕ) (𝓝 (sequenceTwoNorm q ω x)) := by
  have hbound : ∀ j, ‖q (x j)‖ ∈ Set.Icc 0 (‖q‖ * ‖x‖) := by
    intro j
    exact ⟨norm_nonneg _, (q.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j) (norm_nonneg _))⟩
  obtain ⟨a, _, ha⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 (‖q‖ * ‖x‖))).ultrafilter_le_nhds
    (ω.map (fun j => ‖q (x j)‖)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      change ∀ᶠ j in (ω : Filter ℕ), ‖q (x j)‖ ∈ Set.Icc 0 (‖q‖ * ‖x‖)
      exact Eventually.of_forall hbound)
  have ht : Tendsto (fun j => ‖q (x j)‖) (ω : Filter ℕ) (𝓝 a) := ha
  simpa only [sequenceTwoNorm, ht.limUnder_eq] using ht

theorem sequenceTwoNorm_nonneg (x : ℕ →ᵇ A) : 0 ≤ sequenceTwoNorm q ω x :=
  ge_of_tendsto' (tendsto_sequenceTwoNorm q ω x) (fun _ => norm_nonneg _)

theorem sequenceTwoNorm_eq_of_sub_mem (x y : ℕ →ᵇ A)
    (h : x - y ∈ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    sequenceTwoNorm q ω x = sequenceTwoNorm q ω y := by
  have hz : Tendsto (fun j => ‖q (x j)‖ - ‖q (y j)‖) (ω : Filter ℕ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun j => ?_) ((mem_nullSubmodule _ _ _).mp h)
    simpa only [Real.norm_eq_abs, BoundedContinuousFunction.sub_apply, map_sub,
      ContinuousLinearMap.coe_coe] using abs_norm_sub_norm_le (q (x j)) (q (y j))
  have hh := tendsto_nhds_unique
    ((tendsto_sequenceTwoNorm q ω x).sub (tendsto_sequenceTwoNorm q ω y)) hz
  exact sub_eq_zero.mp hh

 

def quotientTwoNorm : ((ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) → ℝ :=
  Quotient.lift (sequenceTwoNorm q ω) (fun x y h =>
    sequenceTwoNorm_eq_of_sub_mem q ω x y ((Submodule.quotientRel_def _).mp h))

@[simp] theorem quotientTwoNorm_mk (x : ℕ →ᵇ A) :
    quotientTwoNorm q ω (Submodule.Quotient.mk x) = sequenceTwoNorm q ω x := rfl

theorem quotientTwoNorm_eq_zero_iff
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    quotientTwoNorm q ω X = 0 ↔ X = 0 := by
  induction X using Quotient.inductionOn with
  | h x =>
    constructor
    · intro hx
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [mem_nullSubmodule]
      change sequenceTwoNorm q ω x = 0 at hx
      exact hx ▸ tendsto_sequenceTwoNorm q ω x
    · intro hx
      have hz : x ∈ nullSubmodule q.toLinearMap (ω : Filter ℕ) :=
        (Submodule.Quotient.mk_eq_zero _).mp hx
      exact tendsto_nhds_unique (tendsto_sequenceTwoNorm q ω x)
        ((mem_nullSubmodule _ _ _).mp hz)

end UltraSeminorm

end
end TracialUltrapower
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Ultrapowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial ultrapowers, quotient traces and bounded-ball maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

def sequenceTrace (x : ℕ →ᵇ A) : ℂ := limUnder (ω : Filter ℕ) (fun j => τ (x j))

end HochschildUltrapower

namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))


def constantSequence : A →⋆ₐ[ℂ] (ℕ →ᵇ A) where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

end HochschildUltrapower
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_DiffuseProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diffuse projections of prescribed trace and conjugation estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)

 

def NoMinimalProjections (M : Type*) [CStarAlgebra M] [PartialOrder M] : Prop :=
  ∀ p : M, IsStarProjection p → p ≠ 0 →
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ q ≠ p



theorem exists_half_subprojection (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ (τ q).re ≤ (τ p).re/2 := by
  obtain ⟨q,hq,hqp,hq0,hqne⟩ := hdiff p hp hp0
  by_cases ht : (τ q).re ≤ (τ p).re/2
  · exact ⟨q,hq,hqp,hq0,ht⟩
  · refine ⟨p-q,(hq.le_iff_sub hp).mp hqp,sub_le_self _ hq.nonneg,?_,?_⟩
    · intro he
      exact hqne (sub_eq_zero.mp he).symm
    · rw [map_sub,Complex.sub_re]
      linarith

 

theorem exists_small_subprojection (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ (τ q).re < ε := by
  have hrec : ∀ n : ℕ, ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧
      (τ q).re ≤ (1/2 : ℝ)^n*(τ p).re := by
    intro n
    induction n with
    | zero => exact ⟨p,hp,le_rfl,hp0,by simp only [pow_zero,one_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨q,hq,hqp,hq0,hqn⟩ := ih
      obtain ⟨r,hr,hrq,hr0,hrt⟩ := exists_half_subprojection τ hdiff hq hq0
      refine ⟨r,hr,hrq.trans hqp,hr0,?_⟩
      rw [pow_succ]
      nlinarith
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n*(τ p).re) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).mul_const (τ p).re
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨q,hq,hqp,hq0,hqn⟩ := hrec n
  exact ⟨q,hq,hqp,hq0,hqn.trans_lt hn⟩

end HochschildDiffuse

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)
  (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htr : t ≤ p-r) : r*t=0 := by
  have hpr := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]

end HochschildComparison
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

lemma projection_gns_sq {q : M} (hq : IsStarProjection q) : ‖τ.toPreGNS q‖^2=(τ q).re := by
  have ht := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS q))
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re,PositiveLinearMap.ofPreGNS_toPreGNS,
    hq.isSelfAdjoint.star_eq,hq.isIdempotentElem.eq] using ht

end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProductTaylor
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noncommutative product expansions and linear and quadratic error terms. -/

noncomputable section



 

 

 

namespace HochschildPatching
namespace ProductTaylor
variable {R : Type*} [Ring R]
def oldProduct (l : List (R × R)) : R := (l.map Prod.fst).prod
def totalProduct (l : List (R × R)) : R := (l.map (fun ab => ab.1+ab.2)).prod
@[simp] lemma old_nil : oldProduct ([] : List (R × R))=1 := rfl
@[simp] lemma total_nil : totalProduct ([] : List (R × R))=1 := rfl
@[simp] lemma old_cons (ab : R × R) (l : List (R × R)) : oldProduct (ab::l)=ab.1*oldProduct l := rfl
@[simp] lemma total_cons (ab : R × R) (l : List (R × R)) : totalProduct (ab::l)=(ab.1+ab.2)*totalProduct l := rfl

def differenceTerms : List (R × R) → List R
  | [] => []
  | ab::l => ab.2*totalProduct l :: (differenceTerms l).map (fun x => ab.1*x)
def linearTerms : List (R × R) → List R
  | [] => []
  | ab::l => ab.2*oldProduct l :: (linearTerms l).map (fun x => ab.1*x)
def quadraticTerms : List (R × R) → List R
  | [] => []
  | ab::l => (differenceTerms l).map (fun x => ab.2*x) ++ (quadraticTerms l).map (fun x => ab.1*x)

lemma sum_map_mul_left (a : R) (l : List R) : (l.map (fun x => a*x)).sum=a*l.sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

lemma total_eq_old_add_difference (l : List (R × R)) : totalProduct l=oldProduct l+(differenceTerms l).sum := by
  induction l with
  | nil => simp [differenceTerms]
  | cons ab l ih =>
    simp only [total_cons,old_cons,differenceTerms,List.sum_cons,sum_map_mul_left]
    rw [ih]
    noncomm_ring
lemma total_eq_old_add_linear_add_quadratic (l : List (R × R)) :
    totalProduct l=oldProduct l+(linearTerms l).sum+(quadraticTerms l).sum := by
  induction l with
  | nil => simp [linearTerms,quadraticTerms]
  | cons ab l ih =>
    simp only [total_cons,old_cons,linearTerms,quadraticTerms,List.sum_cons,List.sum_append,sum_map_mul_left]
    have hd := total_eq_old_add_difference l
    have ht : (differenceTerms l).sum=(linearTerms l).sum+(quadraticTerms l).sum := by
      rw [ih] at hd
      rw [add_assoc] at hd
      exact (add_left_cancel hd).symm
    rw [ht,ih]
    noncomm_ring

lemma mem_differenceTerms {l : List (R × R)} {x : R} (hx : x ∈ differenceTerms l) :
    ∃ pre ab post, l=pre++ab::post ∧ x=oldProduct pre*ab.2*totalProduct post := by
  induction l generalizing x with
  | nil => simp only [differenceTerms,List.not_mem_nil] at hx
  | cons ab l ih =>
    simp only [differenceTerms,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl|⟨y,hy,rfl⟩
    · exact ⟨[],ab,l,rfl,by simp⟩
    · obtain ⟨pre,cd,post,hr,rfl⟩ := ih hy
      exact ⟨ab::pre,cd,post,by simp only [List.cons_append,hr],by simp only [old_cons,mul_assoc]⟩
lemma mem_linearTerms {l : List (R × R)} {x : R} (hx : x ∈ linearTerms l) :
    ∃ pre ab post, l=pre++ab::post ∧ x=oldProduct pre*ab.2*oldProduct post := by
  induction l generalizing x with
  | nil => simp only [linearTerms,List.not_mem_nil] at hx
  | cons ab l ih =>
    simp only [linearTerms,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl|⟨y,hy,rfl⟩
    · exact ⟨[],ab,l,rfl,by simp⟩
    · obtain ⟨pre,cd,post,hr,rfl⟩ := ih hy
      exact ⟨ab::pre,cd,post,by simp only [List.cons_append,hr],by simp only [old_cons,mul_assoc]⟩
lemma mem_quadraticTerms {l : List (R × R)} {x : R} (hx : x ∈ quadraticTerms l) :
    ∃ pre ab middle cd post, l=pre++ab::(middle++cd::post) ∧
      x=oldProduct pre*ab.2*oldProduct middle*cd.2*totalProduct post := by
  induction l generalizing x with
  | nil => simp only [quadraticTerms,List.not_mem_nil] at hx
  | cons ab l ih =>
    simp only [quadraticTerms,List.mem_append,List.mem_map] at hx
    rcases hx with ⟨y,hy,rfl⟩|⟨y,hy,rfl⟩
    · obtain ⟨middle,cd,post,hr,rfl⟩ := mem_differenceTerms hy
      exact ⟨[],ab,middle,cd,post,by simp only [List.nil_append,hr],by simp only [old_nil,one_mul,mul_assoc]⟩
    · obtain ⟨pre,cd,middle,ef,post,hr,rfl⟩ := ih hy
      exact ⟨ab::pre,cd,middle,ef,post,by simp only [List.cons_append,hr],by simp only [old_cons,mul_assoc]⟩

lemma differenceTerms_length (l : List (R × R)) : (differenceTerms l).length=l.length := by
  induction l with
  | nil => rfl
  | cons ab l ih => simp only [differenceTerms,List.length_cons,List.length_map,ih]
lemma linearTerms_length (l : List (R × R)) : (linearTerms l).length=l.length := by
  induction l with
  | nil => rfl
  | cons ab l ih => simp only [linearTerms,List.length_cons,List.length_map,ih]
lemma quadraticTerms_length_le (l : List (R × R)) : (quadraticTerms l).length ≤ l.length^2 := by
  induction l with
  | nil => simp [quadraticTerms]
  | cons ab l ih =>
    simp only [quadraticTerms,List.length_append,List.length_map,differenceTerms_length,List.length_cons]
    nlinarith
end ProductTaylor
end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]

 
def wordProduct {J : Type*} (ρ : J → M) : List (J × M) → M
  | [] => 1
  | (k,a)::l => ρ k*a*wordProduct ρ l
@[simp] lemma wordProduct_nil {J : Type*} (ρ : J → M) : wordProduct ρ []=1 := rfl
@[simp] lemma wordProduct_cons {J : Type*} (ρ : J → M) (k : J) (a : M) (l : List (J × M)) :
    wordProduct ρ ((k,a)::l)=ρ k*a*wordProduct ρ l := rfl
lemma wordProduct_append {J : Type*} (ρ : J → M) (l r : List (J × M)) :
    wordProduct ρ (l++r)=wordProduct ρ l*wordProduct ρ r := by
  induction l with
  | nil => simp
  | cons ka l ih => rcases ka with ⟨k,a⟩; simp only [List.cons_append,wordProduct_cons,ih,mul_assoc]
lemma norm_wordProduct_le_one {J : Type*} (ρ : J → M) (hρ : ∀ k, ‖ρ k‖ ≤ 1)
    (l : List (J × M)) (hl : ∀ ka ∈ l, ‖ka.2‖ ≤ 1) : ‖wordProduct ρ l‖ ≤ 1 := by
  induction l with
  | nil => exact IsStarProjection.norm_le (1 : M) (IsStarProjection.one M)
  | cons ka l ih =>
    rcases ka with ⟨k,a⟩
    have ha := hl (k,a) (List.mem_cons_self ..)
    have ht := ih (fun ka hk => hl ka (List.mem_cons_of_mem _ hk))
    exact (norm_mul_le_of_le (norm_mul_le_of_le (hρ k) ha) ht).trans_eq (by simp)

variable {I : Type*} (F : I → M)
abbrev WordAtom (I : Type*) (K : ℕ) := (Bool × Fin K) × Option I
abbrev BoundedWord (I : Type*) (K N : ℕ) := Option I × {l : List (WordAtom I K) // l.length ≤ N}
instance instFiniteBoundedWord [Finite I] (K N : ℕ) : Finite (BoundedWord I K N) := by
  let : Finite {l : List (WordAtom I K) // l.length ≤ N} := (List.finite_length_le (WordAtom I K) N).to_subtype
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
instance instFintypeBoundedWordOfFinite [Finite I] (K N : ℕ) : Fintype (BoundedWord I K N) := Fintype.ofFinite _

def admissibleTail {K : ℕ} (l : List (WordAtom I K)) : Prop :=
  l ≠ [] ∧ ∀ ka ∈ l.dropLast, ka.2 ≠ none

end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity HochschildComparison
namespace ProductTaylor
variable {A R : Type*} [Ring R]
lemma mem_linearTerms_map (f : A → R × R) {l : List A} {x : R}
    (hx : x ∈ linearTerms (l.map f)) :
    ∃ pre a post, l=pre++a::post ∧ x=oldProduct (pre.map f)*(f a).2*oldProduct (post.map f) := by
  obtain ⟨p,b,t,he,hx⟩ := mem_linearTerms hx
  obtain ⟨pre,rest,hr,hp,ht⟩ := List.map_eq_append_iff.mp he
  obtain ⟨a,post,hs,ha,hpost⟩ := List.map_eq_cons_iff.mp ht
  exact ⟨pre,a,post,by rw [hr,hs],by rw [hp,ha,hpost]; exact hx⟩
lemma mem_quadraticTerms_map (f : A → R × R) {l : List A} {x : R}
    (hx : x ∈ quadraticTerms (l.map f)) :
    ∃ pre a middle b post, l=pre++a::(middle++b::post) ∧
      x=oldProduct (pre.map f)*(f a).2*oldProduct (middle.map f)*(f b).2*totalProduct (post.map f) := by
  obtain ⟨p,a,m,b,t,he,hx⟩ := mem_quadraticTerms hx
  obtain ⟨pre,rest,hr,hp,ht⟩ := List.map_eq_append_iff.mp he
  obtain ⟨aa,rest2,hs,ha,ht2⟩ := List.map_eq_cons_iff.mp ht
  obtain ⟨mid,rest3,hr2,hm,ht3⟩ := List.map_eq_append_iff.mp ht2
  obtain ⟨bb,post,hs2,hb,hpost⟩ := List.map_eq_cons_iff.mp ht3
  exact ⟨pre,aa,mid,bb,post,by rw [hr,hs,hr2,hs2],by rw [hp,ha,hm,hb,hpost]; exact hx⟩
end ProductTaylor

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)

lemma admissible_middle {K : ℕ} {l pre middle post : List (WordAtom I K)} {a b : WordAtom I K}
    (hl : admissibleTail l) (he : l=pre++a::(middle++b::post)) :
    a.2 ≠ none ∧ ∀ c ∈ middle, c.2 ≠ none := by
  have hsub : ∀ c ∈ pre++a::middle, c.2 ≠ none := by
    intro c hc
    apply hl.2 c
    have he' : l=(pre++a::middle)++b::post := by rw [he]; simp only [List.append_assoc,List.cons_append]
    rw [he',List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
    exact List.mem_append_left _ hc
  exact ⟨hsub a (List.mem_append_right _ (List.mem_cons_self ..)),fun c hc =>
    hsub c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))⟩

end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M]
variable {I : Type*} (F : I → M) (τ : M →ₚ[ℂ] ℂ)

lemma support_wrapped_admissible {K : ℕ} (hK : 0<K) (i : I) (l : List (WordAtom I K))
    (hl : ∀ a ∈ l, a.2 ≠ none) :
    admissibleTail (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)])) := by
  constructor
  · exact List.cons_ne_nil _ _
  · intro a ha
    have he : (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)]) : List (WordAtom I K))=
        (((true,⟨0,hK⟩),some i)::l)++[((false,⟨0,hK⟩),none)] := rfl
    rw [he,List.dropLast_concat] at ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact Option.some_ne_none _
    · exact hl a ha

end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*} (F : I → M)
abbrev ShortTail (I : Type*) (K N : ℕ) := {l : List (WordAtom I K) // l.length ≤ N}
abbrev LinearLabel (I : Type*) (K N : ℕ) := Option I × ShortTail I K N × WordAtom I K × ShortTail I K N
instance instFiniteLinearLabel [Finite I] (K N : ℕ) : Finite (LinearLabel I K N) := by
  let : Finite (ShortTail I K N) := (List.finite_length_le (WordAtom I K) N).to_subtype
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
instance instFintypeLinearLabelOfFinite [Finite I] (K N : ℕ) : Fintype (LinearLabel I K N) := Fintype.ofFinite _
def linearPower {K N : ℕ} (a : LinearLabel I K N) : Bool × ℕ := (a.2.2.1.1.1,a.2.2.1.1.2.val)

end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix systems, expectations and rational projection approximation. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)
  (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htp : t ≤ p-r) : r*t=0 := by
  have hh := (ht.le_iff_mul_eq_right ((hr.le_iff_sub hp).mp hrp)).mp htp
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma mul_of_initial_projection {v p : M} (hp : IsStarProjection p)
    (hv : star v*v=p) : v*p=v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  calc
    star (v*p-v)*(v*p-v) = p*(star v*v)*p-p*(star v*v)-(star v*v)*p+star v*v := by
      simp only [star_sub,star_mul,hp.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = 0 := by simp only [hv,hp.isIdempotentElem.eq]; abel

end HochschildMatrixSystems

 

 

 

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ}


variable [PartialOrder M]

variable [StarOrderedRing M]

lemma norm_sq (τ : M →ₚ[ℂ] ℂ) (x : M) :
    ‖τ.toPreGNS x‖^2=(τ (star x*x)).re := by
  have hh := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS x))
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re] using hh

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_trace_real (p : M) (hp : IsStarProjection p) : τ p = ((τ p).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2.symm

end HochschildMatrixSystems
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FinitePhases
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additive characters, phase matrices and orthogonality. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildFinitePhase
variable {I : Type*} [Fintype I]

def character (v : I → ZMod 3) : AddChar (I → ZMod 3) ℂ where
  toFun g := ZMod.stdAddChar (∑ i,v i*g i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' g h := by
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,AddChar.map_add_eq_mul]

lemma character_apply (v g : I → ZMod 3) :
    character v g=ZMod.stdAddChar (∑ i,v i*g i) := rfl

lemma character_zero (g : I → ZMod 3) : character 0 g=1 := by simp [character_apply]
lemma character_add (v w g : I → ZMod 3) :
    character (v+w) g=character v g*character w g := by
  simp only [character_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib,AddChar.map_add_eq_mul]
lemma character_star (v g : I → ZMod 3) : star (character v g)=character (-v) g := by
  simp only [character_apply,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,
    AddChar.map_neg_eq_inv,ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj _).symm

lemma character_eq_one_iff (v : I → ZMod 3) : character v=1 ↔ v=0 := by
  classical
  constructor
  · intro h
    ext i
    have hh := congrArg (fun χ : AddChar (I → ZMod 3) ℂ => χ (Pi.single i 1)) h
    simp only [character_apply,AddChar.one_apply] at hh
    have hsum : (∑ j,v j*((Pi.single i (1:ZMod 3) : I → ZMod 3) j))=v i := by
      simp [Pi.single_apply]
    rw [hsum,← (ZMod.stdAddChar : AddChar (ZMod 3) ℂ).map_zero_eq_one] at hh
    exact ZMod.injective_stdAddChar hh
  · rintro rfl
    ext g
    exact character_zero g

end HochschildFinitePhase

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildFinitePhase
variable {I : Type*} [DecidableEq I]

def frequency (i j : I) : I → ZMod 3 := Pi.single j 1 - Pi.single i 1

lemma frequency_ne_zero {i j : I} (hij : i ≠ j) : frequency i j ≠ 0 := by
  intro h
  have hh := congrFun h i
  norm_num [frequency,Pi.single_apply,hij,Ne.symm hij] at hh

lemma frequency_injective {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l)
    (h : frequency i j = frequency k l) : i=k ∧ j=l := by
  have hik : i=k := by
    by_contra hik
    have hh := congrFun h i
    by_cases hil : i=l
    · subst l
      norm_num [frequency,Pi.single_apply,hij,Ne.symm hij,hik,Ne.symm hik] at hh
      exact (by decide : (-1 : ZMod 3) ≠ 1) hh
    · norm_num [frequency,Pi.single_apply,hij,Ne.symm hij,hik,Ne.symm hik,hil,Ne.symm hil] at hh
  subst k
  refine ⟨rfl,?_⟩
  by_contra hjl
  have hh := congrFun h j
  norm_num [frequency,Pi.single_apply,hij,Ne.symm hij,hjl,Ne.symm hjl] at hh

end HochschildFinitePhase
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_RelativeQuantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative small corners, root phases and weak powers of unitaries. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder







open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildRootPhase
variable {I : Type*} [Fintype I]
variable {m : ℕ} [NeZero m]

def character (v : I → ZMod m) : AddChar (I → ZMod m) ℂ where
  toFun g := ZMod.stdAddChar (∑ i,v i*g i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' g h := by
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,AddChar.map_add_eq_mul]

lemma character_apply (v g : I → ZMod m) :
    character v g=ZMod.stdAddChar (∑ i,v i*g i) := rfl

lemma character_zero (g : I → ZMod m) : character 0 g=1 := by simp [character_apply]
lemma character_add (v w g : I → ZMod m) :
    character (v+w) g=character v g*character w g := by
  simp only [character_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib,AddChar.map_add_eq_mul]
lemma character_star (v g : I → ZMod m) : star (character v g)=character (-v) g := by
  simp only [character_apply,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,
    AddChar.map_neg_eq_inv,ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj _).symm

lemma character_eq_one_iff (v : I → ZMod m) : character v=1 ↔ v=0 := by
  classical
  constructor
  · intro h
    ext i
    have hh := congrArg (fun χ : AddChar (I → ZMod m) ℂ => χ (Pi.single i 1)) h
    simp only [character_apply,AddChar.one_apply] at hh
    have hsum : (∑ j,v j*((Pi.single i (1:ZMod m) : I → ZMod m) j))=v i := by
      simp [Pi.single_apply]
    rw [hsum,← (ZMod.stdAddChar : AddChar (ZMod m) ℂ).map_zero_eq_one] at hh
    exact ZMod.injective_stdAddChar hh
  · rintro rfl
    ext g
    exact character_zero g

end HochschildRootPhase

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildRootPhase
variable {M : Type*} [CStarAlgebra M]
variable {n m : ℕ}
  [NeZero m]

omit [NeZero m] in
lemma single_frequency_injective (k : ZMod m) (hk : k ≠ 0) :
    Function.Injective (fun i : Fin n => Pi.single i k) := by
  intro i j hij
  by_contra h
  have hh := congrFun hij i
  simp only [Pi.single_eq_same,Pi.single_eq_of_ne h] at hh
  exact hk hh

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IncrementalPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner partial unitaries, incremental moment estimates and unitary completion. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (q : M) (hq : IsStarProjection q)

def signedExponent (k : Bool × ℕ) : ℤ := if k.1 then -((k.2 : ℤ)+1) else (k.2 : ℤ)+1
end HochschildPatching

 

 

 

open scoped ComplexOrder







namespace HochschildPatching

def expBudget (δ C s : ℝ) : ℝ := δ*(Real.exp (C*s)-1)
lemma expBudget_continuous (δ C : ℝ) : Continuous (expBudget δ C) := by unfold expBudget; fun_prop
lemma expBudget_nonneg {δ C s : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hs : 0 ≤ s) : 0 ≤ expBudget δ C s := by
  exact mul_nonneg hδ (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hC hs)))
lemma expBudget_increment {δ C s t : ℝ} (hδ : 0 ≤ δ) :
    expBudget δ C s+C*(δ+expBudget δ C s)*t ≤ expBudget δ C (s+t) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (C*t)) (mul_nonneg hδ (Real.exp_pos (C*s)).le)
  have he : Real.exp (C*(s+t))=Real.exp (C*s)*Real.exp (C*t) := by rw [mul_add,Real.exp_add]
  unfold expBudget
  rw [he]
  nlinarith

def patchRate (n T : ℝ) : ℝ := 1+2*n^2/(1-T)
def patchTolerance (δ n : ℝ) : ℝ := δ/(n+n^2+1)
lemma patchTolerance_pos {δ n : ℝ} (hδ : 0<δ) (hn : 0 ≤ n) : 0<patchTolerance δ n := by
  unfold patchTolerance
  apply div_pos hδ
  nlinarith [sq_nonneg n]
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small unitary moments, reindexing and simultaneous moment sequences. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} {K L : ℕ}

def mapAtom (f : I → J) (g : Fin K → Fin L) (a : WordAtom I K) : WordAtom J L :=
  ((a.1.1,g a.1.2),a.2.map f)

lemma admissibleTail_map (f : I → J) (g : Fin K → Fin L) (l : List (WordAtom I K))
    (hl : admissibleTail l) : admissibleTail (l.map (mapAtom f g)) := by
  constructor
  · intro h; exact hl.1 (List.map_eq_nil_iff.mp h)
  · intro b hb
    rw [← List.map_dropLast] at hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    intro h
    exact hl.2 a ha (Option.map_eq_none_iff.mp h)

def coeffNumber (a : Option I) : ℕ := if a.isSome then 1 else 0
def wordCoeffNumber (a : Option I) (l : List (WordAtom I K)) : ℕ :=
  coeffNumber a + (l.map (fun b => coeffNumber b.2)).sum
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UltrapowerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered sequences and unitary moments in tracial ultrapowers. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open HochschildRigidity TracialUltrapower HochschildPatching
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))

omit [StarOrderedRing M] in
include h1 in
lemma trace_centered_half (a : M) : τ ((1/2:ℂ) • (a-τ a • (1:M)))=0 := by
  simp only [map_smul,map_sub,h1,smul_eq_mul,mul_one,sub_self,mul_zero]

end HochschildUltrapower

 

 

open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPatching
open HochschildComparison
variable {M A : Type*} [CStarAlgebra M] [CStarAlgebra A]
variable {I : Type*} {K : ℕ}

def mapUnitary (φ : M →⋆ₐ[ℂ] A) : unitary M →⋆* unitary A :=
  Unitary.map { φ.toMonoidHom with map_star' := fun a => map_star φ a }

def evalSequence (n : ℕ) : (ℕ →ᵇ M) →⋆ₐ[ℂ] M where
  toFun a := a n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction





open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AlternatingMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer powers, alternating words and graded free moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
namespace HochschildPatching
variable {I : Type*} {M : Type*} [CStarAlgebra M]
abbrev IntAtom (I : Type*) := ℤ × Option I

def admissibleIntTail (l : List (IntAtom I)) : Prop :=
  l ≠ [] ∧ ∀ b ∈ l.dropLast, b.2 ≠ none

def exponentCode (k : ℤ) : Bool × ℕ := (decide (k<0), k.natAbs-1)
lemma signed_exponentCode (k : ℤ) (hk : k ≠ 0) : signedExponent (exponentCode k)=k := by
  have hn : (k.natAbs-1:ℕ)+1=k.natAbs := Nat.sub_add_cancel (Int.natAbs_pos.mpr hk)
  have hn' : ((k.natAbs-1:ℕ):ℤ)+1=(k.natAbs:ℤ) := by exact_mod_cast hn
  simp only [exponentCode,signedExponent,hn',Int.natCast_natAbs]
  by_cases hh : k<0
  · simp [hh,abs_of_neg hh]
  · simp [hh,abs_of_nonneg (le_of_not_gt hh)]

def toIntAtom {K : ℕ} (b : WordAtom I K) : IntAtom I := (signedExponent (b.1.1,b.1.2.val),b.2)
end HochschildPatching

 

 

namespace HochschildPatching
variable {I H M : Type*} [CStarAlgebra M]
lemma intTail_cons {t : List (IntAtom I)} (ht : admissibleIntTail t) (k : ℤ) (i : I) :
    admissibleIntTail ((k,some i)::t) := by
  refine ⟨List.cons_ne_nil _ _,?_⟩
  rw [List.dropLast_cons_of_ne_nil ht.1]
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp
  · exact ht.2 b hb

end HochschildPatching







end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/
section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace.SeparableSpace E]

theorem exists_countable_total_dual :
    ∃ g : ℕ → StrongDual ℂ E, (∀ n, ‖g n‖ ≤ 1) ∧
      ∀ x : E, (∀ n, g n x = 0) → x = 0 := by
  choose g hg he using fun n => exists_dual_vector'' ℂ (TopologicalSpace.denseSeq E n)
  refine ⟨g, hg, fun x hx => ?_⟩
  by_contra hzero
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hzero
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq E).exists_dist_lt x
    (by positivity : 0 < ‖x‖ / 3)
  have hb : ‖TopologicalSpace.denseSeq E n‖ ≤ ‖TopologicalSpace.denseSeq E n - x‖ := by
    calc
      ‖TopologicalSpace.denseSeq E n‖ =
          ‖g n (TopologicalSpace.denseSeq E n - x)‖ := by
        simp only [map_sub, hx, sub_zero, he, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖g n‖ * ‖TopologicalSpace.denseSeq E n - x‖ := (g n).le_opNorm _
      _ ≤ ‖TopologicalSpace.denseSeq E n - x‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hg n) (norm_nonneg _)
  have ht := norm_le_norm_add_norm_sub (TopologicalSpace.denseSeq E n) x
  rw [norm_sub_rev] at ht
  rw [dist_eq_norm] at hn
  rw [norm_sub_rev] at hb
  linarith

end

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem kernel_invariant_of_commutes (x y : H →L[ℂ] H) (h : x*y=y*x) :
    x.ker ∈ Module.End.invtSubmodule y.toLinearMap := by
  intro ξ hξ
  change x (y ξ)=0
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) h
  change x (y ξ)=y (x ξ) at he
  rw [he,show x ξ=0 from hξ,map_zero]

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_commutes_star_right {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) : Commute x (star y) := by
  have h := congrArg star hxy.eq
  simp only [star_mul,hx.star_eq] at h
  exact h.symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def algebraInclusion (h : N ≤ M) : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion h

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def bicommutantStar (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))

theorem bicommutantStar_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantStar S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  unfold bicommutantStar
  rw [StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

def bicommutantVonNeumann (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := bicommutantStar S
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (bicommutantStar S : Set (H →L[ℂ] H)))=
      (bicommutantStar S : Set (H →L[ℂ] H))
    rw [bicommutantStar_coe,Set.centralizer_centralizer_centralizer]

theorem bicommutantVonNeumann_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantVonNeumann S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  exact bicommutantStar_coe S

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_OperatorAlgebra
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete operators for Kadison similarity

These definitions use bounded operators on the actual Hilbert space, and similarity
uses a unit of that bounded-operator algebra.  The compression estimate is the
operator calculation in Lemma `lem:compressed-commutator` of the manuscript.
-/

noncomputable section

namespace KadisonSimilarity

section Commutators

variable {R : Type*} [NormedRing R]

@[simp] theorem commutator_zero_left (T : R) : commutator 0 T = 0 := by
  simp [commutator]

@[simp] theorem commutator_zero_right (T : R) : commutator T 0 = 0 := by
  simp [commutator]

end Commutators

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_Amplification
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix amplification and the main statements

Matrices act on finite Hilbert sums with their `ℓ²` norm. Consequently the
norm in `CommutatorEstimate` is the concrete operator matrix norm, rather than
the coordinatewise supremum norm of a matrix. No main estimate is assumed here.
-/

noncomputable section

universe u v

namespace KadisonSimilarity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem matrixOperator_apply {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (ξ : HilbertCopies H n) (i : Fin n) :
    matrixOperator X ξ i = ∑ j : Fin n, X i j (ξ j) := by
  simp [matrixOperator]

@[simp] theorem amplify_apply (Y : H →L[ℂ] H) (n : ℕ)
    (ξ : HilbertCopies H n) (i : Fin n) : amplify Y n ξ i = Y (ξ i) := by
  simp [amplify]

@[simp] theorem innerDerivation_apply (Y T : H →L[ℂ] H) :
    innerDerivation Y T = commutator Y T := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicFactorization
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic column factorization from equality of vector functionals

Equality of quadratic forms yields an intertwining column contraction.
Existence of a realizing vector is a consequence of standard form.
-/

noncomputable section
namespace KadisonSimilarity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The linear orbit map at the vector realizing the positive functional. -/
def orbitLinearMap (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) : N →ₗ[ℂ] K where
  toFun a := (a : K →L[ℂ] K) ζ
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem orbitLinearMap_apply (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) (a : N) :
    orbitLinearMap N ζ a = (a : K →L[ℂ] K) ζ := rfl

/-- The closed cyclic subspace generated by the realizing vector. -/
def orbitClosure (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) : ClosedSubmodule ℂ K :=
  (LinearMap.range (orbitLinearMap N ζ)).closure

/-- The orbit map with codomain restricted to the closed cyclic subspace. -/
def orbitIntoClosure (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) :
    N →ₗ[ℂ] orbitClosure N ζ :=
  (orbitLinearMap N ζ).codRestrict (orbitClosure N ζ).toSubmodule fun a =>
    (LinearMap.range (orbitLinearMap N ζ)).le_topologicalClosure ⟨a, rfl⟩

@[simp] theorem orbitIntoClosure_coe (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) (a : N) :
    (orbitIntoClosure N ζ a : K) = (a : K →L[ℂ] K) ζ := rfl

/-- The closed orbit is invariant under the star subalgebra. -/
theorem orbitClosure_invariant (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K)
    (a : N) (x : K) (hx : x ∈ orbitClosure N ζ) :
    (a : K →L[ℂ] K) x ∈ orbitClosure N ζ := by
  have hmap : Set.MapsTo (a : K →L[ℂ] K)
      (LinearMap.range (orbitLinearMap N ζ) : Set K)
      (LinearMap.range (orbitLinearMap N ζ) : Set K) := by
    rintro y ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    simp [mul_apply_eq_comp]
  exact hmap.closure (a : K →L[ℂ] K).continuous hx

/-- The coordinates of a bounded column operator. -/
def columnEntry {n : ℕ} (V : K →L[ℂ] HilbertCopies K n) (i : Fin n) : K →L[ℂ] K :=
  (PiLp.proj 2 (fun _ : Fin n => K) i).comp V

omit [CompleteSpace K] in
@[simp] theorem columnEntry_apply {n : ℕ}
    (V : K →L[ℂ] HilbertCopies K n) (i : Fin n) (x : K) :
    columnEntry V i x = V x i := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.columnEntry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete matrix norms and complete boundedness

The matrix norm used here is `CStarMatrix`'s C-star norm. The representation
on finite Hilbert sums is shown to preserve that norm, connecting the concrete
commutator estimate with the usual notion of complete boundedness.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebraic operator-matrix action, before changing the matrix norm. -/
def operatorMatrixRepresentation (n : ℕ) :
    Matrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ]
      (HilbertCopies H n →L[ℂ] HilbertCopies H n) where
  toFun X := matrixOperator X
  map_zero' := by ext ξ i; simp [matrixOperator]
  map_one' := by
    ext ξ i
    simp [matrixOperator, Matrix.one_apply]
    have hentry (j : Fin n) :
        (if i = j then (1 : H →L[ℂ] H) else 0) (ξ j) =
          if i = j then ξ j else 0 := by split_ifs <;> simp
    simp_rw [hentry]
    simp
  map_add' X Y := by ext ξ i; simp [matrixOperator, Finset.sum_add_distrib]
  commutes' c := by
    ext ξ i
    simp [matrixOperator, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
    have hentry (j : Fin n) :
        (if i = j then c • (1 : H →L[ℂ] H) else 0) (ξ j) =
          if i = j then c • ξ j else 0 := by split_ifs <;> simp
    simp_rw [hentry]
    simp
  map_mul' X Y := by
    ext ξ i
    simp only [matrixOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearEquiv.coe_coe,
      PiLp.continuousLinearEquiv_symm_apply, sum_apply, PiLp.proj_apply,
      Matrix.mul_apply, mul_apply_eq_comp, map_sum]
    rw [Finset.sum_comm]
  map_star' X := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    simp only [PiLp.inner_apply, matrixOperator_apply, Matrix.star_apply,
      ContinuousLinearMap.star_eq_adjoint,
      sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_left]
    rw [Finset.sum_comm]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_RectangularDerivations
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.columnEntry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangular derivations and the row/column estimate -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Finite rectangular operator matrices act between the two Hilbert sums. -/
def rectangularMatrixOperator {p q : ℕ}
    (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) :
    HilbertCopies K q →L[ℂ] HilbertCopies F p :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin p => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j : Fin q, (X i j).comp (PiLp.proj 2 (fun _ : Fin q => K) j))

@[simp] theorem rectangularMatrixOperator_apply {p q : ℕ}
    (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F))
    (ξ : HilbertCopies K q) (i : Fin p) :
    rectangularMatrixOperator X ξ i = ∑ j : Fin q, X i j (ξ j) := by
  simp [rectangularMatrixOperator]

@[simp] theorem rectangularMatrixOperator_zero {p q : ℕ} :
    rectangularMatrixOperator (0 : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) = 0 := by
  ext ξ i
  simp

/-- Coordinatewise amplification of a bounded operator between different spaces. -/
def mapCopies (T : K →L[ℂ] F) (n : ℕ) : HilbertCopies K n →L[ℂ] HilbertCopies F n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : Fin n => K) i))

@[simp] theorem mapCopies_apply (T : K →L[ℂ] F) (n : ℕ)
    (ξ : HilbertCopies K n) (i : Fin n) : mapCopies T n ξ i = T (ξ i) := by
  simp [mapCopies]

/-- The Hilbert direct sum used in the rectangular triangular representation. -/
abbrev RectangularSum (F K : Type*) := WithLp 2 (F × K)

open scoped CStarAlgebra

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumns
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.columnEntry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extending a corner intertwiner through finitely many matrix units

These are the matrix-coordinate steps of `lem:full-column`: coordinatewise
amplification preserves the error norm and intertwines a full operator matrix
as soon as it intertwines each entry. The geometric construction of the
corner and its matrix-unit coordinates is still required.
-/

noncomputable section

namespace KadisonSimilarity

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] theorem mapCopies_sub (S T : K →L[ℂ] F) (n : ℕ) :
    mapCopies (S - T) n = mapCopies S n - mapCopies T n := by
  ext x i
  simp only [mapCopies_apply, sub_apply, PiLp.sub_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumnTheorem
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The full-column implementation argument

The corner commutator is constructed here, corrected by the proved cyclic
implementation theorem, and extended through finite matrix coordinates with
exactly the same norm. Extension by zero and the tracial commutation theorem
then identify the resulting intertwiner as a right multiplier.

The finite-factor realization of the corner and its matrix coordinates remains
explicit geometric data; the full-column conclusion is not an input.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section CornerCommutator

variable {C F K : Type*} [CStarAlgebra C]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual rectangular commutator of a corner operator. -/
def cornerCommutator (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (G : K →L[ℂ] F) : C →L[ℂ] (K →L[ℂ] F) where
  toFun a := G.comp (σ a) - (ρ a).comp G
  map_add' := by
    intro a b
    ext x
    simp
    abel
  map_smul' := by
    intro c a
    ext x
    simp [smul_sub]
  cont := ((map_continuous σ).const_clm_comp G).sub
    ((map_continuous ρ).clm_comp_const G)

@[simp] theorem cornerCommutator_apply (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (G : K →L[ℂ] F) (a : C) :
    cornerCommutator ρ σ G a = G.comp (σ a) - (ρ a).comp G := rfl

end CornerCommutator

section ScalarMatrixUnits

variable {F K : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Insertion into one coordinate of a finite Hilbert sum. -/
def copyInsert {n : ℕ} (i : Fin n) : K →L[ℂ] HilbertCopies K n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => K) i)

@[simp] theorem copyInsert_apply {n : ℕ} (i : Fin n) (x : K) :
    copyInsert i x = PiLp.single 2 i x := rfl

/-- The scalar matrix unit which sends coordinate `j` to coordinate `i`. -/
def copyMatrixUnit {n : ℕ} (i j : Fin n) :
    HilbertCopies K n →L[ℂ] HilbertCopies K n :=
  (copyInsert i).comp (PiLp.proj 2 (fun _ : Fin n => K) j)

@[simp] theorem copyMatrixUnit_apply {n : ℕ} (i j : Fin n) (x : HilbertCopies K n) :
    copyMatrixUnit i j x = PiLp.single 2 i (x j) := rfl

/-- A diagonal corner of a bounded operator on two finite Hilbert sums. -/
def copyCorner {n : ℕ} (i : Fin n) (W : HilbertCopies K n →L[ℂ] HilbertCopies F n) :
    K →L[ℂ] F :=
  (PiLp.proj 2 (fun _ : Fin n => F) i).comp (W.comp (copyInsert i))

@[simp] theorem copyCorner_apply {n : ℕ} (i : Fin n)
    (W : HilbertCopies K n →L[ℂ] HilbertCopies F n) (x : K) :
    copyCorner i W x = W (PiLp.single 2 i x) i := rfl

end ScalarMatrixUnits

section MatrixCoordinates

variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite matrix-unit coordinates of a full column and its corner.
The two action identities say that full left multiplication has the usual
corner matrix entries. They assert no existence of an intertwiner. -/
structure FullColumnCoordinates
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (n : ℕ) where
  domain : D ≃ₗᵢ[ℂ] HilbertCopies K n
  codomain : H ≃ₗᵢ[ℂ] HilbertCopies F n
  entry : P → Matrix (Fin n) (Fin n) C
  domain_action : ∀ a x, domain (Lr a x) =
    matrixOperator (fun i j => σ (entry a i j)) (domain x)
  codomain_action : ∀ a x, codomain (L a x) =
    matrixOperator (fun i j => ρ (entry a i j)) (codomain x)

namespace FullColumnCoordinates

variable {L : P →⋆ₐ[ℂ] (H →L[ℂ] H)} {Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D)}
  {ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)} {σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)} {n : ℕ}

/-- Diagonal extension of a corner operator through matrix-unit coordinates. -/
def extend (c : FullColumnCoordinates L Lr ρ σ n) (T : K →L[ℂ] F) : D →L[ℂ] H :=
  c.codomain.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mapCopies T n).comp c.domain.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem extend_apply (c : FullColumnCoordinates L Lr ρ σ n)
    (T : K →L[ℂ] F) (x : D) :
    c.codomain (c.extend T x) = mapCopies T n (c.domain x) := by
  simp [extend]

end FullColumnCoordinates
end MatrixCoordinates

section CyclicCornerData

variable {P C K Q : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The precise finite-factor comparison consequence needed for the chosen
corner. This is the trace form of projection comparison: Blackadar,
III.1.1.11, together with the faithful finite trace. -/
def FiniteFactorProjectionComparison (τ : P → ℝ) : Prop :=
  ∀ e r : P, IsStarProjection e → IsStarProjection r → τ r ≤ τ e →
    ∃ v : P, star v * v = r ∧ e * (v * star v) = v * star v

end CyclicCornerData

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDecomposition
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every unital star representation is the orthogonal sum of cyclic reducing
representations. The family is constructed by Zorn's lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

/-- The bounded action on the actual closed orbit subspace. -/
def orbitAction (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    orbitClosure σ.range ξ →L[ℂ] orbitClosure σ.range ξ :=
  (σ a).restrict (orbitClosure_invariant σ.range ξ (σ.rangeRestrict a))

@[simp] theorem orbitAction_coe (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A)
    (x : orbitClosure σ.range ξ) : (orbitAction σ ξ a x : H) = σ a (x : H) := rfl

/-- Restriction to a cyclic reducing subspace is a unital star representation. -/
def orbitRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →⋆ₐ[ℂ] (orbitClosure σ.range ξ →L[ℂ] orbitClosure σ.range ξ) where
  toFun := orbitAction σ ξ
  map_zero' := by
    ext x
    simp
  map_one' := by
    ext x
    simp
  map_add' a b := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp [mul_apply_eq_comp]
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ y ((orbitAction σ ξ a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ (σ a (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem orbitRepresentation_coe (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A)
    (x : orbitClosure σ.range ξ) : (orbitRepresentation σ ξ a x : H) = σ a (x : H) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorSlices
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing tensor slices in the propagation argument

A bounded weakly null family of vectors gives strongly vanishing slices of
any fixed vector in the completed Hilbert tensor product. This is the density
step in `lem:propagation`, with the uniform bound proved on the completion.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The Hilbert completion of the algebraic tensor product. -/
def HilbertTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  UniformSpace.Completion (E ⊗[ℂ] F)

/-- Keep the canonical completed-tensor structures named. In iterated word
spaces this shares the structure terms instead of expanding each completion
and algebraic tensor instance at every use. -/
instance hilbertTensorNormedAddCommGroup : NormedAddCommGroup (HilbertTensor E F) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (E ⊗[ℂ] F)))

instance hilbertTensorInnerProductSpace : InnerProductSpace ℂ (HilbertTensor E F) :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion (E ⊗[ℂ] F)))

instance hilbertTensorCompleteSpace : CompleteSpace (HilbertTensor E F) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (E ⊗[ℂ] F)))

instance hilbertTensorCoe : Coe (E ⊗[ℂ] F) (HilbertTensor E F) :=
  ⟨fun x => (x : UniformSpace.Completion (E ⊗[ℂ] F))⟩

@[simp] theorem norm_hilbertTensor_coe (x : E ⊗[ℂ] F) :
    ‖(x : HilbertTensor E F)‖ = ‖x‖ :=
  UniformSpace.Completion.norm_coe x

/-- Contract the first tensor coordinate against `x`. -/
def algebraTensorSlice (x : E) : E ⊗[ℂ] F →L[ℂ] F :=
  (TensorProduct.lidIsometry ℂ F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (TensorProduct.mapL (innerSL ℂ x) (ContinuousLinearMap.id ℂ F))

@[simp] theorem algebraTensorSlice_tmul (x a : E) (b : F) :
    algebraTensorSlice x (a ⊗ₜ[ℂ] b) = inner ℂ x a • b := by
  simp [algebraTensorSlice]

variable [CompleteSpace F]

/-- The slice extends uniquely to the completed Hilbert tensor product. -/
def tensorSlice (x : E) : HilbertTensor E F →L[ℂ] F :=
  (algebraTensorSlice x).fromCompletion

@[simp] theorem tensorSlice_coe (x : E) (z : E ⊗[ℂ] F) :
    tensorSlice x (z : HilbertTensor E F) = algebraTensorSlice x z :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorWords
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite words in completed Hilbert tensor powers

The scalar word has length zero. Longer words are genuine Hilbert tensor
products, completed only after the finite algebraic tensor product is formed.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

/-- Scalars at the same universe as the Hilbert space. -/
abbrev TensorScalars : Type u := ULift.{u} ℂ

instance tensorScalarsInnerProductSpace : InnerProductSpace ℂ (TensorScalars.{u}) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Bundling keeps the vector-space structures available during the recursion. -/
structure TensorWordSpace where
  Carrier : Type u
  normed : NormedAddCommGroup Carrier
  innerSpace : @InnerProductSpace ℂ Carrier _ normed.toSeminormedAddCommGroup

attribute [instance] TensorWordSpace.normed TensorWordSpace.innerSpace

/-- Right-associated algebraic Hilbert tensor powers, including degree zero. -/
def tensorWordSpace (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ℕ → TensorWordSpace.{u}
  | 0 => ⟨TensorScalars, inferInstance, inferInstance⟩
  | n + 1 => ⟨E ⊗[ℂ] (tensorWordSpace E n).Carrier, inferInstance, inferInstance⟩

abbrev TensorWord (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :=
  (tensorWordSpace E n).Carrier

/-- The elementary word determined by its letters. -/
def tensorWord : {n : ℕ} → (Fin n → E) → TensorWord E n
  | 0, _ => ⟨1⟩
  | _n + 1, x => x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x)

/-- Inner products of words are products of the inner products of letters. -/
theorem inner_tensorWord {n : ℕ} (x y : Fin n → E) :
    inner ℂ (tensorWord x) (tensorWord y) = ∏ i, inner ℂ (x i) (y i) := by
  induction n with
  | zero =>
      change inner ℂ (1 : ℂ) 1 = _
      simp
  | succ n ih =>
      change inner ℂ (x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x))
        (y 0 ⊗ₜ[ℂ] tensorWord (Fin.tail y)) = _
      rw [TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]
      rfl

/-- Completed finite Hilbert tensor powers. -/
abbrev CompletedTensorWord (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) := UniformSpace.Completion (TensorWord E n)

/-- An elementary word in the completed tensor power. -/
def completedTensorWord {n : ℕ} (x : Fin n → E) : CompletedTensorWord E n := tensorWord x

@[simp] theorem inner_completedTensorWord {n : ℕ} (x y : Fin n → E) :
    inner ℂ (completedTensorWord x) (completedTensorWord y) = ∏ i, inner ℂ (x i) (y i) := by
  rw [completedTensorWord, completedTensorWord, UniformSpace.Completion.inner_coe,
    inner_tensorWord]

/-- Elementary words linearly span the algebraic tensor power. -/
theorem tensorWord_mem_submodule : ∀ n : ℕ, ∀ S : Submodule ℂ (TensorWord E n),
    (∀ x : Fin n → E, tensorWord x ∈ S) → ∀ z, z ∈ S := by
  intro n
  induction n with
  | zero =>
      intro S hS z
      have heq : z = z.down • tensorWord (Fin.elim0 : Fin 0 → E) := by
        cases z
        apply ULift.ext
        change _ = _ * 1
        exact (mul_one _).symm
      rw [heq]
      exact S.smul_mem _ (hS _)
  | succ n ih =>
      intro S hS z
      induction z using OAI.tensorInductionOn with
      | tmul a b =>
          let T : Submodule ℂ (TensorWord E n) :=
            S.comap (TensorProduct.mk ℂ E (TensorWord E n) a)
          apply ih T ?_ b
          intro x
          change a ⊗ₜ[ℂ] tensorWord x ∈ S
          change tensorWord (Fin.cons a x) ∈ S
          exact hS _
      | add a b ha hb => exact S.add_mem ha hb

/-- Elementary words are total after Hilbert completion. -/
theorem completedTensorWord_mem_closed_submodule {n : ℕ}
    (S : Submodule ℂ (CompletedTensorWord E n))
    (hclosed : IsClosed (S : Set (CompletedTensorWord E n)))
    (hword : ∀ x : Fin n → E, completedTensorWord x ∈ S)
    (z : CompletedTensorWord E n) : z ∈ S := by
  refine UniformSpace.Completion.induction_on z hclosed ?_
  intro w
  let T : Submodule ℂ (TensorWord E n) :=
    S.comap (UniformSpace.Completion.toComplL : TensorWord E n →L[ℂ]
      CompletedTensorWord E n).toLinearMap
  exact tensorWord_mem_submodule n T hword w

/-- Continuous operators are determined by their values on elementary words. -/
theorem continuousLinearMap_ext_completedTensorWords {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}
    (f g : CompletedTensorWord E n →L[ℂ] F)
    (hword : ∀ x : Fin n → E, f (completedTensorWord x) = g (completedTensorWord x)) : f = g := by
  let S : Submodule ℂ (CompletedTensorWord E n) := (f - g).ker
  have hmem (z : CompletedTensorWord E n) : z ∈ S := by
    apply completedTensorWord_mem_closed_submodule S (f - g).isClosed_ker ?_ z
    intro x
    change f (completedTensorWord x) - g (completedTensorWord x) = 0
    exact sub_eq_zero.mpr (hword x)
  ext z
  exact sub_eq_zero.mp (hmem z)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointBounds
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The endpoint matrix-unit estimate from a supporting projection

For the coefficient tests it suffices to move a self-adjoint supporting
projection across the inner product. This gives the required dimension factor
without invoking the full tracial commutation theorem.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The tensor norm on elementary words is exactly the product of letter norms. -/
theorem norm_tensorWord : ∀ (n : ℕ) (x : Fin n → E),
    ‖tensorWord x‖ = ∏ i, ‖x i‖ := by
  intro n
  induction n with
  | zero =>
    intro x
    change ‖(⟨1⟩ : TensorScalars.{u})‖ = 1
    simp only [ULift.norm_def, norm_one]
  | succ n ih =>
    intro x
    change ‖x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x)‖ = ∏ i, ‖x i‖
    rw [TensorProduct.norm_tmul, ih, Fin.prod_univ_succ]
    rfl

/-- Completion preserves the elementary tensor norm. -/
theorem norm_completedTensorWord {n : ℕ} (x : Fin n → E) :
    ‖completedTensorWord x‖ = ∏ i, ‖x i‖ := by
  change ‖(tensorWord x : UniformSpace.Completion (TensorWord E n))‖ = _
  rw [UniformSpace.Completion.norm_coe, norm_tensorWord]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorDensity
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing finite-stage pairing identities to completed tensor words

Continuity and density extend the coefficient identity on a common matrix
stage to arbitrary letters. The final vanishing statement then uses actual
totality of elementary Hilbert tensors.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem continuous_tensorWord (n : ℕ) : Continuous (tensorWord (E := E) (n := n)) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      change Continuous (fun x : Fin (n + 1) → E => x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x))
      have htail : Continuous (fun x : Fin (n + 1) → E => Fin.tail x) :=
        continuous_pi (fun i => continuous_apply i.succ)
      have hf : Continuous (fun x : Fin (n + 1) → E => (x 0, tensorWord (Fin.tail x))) :=
        (continuous_apply 0).prodMk (ih.comp htail)
      have hg : Continuous (fun p : E × TensorWord E n => p.1 ⊗ₜ[ℂ] p.2) :=
        TensorProduct.continuous_tmul
      exact hg.comp hf

theorem continuous_completedTensorWord (n : ℕ) :
    Continuous (completedTensorWord (E := E) (n := n)) :=
  (UniformSpace.Completion.continuous_coe (α := TensorWord E n)).comp (continuous_tensorWord n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorPermutations
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Permutations of completed Hilbert tensor words

The permutation maps are constructed from the multilinear universal property
and proved isometric on the algebraic tensor power before completion.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tensorWord_update_add : ∀ n : ℕ, ∀ (x : Fin n → E) (i : Fin n) (a b : E),
    tensorWord (Function.update x i (a + b)) =
      tensorWord (Function.update x i a) + tensorWord (Function.update x i b) := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ n ih =>
      intro x i a b
      cases i using Fin.cases with
      | zero =>
          change (a + b) ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 (a + b))) =
            a ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 a)) +
              b ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 b))
          simp only [Fin.tail_update_zero, TensorProduct.add_tmul]
      | succ i =>
          change Function.update x i.succ (a + b) 0 ⊗ₜ[ℂ]
            tensorWord (Fin.tail (Function.update x i.succ (a + b))) =
            Function.update x i.succ a 0 ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x i.succ a)) +
              Function.update x i.succ b 0 ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x i.succ b))
          simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),
            Fin.tail_update_succ, ih, TensorProduct.tmul_add]

theorem tensorWord_update_smul : ∀ n : ℕ, ∀ (x : Fin n → E) (i : Fin n) (c : ℂ) (a : E),
    tensorWord (Function.update x i (c • a)) = c • tensorWord (Function.update x i a) := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ n ih =>
      intro x i c a
      cases i using Fin.cases with
      | zero =>
          change (c • a) ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 (c • a))) =
            c • (a ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 a)))
          simp only [Fin.tail_update_zero, TensorProduct.smul_tmul']
      | succ i =>
          change Function.update x i.succ (c • a) 0 ⊗ₜ[ℂ]
            tensorWord (Fin.tail (Function.update x i.succ (c • a))) =
              c • (Function.update x i.succ a 0 ⊗ₜ[ℂ]
                tensorWord (Fin.tail (Function.update x i.succ a)))
          simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),
            Fin.tail_update_succ, ih, TensorProduct.tmul_smul]

/-- The elementary word map, with its multilinearity bundled. -/
def tensorWordMultilinear (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => E) (TensorWord E n) :=
  MultilinearMap.mk' tensorWord (tensorWord_update_add n) (tensorWord_update_smul n)

@[simp] theorem tensorWordMultilinear_apply (n : ℕ) (x : Fin n → E) :
    tensorWordMultilinear n x = tensorWord x := rfl

variable (E)

/-- The multilinear universal property of the iterated algebraic tensor word. -/
def tensorWordLiftLinear (F : Type*) [AddCommGroup F] [Module ℂ F] :
    (n : ℕ) → MultilinearMap ℂ (fun _ : Fin n => E) F →ₗ[ℂ] (TensorWord E n →ₗ[ℂ] F)
  | 0 =>
    { toFun := fun f =>
        { toFun := fun z => z.down • f Fin.elim0
          map_add' := fun _ _ => add_smul _ _ _
          map_smul' := fun c z => mul_smul c z.down _ }
      map_add' := by intro f g; ext z; exact smul_add _ _ _
      map_smul' := by intro c f; ext z; exact smul_comm _ _ _ }
  | n + 1 =>
    { toFun := fun f => TensorProduct.lift ((tensorWordLiftLinear F n).comp f.curryLeft)
      map_add' := by
        intro f g
        apply TensorProduct.ext'
        intro a b
        change tensorWordLiftLinear F n ((f + g).curryLeft a) b = _
        have heq : (f + g).curryLeft a = f.curryLeft a + g.curryLeft a := rfl
        rw [heq, map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro c f
        apply TensorProduct.ext'
        intro a b
        change tensorWordLiftLinear F n ((c • f).curryLeft a) b = _
        have heq : (c • f).curryLeft a = c • f.curryLeft a := rfl
        rw [heq, map_smul, LinearMap.smul_apply]
        rfl }

variable {E}

@[simp] theorem tensorWordLiftLinear_apply_word {F : Type*} [AddCommGroup F] [Module ℂ F] :
    ∀ (n : ℕ) (f : MultilinearMap ℂ (fun _ : Fin n => E) F) (x : Fin n → E),
      tensorWordLiftLinear E F n f (tensorWord x) = f x := by
  intro n
  induction n with
  | zero =>
      intro f x
      change (1 : ℂ) • f Fin.elim0 = f x
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      rw [hx, one_smul]
  | succ n ih =>
      intro f x
      change tensorWordLiftLinear E F n (f.curryLeft (x 0)) (tensorWord (Fin.tail x)) = f x
      rw [ih, MultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Algebraic linear maps on tensor words are determined by elementary words. -/
theorem linearMap_ext_tensorWords {F : Type*} [AddCommGroup F] [Module ℂ F] {n : ℕ}
    (f g : TensorWord E n →ₗ[ℂ] F)
    (hword : ∀ x : Fin n → E, f (tensorWord x) = g (tensorWord x)) : f = g := by
  let S : Submodule ℂ (TensorWord E n) := (f - g).ker
  have hmem (z : TensorWord E n) : z ∈ S :=
    tensorWord_mem_submodule n S (fun x => sub_eq_zero.mpr (hword x)) z
  ext z
  exact sub_eq_zero.mp (hmem z)

/-- The algebraic map permuting tensor positions. -/
def tensorPermutationLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TensorWord E n →ₗ[ℂ] TensorWord E n :=
  tensorWordLiftLinear E (TensorWord E n) n ((tensorWordMultilinear n).domDomCongr σ.symm)

@[simp] theorem tensorPermutationLinear_word {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → E) :
    tensorPermutationLinear σ (tensorWord x) = tensorWord (fun i => x (σ.symm i)) := by
  rw [tensorPermutationLinear, tensorWordLiftLinear_apply_word]
  rfl

theorem linearMap_preserves_inner_of_words {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {n : ℕ}
    (f : TensorWord E n →ₗ[ℂ] F)
    (hword : ∀ x y : Fin n → E,
      inner ℂ (f (tensorWord x)) (f (tensorWord y)) = inner ℂ (tensorWord x) (tensorWord y)) :
    ∀ a b, inner ℂ (f a) (f b) = inner ℂ a b := by
  have hfirst (x : Fin n → E) (b : TensorWord E n) :
      inner ℂ (f (tensorWord x)) (f b) = inner ℂ (tensorWord x) b := by
    have heq := linearMap_ext_tensorWords
      ((innerSL ℂ (f (tensorWord x))).toLinearMap.comp f)
      (innerSL ℂ (tensorWord x)).toLinearMap (hword x)
    exact congrArg (fun g : TensorWord E n →ₗ[ℂ] ℂ => g b) heq
  intro a b
  have heq := linearMap_ext_tensorWords ((innerSL ℂ (f a)).toLinearMap.comp f)
    (innerSL ℂ a).toLinearMap (fun x => by
      change inner ℂ (f a) (f (tensorWord x)) = inner ℂ a (tensorWord x)
      simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hfirst x a))
  exact congrArg (fun g : TensorWord E n →ₗ[ℂ] ℂ => g b) heq

/-- Tensor-position permutations preserve the Hilbert inner product. -/
def tensorPermutationIsometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TensorWord E n →ₗᵢ[ℂ] TensorWord E n :=
  (tensorPermutationLinear σ).isometryOfInner (linearMap_preserves_inner_of_words _ (by
    intro x y
    simp only [tensorPermutationLinear_word, inner_tensorWord]
    exact Equiv.prod_comp σ.symm (fun i => inner ℂ (x i) (y i))))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointTensors
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed tensor words with an unrestricted first endpoint

The endpoint and the centered tail may live in different Hilbert spaces.
Their completed tensor product has total elementary words and carries
the operators `I ⊗ A` and endpoint slices.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

@[simp] theorem inner_hilbertTensor_coe (x y : E ⊗[ℂ] F) :
    inner ℂ (x : HilbertTensor E F) (y : HilbertTensor E F) = inner ℂ x y :=
  UniformSpace.Completion.inner_coe x y

@[simp] theorem hilbertTensor_coe_add (x y : E ⊗[ℂ] F) :
    ((x + y : E ⊗[ℂ] F) : HilbertTensor E F) =
      (x : HilbertTensor E F) + (y : HilbertTensor E F) :=
  UniformSpace.Completion.coe_add x y

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantForms
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-stage coefficient form

The coefficient function used by the invariant argument is proved multilinear
from the linear source letters and conjugate-linear test letters. No finite or
completed coefficient expansion is part of this construction.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexConjugate TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def pullLetters {D V I S : Type*} (f : D → V) (j : I → S) (v : S → D) : I → V :=
  f ∘ v ∘ j

theorem pullLetters_update {D V I S : Type*} [DecidableEq I] [DecidableEq S]
    (f : D → V) (j : I → S) (hj : Function.Injective j) (v : S → D) (i : I) (a : D) :
    pullLetters f j (Function.update v (j i) a) =
      Function.update (pullLetters f j v) i (f a) := by
  unfold pullLetters
  rw [Function.update_comp_eq_of_injective v hj i a,
    Function.comp_update]

theorem pullLetters_update_miss {D V I S : Type*} [DecidableEq S]
    (f : D → V) (j : I → S) (v : S → D) (i : S) (a : D) (hmiss : ∀ x, j x ≠ i) :
    pullLetters f j (Function.update v i a) = pullLetters f j v := by
  unfold pullLetters
  rw [Function.update_comp_eq_of_forall_ne v a hmiss]

abbrev sourceIndex {k l : ℕ} (i : Fin k) : Option (Fin k ⊕ Fin l) := some (Sum.inl i)
abbrev testIndex {k l : ℕ} (i : Fin l) : Option (Fin k ⊕ Fin l) := some (Sum.inr i)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantIntertwiners
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix realization of the invariant-intertwiner argument

Finite coefficient forms are constructed from explicit Hilbert-space matrix
realizations. Normalized Hilbert--Schmidt inner products supply the matrix-unit
norms, while left matrix actions supply endpoint transfer. The sole invariant
theory input remains finite-dimensional Schur--Weyl spanning.
-/

noncomputable section
namespace KadisonSimilarity

variable {E F α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype α] [DecidableEq α]

/-- Local geometric data of one full matrix stage in a tracial Hilbert space.
The maps and identities describe its normalized Hilbert--Schmidt realization;
no coefficient expansion or intertwiner classification is included. -/
structure MatrixHilbertStage where
  full : Matrix α α ℂ →ₗ[ℂ] E
  center : Matrix α α ℂ →ₗ[ℂ] F
  left : Matrix α α ℂ → (E →L[ℂ] E)
  inner_full : ∀ a b, inner ℂ (full a) (full b) =
    (Fintype.card α : ℂ)⁻¹ * Matrix.trace (star a * b)
  norm_center_le : ∀ a, ‖center a‖ ≤ ‖full a‖
  left_apply : ∀ a b, left a (full b) = full (a * b)
  left_adjoint : ∀ a, (left a).adjoint = left (star a)

/-- The test endpoint map is conjugate-linear because matrix star is. -/
def MatrixHilbertStage.testEndpoint
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) : Matrix α α ℂ →ₗ⋆[ℂ] E :=
  R.full.comp (starLinearEquiv ℂ).toLinearMap

def MatrixHilbertStage.testLetter
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F) :
    Matrix α α ℂ →ₗ⋆[ℂ] F := J.toLinearMap.comp R.center

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixRealization
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix stages inside an actual tracial Hilbert representation

A trace-preserving matrix embedding supplies the normalized Hilbert--Schmidt
geometry, the corner left action, and the centered projection used by the
invariant-intertwiner argument. No invariant-theory conclusion is an input.
-/

noncomputable section
namespace KadisonSimilarity

variable {R E α : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype α] [DecidableEq α]

/-- The centered subspace is the orthogonal complement of the trace vector. -/
abbrev centeredSubspace (Ω : E) : Submodule ℂ E := (ℂ ∙ Ω)ᗮ

/-- Center a represented algebra vector by its actual orthogonal projection. -/
def tracialCenter (V : R →ₗ[ℂ] E) : R →ₗ[ℂ] centeredSubspace (V 1) :=
  (centeredSubspace (V 1)).orthogonalProjectionOnto.toLinearMap.comp V

omit [StarRing R] [CompleteSpace E] in
@[simp] theorem tracialCenter_apply (V : R →ₗ[ℂ] E) (a : R) :
    tracialCenter V a = (centeredSubspace (V 1)).orthogonalProjectionOnto (V a) := rfl

omit [StarRing R] [CompleteSpace E] in
/-- Centering is contractive in the represented Hilbert norm. -/
theorem norm_tracialCenter_le (V : R →ₗ[ℂ] E) (a : R) :
    ‖tracialCenter V a‖ ≤ ‖V a‖ :=
  (centeredSubspace (V 1)).norm_orthogonalProjectionOnto_apply_le (V a)

omit [StarRing R] [CompleteSpace E] in
@[simp] theorem tracialCenter_one (V : R →ₗ[ℂ] E) : tracialCenter V 1 = 0 :=
  Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (V 1)

omit [StarRing R] [CompleteSpace E] in
/-- Density of the represented algebra passes to its centered projection. -/
theorem denseRange_tracialCenter (V : R →ₗ[ℂ] E) (hdense : DenseRange V) :
    DenseRange (tracialCenter V) := by
  have hs : Function.Surjective (centeredSubspace (V 1)).orthogonalProjectionOnto := by
    intro x
    exact ⟨x, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  exact hs.denseRange.comp hdense
    (centeredSubspace (V 1)).orthogonalProjectionOnto.continuous

omit [StarRing R] [CompleteSpace E] in
/-- Subtracting the trace creates an algebraic trace-zero vector and does not
change its centered projection. -/
theorem tracialCenter_sub_trace (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (a : R) :
    tracialCenter V (a - τ a • 1) = tracialCenter V a := by
  simp only [map_sub, map_smul, tracialCenter_one, smul_zero, sub_zero]

omit [StarRing R] in
theorem trace_sub_trace (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) (a : R) :
    τ (a - τ a • 1) = 0 := by
  simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]

omit [CompleteSpace E] in
/-- Trace-zero algebra vectors already lie in the centered subspace. -/
theorem tracial_vector_mem_centered (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (a : R) (ha : τ a = 0) : V a ∈ centeredSubspace (V 1) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hinner]
  simpa only [star_one, one_mul] using ha

omit [CompleteSpace E] in
/-- Inserting a centered trace-zero vector back into the full Hilbert space
recovers the original vector exactly. -/
theorem coe_tracialCenter_of_trace_zero (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (a : R) (ha : τ a = 0) : (tracialCenter V a : E) = V a := by
  exact (centeredSubspace (V 1)).starProjection_eq_self_iff.mpr
    (tracial_vector_mem_centered τ V hinner a ha)

omit [CompleteSpace E] in
/-- Orthogonal centering is precisely subtraction of the trace component. -/
theorem coe_tracialCenter (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b)) (hτ : τ 1 = 1)
    (a : R) : (tracialCenter V a : E) = V a - τ a • V 1 := by
  have h := coe_tracialCenter_of_trace_zero τ V hinner (a - τ a • 1)
    (trace_sub_trace τ hτ a)
  rw [tracialCenter_sub_trace] at h
  simpa only [map_sub, map_smul] using h

section Conjugation

variable [StarModule ℂ R]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V)

include hinner htrace in
omit [CompleteSpace E] [StarModule ℂ R] in
/-- The tracial identity makes algebraic involution isometric in the represented
Hilbert norm, even before a norm on the algebra has been specified. -/
theorem norm_tracial_star (a : R) : ‖V (star a)‖ = ‖V a‖ := by
  have hs : ‖V (star a)‖ ^ 2 = ‖V a‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      hinner, hinner, star_star, htrace]
  nlinarith [norm_nonneg (V a), norm_nonneg (V (star a))]

end Conjugation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_TracialCornerCyclicity
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclicity of finite tracial corners from dense algebra vectors and
partial-isometry transport. No corner cyclicity or density is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete data of a tracial Hilbert representation. -/
structure TracialCornerGeometry (P H : Type*) [CStarAlgebra P]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  trace : P →ₗ[ℂ] ℂ
  vector : P →ₗ[ℂ] H
  left : P →⋆ₐ[ℂ] (H →L[ℂ] H)
  inner_vector : ∀ a b, inner ℂ (vector a) (vector b) = trace (star a * b)
  tracial : ∀ a b, trace (a * b) = trace (b * a)
  dense_vector : DenseRange vector
  left_vector : ∀ a b, left a (vector b) = vector (a * b)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcFourier
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered arc, its exact second moment, and its nonzero Fourier
coefficients, computed using normalized angular Lebesgue integration. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Set

/-- A representative of the centered arc indicator; endpoints have measure zero. -/
def centeredArc (θ x : ℝ) : ℝ :=
  (Ioc (-θ) θ).indicator (fun _ => (1 : ℝ)) x - θ / Real.pi

/-- The normalized angular Fourier transform of the actual centered arc. -/
def arcFourierIntegral (θ : ℝ) (l : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ x in -Real.pi..Real.pi,
      (centeredArc θ x : ℂ) * Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralFourier
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact dihedral word identity and the finite Fourier matrix entries. -/

noncomputable section
namespace KadisonSimilarity

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The corner of a symmetry, written algebraically. -/
def dihedralHalfProjection (d : Rˣ) : R := (1 / 2 : ℂ) • (1 + (d : R))

end Algebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_OrthogonalColumns
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orthogonal word levels and their full-codomain errors. -/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Assemble maps from the individual coordinates of a finite Hilbert sum. -/
def sumColumns {N : ℕ} (U : Fin N → H →L[ℂ] K) : HilbertCopies H N →L[ℂ] K :=
  ∑ i : Fin N, (U i).comp (PiLp.proj 2 (fun _ : Fin N => H) i)

@[simp] theorem sumColumns_apply {N : ℕ} (U : Fin N → H →L[ℂ] K)
    (x : HilbertCopies H N) : sumColumns U x = ∑ i : Fin N, U i (x i) := by
  simp [sumColumns]

variable [CompleteSpace H] [CompleteSpace K]

@[simp] theorem sumColumns_adjoint_apply {N : ℕ} (U : Fin N → H →L[ℂ] K)
    (y : K) (i : Fin N) : (sumColumns U).adjoint y i = (U i).adjoint y := by
  apply ext_inner_left ℂ
  intro x
  have h := adjoint_inner_right (sumColumns U) (PiLp.single 2 i x) y
  have hsum : sumColumns U (PiLp.single 2 i x) = U i x := by
    simp only [sumColumns_apply, PiLp.single_apply, apply_ite, map_zero]
    simp
  rw [hsum] at h
  have hin : inner ℂ (PiLp.single 2 i x) ((sumColumns U).adjoint y) =
      inner ℂ x ((sumColumns U).adjoint y i) := by
    rw [PiLp.inner_apply]
    have hs := Finset.sum_eq_single (s := Finset.univ) i
      (f := fun j : Fin N => inner ℂ
        ((PiLp.single 2 i x : HilbertCopies H N) j) ((sumColumns U).adjoint y j))
      (by intro j _ hji; simp [hji]) (by simp)
    simpa only [PiLp.single_eq_same] using hs
  rw [hin] at h
  exact h.trans (adjoint_inner_right (U i) x y).symm


end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeExpectation
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The expectation of a free compression

Scalar tracial freeness is expressed by vanishing alternating centered words.
The formula `E(e b e) = τ(e)^2 b` is derived by testing against the second
algebra, rather than included among the free-product input data.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

/-- An alternating word of centered letters in two specified algebras. -/
inductive AlternatingCenteredWord (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) :
    Bool → List R → Prop
  | nil (side : Bool) : AlternatingCenteredWord τ P Q side []
  | cons {side : Bool} {x : R} {xs : List R}
      (hmem : x ∈ if side then P else Q) (hzero : τ x = 0)
      (htail : AlternatingCenteredWord τ P Q (!side) xs) :
      AlternatingCenteredWord τ P Q side (x :: xs)

/-- Scalar freeness, in the alternating-centered-word convention of the paper. -/
def ScalarFree (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) : Prop :=
  ∀ side x xs, AlternatingCenteredWord τ P Q side (x :: xs) → τ ((x :: xs).prod) = 0

/-- Centering uses the normalized trace. -/
def traceCentered (τ : R →ₗ[ℂ] ℂ) (a : R) : R := a - τ a • 1

theorem traceCentered_mem (τ : R →ₗ[ℂ] ℂ) (P : StarSubalgebra ℂ R)
    {a : R} (ha : a ∈ P) : traceCentered τ a ∈ P :=
  P.sub_mem ha (P.smul_mem (P.one_mem) _)

omit [StarRing R] [StarModule ℂ R] in
@[simp] theorem traceCentered_trace (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) (a : R) :
    τ (traceCentered τ a) = 0 := by simp [traceCentered, hτ]

omit [StarRing R] [StarModule ℂ R] in
theorem traceCentered_add (τ : R →ₗ[ℂ] ℂ) (a : R) :
    traceCentered τ a + τ a • 1 = a := sub_add_cancel _ _

/-- The trace pairing determines the conditional expectation in a faithful
tracial representation. -/
theorem expectation_eq_of_trace_pairings
    (τ : R →ₗ[ℂ] ℂ) (Q : StarSubalgebra ℂ R)
    (hfaithful : ∀ z, τ (star z * z) = 0 → z = 0)
    (E : R →ₗ[ℂ] R) (hE : ∀ x, E x ∈ Q)
    (htrace : ∀ x c, c ∈ Q → τ (c * E x) = τ (c * x))
    (x y : R) (hy : y ∈ Q)
    (hxy : ∀ c, c ∈ Q → τ (c * x) = τ (c * y)) : E x = y := by
  apply sub_eq_zero.mp
  apply hfaithful
  have hc : star (E x - y) ∈ Q := star_mem (Q.sub_mem (hE x) hy)
  rw [mul_sub, map_sub, htrace x _ hc, hxy _ hc, sub_self]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeDihedral
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar and reflection-coset moments of two free centered symmetries,
derived directly from alternating-centered-word freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

def pairedWord (d s : R) : ℕ → List R
  | 0 => []
  | n + 1 => d :: s :: pairedWord d s n

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem pairedWord_prod (d s : R) (n : ℕ) :
    (pairedWord d s n).prod = (d * s) ^ n := by
  induction n with
  | zero => simp [pairedWord]
  | succ n ih => simp only [pairedWord, List.prod_cons, ih, pow_succ']; simp [mul_assoc]

theorem pairedWord_alternating
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0) (n : ℕ) :
    AlternatingCenteredWord τ P Q true (pairedWord d s n) := by
  induction n with
  | zero => exact .nil true
  | succ n ih => exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

/-- Exchanging the free factors exchanges the alternating starting side. -/
theorem ScalarFree.symm {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}
    (h : ScalarFree τ P Q) : ScalarFree τ Q P := by
  intro side x xs hw
  apply h (!side) x xs
  have swap : ∀ {side : Bool} {w : List R}, AlternatingCenteredWord τ Q P side w →
      AlternatingCenteredWord τ P Q (!side) w := by
    intro side w hw
    induction hw with
    | nil side => exact .nil (!side)
    | @cons side x xs hm hz ht ih =>
      apply AlternatingCenteredWord.cons (by cases side <;> simpa using hm) hz
      simpa using ih
  exact swap hw

/-- Every positive power of the product of free centered letters has trace zero. -/
theorem ScalarFree.trace_pair_power {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}
    (hf : ScalarFree τ P Q) {d s : R}
    (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)
    {n : ℕ} (hn : 0 < n) : τ ((d * s) ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have ha := pairedWord_alternating τ P Q hd hs hd0 hs0 (m + 1)
  have ht := hf true d (s :: pairedWord d s m) ha
  rw [← pairedWord_prod d s (m + 1)]
  exact ht

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordOrthogonality
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Orthogonality of the actual dihedral word inclusions

Alternating-centered-word freeness computes the tracial pairing of the words
`e (s d)^k a`. The algebraic calculation only needs `e` in the first free
algebra; its projection and support properties enter when these pairings are
used to construct the normalized Hilbert-space inclusions.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

def dihedralPairs (x y : R) : ℕ → List R
  | 0 => []
  | n + 1 => x :: y :: dihedralPairs x y n

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem dihedralPairs_prod (x y : R) (n : ℕ) :
    (dihedralPairs x y n).prod = (x * y) ^ n := by
  induction n with
  | zero => simp [dihedralPairs]
  | succ n ih => simp only [dihedralPairs, List.prod_cons, ih, pow_succ']; simp [mul_assoc]

def dihedralSandwich (d s e : R) : ℕ → ℕ → List R
  | 0, j => e :: dihedralPairs s d j
  | k + 1, j => d :: s :: dihedralSandwich d s e k j

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem dihedralSandwich_prod (d s e : R) (k j : ℕ) :
    (dihedralSandwich d s e k j).prod = (d * s) ^ k * e * (s * d) ^ j := by
  induction k with
  | zero => simp [dihedralSandwich, dihedralPairs_prod]
  | succ k ih =>
    simp only [dihedralSandwich, List.prod_cons, ih, pow_succ']
    simp only [mul_assoc]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
  {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)

include hd hs hd0 hs0 in
theorem dihedralPairs_left_alternating (n : ℕ) :
    AlternatingCenteredWord τ P Q true (dihedralPairs d s n) := by
  induction n with
  | zero => exact .nil true
  | succ n ih => exact .cons (by simpa) hd0 (.cons (by simpa) hs0 ih)

include hd hs hd0 hs0 in
theorem dihedralPairs_right_alternating (n : ℕ) :
    AlternatingCenteredWord τ P Q false (dihedralPairs s d n) := by
  induction n with
  | zero => exact .nil false
  | succ n ih => exact .cons (by simpa) hs0 (.cons (by simpa) hd0 ih)

include hd hs hd0 hs0 in
theorem dihedralSandwich_alternating {e : R} (he : e ∈ P) (he0 : τ e = 0)
    (k j : ℕ) : AlternatingCenteredWord τ P Q true (dihedralSandwich d s e k j) := by
  induction k with
  | zero => exact .cons (by simpa) he0 (dihedralPairs_right_alternating τ hd hs hd0 hs0 j)
  | succ k ih => exact .cons (by simpa) hd0 (.cons (by simpa) hs0 ih)

include hf in
theorem trace_nonempty_alternating (side : Bool) (xs : List R)
    (hxs : xs ≠ []) (halt : AlternatingCenteredWord τ P Q side xs) : τ xs.prod = 0 := by
  obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil hxs
  exact hf side x tail halt

include hd hs hd0 hs0 in
theorem dihedralPairs_append_alternating {a : R} (ha : a ∈ Q) (ha0 : τ a = 0)
    (n : ℕ) : AlternatingCenteredWord τ P Q false (dihedralPairs s d n ++ [a]) := by
  induction n with
  | zero => exact .cons (by simpa) ha0 (.nil true)
  | succ n ih => exact .cons (by simpa) hs0 (.cons (by simpa) hd0 ih)

include hτ hf hd hs hd0 hs0 in
/-- Every positive residual dihedral power pairs trivially with the entire
second algebra, from either orientation. -/
theorem trace_test_dihedral_power (htr : ∀ a b, τ (a * b) = τ (b * a))
    {a : R} (ha : a ∈ Q) {n : ℕ} (hn : 0 < n) :
    τ (a * (d * s) ^ n) = 0 ∧ τ (a * (s * d) ^ n) = 0 := by
  have ha0 := traceCentered_trace τ hτ a
  have ham := traceCentered_mem τ Q ha
  have hp : τ (traceCentered τ a * (d * s) ^ n) = 0 := by
    have hw := hf false (traceCentered τ a) (dihedralPairs d s n)
      (.cons (by simpa using ham) ha0 (dihedralPairs_left_alternating τ hd hs hd0 hs0 n))
    simpa only [List.prod_cons, dihedralPairs_prod] using hw
  have hm : τ ((s * d) ^ n * traceCentered τ a) = 0 := by
    have hw := trace_nonempty_alternating τ hf false
      (dihedralPairs s d n ++ [traceCentered τ a]) (by simp)
      (dihedralPairs_append_alternating τ hd hs hd0 hs0 ham ha0 n)
    simpa only [List.prod_append, List.prod_singleton, dihedralPairs_prod] using hw
  have hpp := hf.trace_pair_power hd hs hd0 hs0 hn
  have hmp := hf.symm.trace_pair_power hs hd hs0 hd0 hn
  constructor
  · rw [← traceCentered_add τ a, add_mul, smul_mul_assoc, one_mul, map_add, map_smul,
      hp, hpp, smul_zero, add_zero]
  · rw [htr a ((s * d) ^ n), ← traceCentered_add τ a, mul_add, mul_smul_comm,
      mul_one, map_add, map_smul, hm, hmp, smul_zero, add_zero]

include hτ hf hd hs hd0 hs0 in
/-- A centered first-algebra letter between the two dihedral halves has zero
trace against every second-algebra coefficient. -/
theorem trace_centered_dihedral_sandwich {e a : R} (he : e ∈ P) (he0 : τ e = 0)
    (ha : a ∈ Q) (k j : ℕ) : τ (a * ((d * s) ^ k * e * (s * d) ^ j)) = 0 := by
  have halt := dihedralSandwich_alternating τ hd hs hd0 hs0 he he0 k j
  have hnonempty : dihedralSandwich d s e k j ≠ [] := by
    cases k <;> simp [dihedralSandwich]
  have heword : τ ((d * s) ^ k * e * (s * d) ^ j) = 0 := by
    simpa only [dihedralSandwich_prod] using trace_nonempty_alternating τ hf true _ hnonempty halt
  have haword : τ (traceCentered τ a * ((d * s) ^ k * e * (s * d) ^ j)) = 0 := by
    have h := hf false (traceCentered τ a) (dihedralSandwich d s e k j)
      (.cons (by simpa using traceCentered_mem τ Q ha) (traceCentered_trace τ hτ a) halt)
    simpa only [List.prod_cons, dihedralSandwich_prod] using h
  rw [← traceCentered_add τ a, add_mul, smul_mul_assoc, one_mul, map_add, map_smul,
    haword, heword, smul_zero, add_zero]

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem dihedral_cancel_successors (hdd : d * d = 1) (hss : s * s = 1)
    (k j : ℕ) : (d * s) ^ (k + 1) * (s * d) ^ (j + 1) = (d * s) ^ k * (s * d) ^ j := by
  have hxy : (d * s) * (s * d) = 1 := by
    rw [mul_assoc d s (s * d), ← mul_assoc s s d, hss, one_mul, hdd]
  rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc (d * s) (s * d), hxy, one_mul]

include hτ hf hd hs hd0 hs0 in
theorem trace_test_dihedral_product (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hdd : d * d = 1) (hss : s * s = 1) {a : R} (ha : a ∈ Q) (k j : ℕ) :
    τ (a * ((d * s) ^ k * (s * d) ^ j)) = if k = j then τ a else 0 := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => simp
    | succ j =>
      simpa using (trace_test_dihedral_power τ hτ hf hd hs hd0 hs0 htr ha (Nat.succ_pos j)).2
  | succ k ih =>
    cases j with
    | zero =>
      simpa using (trace_test_dihedral_power τ hτ hf hd hs hd0 hs0 htr ha (Nat.succ_pos k)).1
    | succ j =>
      rw [dihedral_cancel_successors hdd hss]
      simpa only [Nat.succ.injEq] using ih j

include hτ hf hd hs hd0 hs0 in
/-- The scalar trace of the middle letter is the only surviving contribution
to the diagonal word pairing. -/
theorem trace_dihedral_sandwich (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hdd : d * d = 1) (hss : s * s = 1) {e a : R} (he : e ∈ P) (ha : a ∈ Q)
    (k j : ℕ) :
    τ (a * ((d * s) ^ k * e * (s * d) ^ j)) = if k = j then τ e * τ a else 0 := by
  have hexpand : a * ((d * s) ^ k * e * (s * d) ^ j) =
      a * ((d * s) ^ k * traceCentered τ e * (s * d) ^ j) +
      τ e • (a * ((d * s) ^ k * (s * d) ^ j)) := by
    conv_lhs => rw [← traceCentered_add τ e]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hexpand, map_add, map_smul,
    trace_centered_dihedral_sandwich τ hτ hf hd hs hd0 hs0
      (traceCentered_mem τ P he) (traceCentered_trace τ hτ e) ha,
    trace_test_dihedral_product τ hτ hf hd hs hd0 hs0 htr hdd hss ha, zero_add]
  split_ifs <;> simp_all only [smul_eq_mul, mul_zero]

include hτ hf hd hs hd0 hs0 in
/-- The exact inner-product identity for the unnormalized word maps
`v ↦ e (s d)^k v`. No projection or support hypothesis on `e` is needed for
this tracial sandwich identity. -/
theorem dihedral_word_pairing (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hdd : d * d = 1) (hss : s * s = 1) {e v w : R}
    (he : e ∈ P) (hv : v ∈ Q) (hw : w ∈ Q) (k j : ℕ) :
    τ (star v * (d * s) ^ k * e * (s * d) ^ j * w) =
      if k = j then τ e * τ (star v * w) else 0 := by
  calc
    _ = τ (w * (star v * (d * s) ^ k * e * (s * d) ^ j)) := htr _ w
    _ = τ ((w * star v) * ((d * s) ^ k * e * (s * d) ^ j)) := by
      congr 1
      simp only [mul_assoc]
    _ = if k = j then τ e * τ (w * star v) else 0 :=
      trace_dihedral_sandwich τ hτ hf hd hs hd0 hs0 htr hdd hss he
        (Q.mul_mem hw (show star v ∈ Q from star_mem hv)) k j
    _ = _ := by rw [htr w (star v)]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordIsometries
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized dihedral word inclusions on actual tracial Hilbert spaces. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The unnormalized algebraic word inclusion. -/
def dihedralWordMap (Q : StarSubalgebra ℂ R) (V : R →ₗ[ℂ] E) (e d s : R)
    (k : ℕ) : Q →ₗ[ℂ] E where
  toFun a := V (e * (s * d) ^ k * (a : R))
  map_add' a b := by
    change V (e * (s * d) ^ k * ((a : R) + (b : R))) = _
    rw [mul_add, map_add]
  map_smul' c a := by
    change V (e * (s * d) ^ k * (c • (a : R))) = _
    rw [mul_smul_comm, map_smul, RingHom.id_apply]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  (htr : ∀ a b, τ (a * b) = τ (b * a))
  (V : R →ₗ[ℂ] E) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
  (d s e : R) (hd : d ∈ P) (hs : s ∈ Q) (he : e ∈ P)
  (hd0 : τ d = 0) (hs0 : τ s = 0)
  (hdd : d * d = 1) (hss : s * s = 1)
  (hdstar : star d = d) (hsstar : star s = s)
  (hestar : star e = e) (hee : e * e = e)

include hτ htr hinner hf hd hs he hd0 hs0 hdd hss hdstar hsstar hestar hee in
omit [CompleteSpace E] in
/-- The projection and selfadjointness hypotheses turn the tracial sandwich
formula into the actual Hilbert inner products of the word maps. -/
theorem inner_dihedralWordMap (k j : ℕ) (a b : Q) :
    inner ℂ (dihedralWordMap Q V e d s k a) (dihedralWordMap Q V e d s j b) =
      if k = j then τ e * τ (star (a : R) * (b : R)) else 0 := by
  change inner ℂ (V (e * (s * d) ^ k * (a : R)))
    (V (e * (s * d) ^ j * (b : R))) = _
  rw [hinner]
  have heq : star (e * (s * d) ^ k * (a : R)) * (e * (s * d) ^ j * (b : R)) =
      star (a : R) * (d * s) ^ k * e * (s * d) ^ j * (b : R) := by
    simp only [star_mul, star_pow, hdstar, hsstar, hestar]
    calc
      _ = star (a : R) * (d * s) ^ k * (e * e) * (s * d) ^ j * (b : R) := by
        noncomm_ring
      _ = _ := by rw [hee]
  rw [heq]
  exact dihedral_word_pairing τ hτ hf hd hs hd0 hs0 htr hdd hss he a.property b.property k j

/-- The actual normalization factor `t⁻¹ᐟ²`. -/
def dihedralNormalization (t : ℝ) : ℂ := ((Real.sqrt t)⁻¹ : ℝ)

theorem dihedralNormalization_identity {t : ℝ} (ht : 0 < t) :
    star (dihedralNormalization t) * dihedralNormalization t * (t : ℂ) = 1 := by
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hn : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = (1 : ℝ) := by
    calc
      _ = (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * (Real.sqrt t * Real.sqrt t) :=
        congrArg (fun z : ℝ => (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * z)
          (Real.mul_self_sqrt ht.le).symm
      _ = 1 := by field_simp
  have hstar : star (dihedralNormalization t) = dihedralNormalization t := by
    simp [dihedralNormalization]
  rw [hstar]
  unfold dihedralNormalization
  exact_mod_cast hn

/-- The normalized algebraic word map whose Hilbert extension is isometric. -/
def normalizedDihedralWordMap (t : ℝ) (k : ℕ) : Q →ₗ[ℂ] E :=
  dihedralNormalization t • dihedralWordMap Q V e d s k

variable (VA : Q →ₗ[ℂ] K)
  (hA : ∀ a b : Q, inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)))
  (t : ℝ) (ht : 0 < t) (hte : τ e = (t : ℂ))

include hτ htr hinner hf hd hs he hd0 hs0 hdd hss hdstar hsstar hestar hee hA ht hte in
omit [CompleteSpace E] in
theorem inner_normalizedDihedralWordMap (k j : ℕ) (a b : Q) :
    inner ℂ (normalizedDihedralWordMap V Q d s e t k a)
      (normalizedDihedralWordMap V Q d s e t j b) =
      if k = j then inner ℂ (VA a) (VA b) else 0 := by
  change inner ℂ (dihedralNormalization t • dihedralWordMap Q V e d s k a)
    (dihedralNormalization t • dihedralWordMap Q V e d s j b) = _
  rw [inner_smul_left, inner_smul_right,
    inner_dihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte, hte, hA]
    change star (dihedralNormalization t) *
      (dihedralNormalization t * ((t : ℂ) * τ (star (a : R) * (b : R)))) = _
    calc
      _ = (star (dihedralNormalization t) * dihedralNormalization t * (t : ℂ)) *
          τ (star (a : R) * (b : R)) := by ring
      _ = _ := by rw [dihedralNormalization_identity ht, one_mul]
  · simp only [hkj, ↓reduceIte, mul_zero]

include hτ htr hinner hf hd hs he hd0 hs0 hdd hss hdstar hsstar hestar hee hA ht hte in
omit [CompleteSpace E] in
theorem norm_normalizedDihedralWordMap (k : ℕ) (a : Q) :
    ‖normalizedDihedralWordMap V Q d s e t k a‖ = ‖VA a‖ := by
  have hn : ‖normalizedDihedralWordMap V Q d s e t k a‖ ^ 2 = ‖VA a‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
        hdstar hsstar hestar hee VA hA t ht hte]
    simp
  nlinarith [norm_nonneg (normalizedDihedralWordMap V Q d s e t k a), norm_nonneg (VA a)]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ActualArcCompression
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow-arc finite Fourier compression with actual normalized tracial
dihedral word inclusions. Their formulas and orthogonality are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Algebra ℂ R] [StarModule ℂ R] [StarRing R] in
theorem involution_unit_val_mul_self (d : Rˣ) (hd : d⁻¹ = d) :
    (d : R) * (d : R) = 1 := by
  have hu : d * d = 1 := by simpa only [hd] using inv_mul_cancel d
  exact congrArg (fun u : Rˣ => (u : R)) hu

omit [Algebra ℂ R] [StarModule ℂ R] in
theorem involution_unit_val_star (d : Rˣ) (hd : star d = d) : star (d : R) = (d : R) := by
  simpa only [Units.coe_star] using congrArg (fun u : Rˣ => (u : R)) hd

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Hyperreflexivity
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Arveson commutant-distance formula reduces hyperreflexivity to
uniform matrix commutator bounds and the scalar spectral estimate.
The formula is recorded in Christensen, Sinclair, Smith and White,
*Perturbations of C*-algebraic invariants*, Geom. Funct. Anal. 20 (2010),
368–397, Equation (2.1). -/

noncomputable section

namespace KadisonSimilarity

universe u

open scoped ENNReal

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Completely bounded norm of the inner derivation restricted to `P`.
The extended nonnegative real value permits this norm to be infinite before
an estimate has been proved. Matrix norms are the concrete Hilbert norms. -/
def completeCommutatorNorm (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (_ : ∀ i j, X i j ∈ P) (_ : ‖matrixOperator X‖ ≤ 1),
    ENNReal.ofReal ‖commutator (amplify Y n) (matrixOperator X)‖

/-- The specialization of CSSW (2010), Equation (2.1), used for this operator.
`M` is already equal to its double commutant by its `VonNeumannAlgebra` structure. -/
def ArvesonDistanceFormula (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : Prop :=
  completeCommutatorNorm M.commutant T =
    ENNReal.ofReal (2 * Metric.infDist T (M : Set (H →L[ℂ] H)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_EvenAlternatingWords
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Under a tracial functional, vanishing of nonempty even alternating
centered words implies scalar freeness. The odd-word step rotates the last
letter next to the first, centers their product, and shortens the word. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}

namespace AlternatingCenteredWord

/-- Any prefix retains the starting side and centered alternation. -/
theorem take_prefix {side : Bool} {xs ys : List R}
    (h : AlternatingCenteredWord τ P Q side (xs ++ ys)) :
    AlternatingCenteredWord τ P Q side xs := by
  induction xs generalizing side with
  | nil => exact .nil side
  | cons x xs ih =>
    cases h with
    | cons hm hz ht => exact .cons hm hz (ih ht)

/-- After an even prefix, the last letter lies in the starting algebra. -/
theorem last_mem_of_even_prefix {side : Bool} (xs : List R) (z : R)
    (h : AlternatingCenteredWord τ P Q side (xs ++ [z]))
    (heven : xs.length % 2 = 0) : z ∈ (if side then P else Q) := by
  induction xs using List.twoStepInduction generalizing side with
  | nil =>
    cases h with
    | cons hm _ _ => exact hm
  | singleton x => simp at heven
  | cons_cons x y xs ih _ =>
    cases h with
    | cons _ _ ht =>
      cases ht with
      | cons _ _ ht =>
        apply ih (side := side)
        · simpa only [Bool.not_not, List.append_eq] using ht
        · simp only [List.length_cons] at heven
          omega

/-- Appending the opposite-algebra letter closes an odd alternating word. -/
theorem append_of_odd_length {side : Bool} (xs : List R) (z : R)
    (h : AlternatingCenteredWord τ P Q side xs)
    (hodd : xs.length % 2 = 1) (hz : z ∈ (if !side then P else Q))
    (hz0 : τ z = 0) :
    AlternatingCenteredWord τ P Q side (xs ++ [z]) := by
  induction xs using List.twoStepInduction generalizing side with
  | nil => simp at hodd
  | singleton x =>
    cases h with
    | cons hm h0 _ =>
      exact .cons hm h0 (.cons hz hz0 (.nil _))
  | cons_cons x y xs ih _ =>
    cases h with
    | cons hm h0 ht =>
      cases ht with
      | cons hm' h0' ht' =>
        have htail : AlternatingCenteredWord τ P Q side xs := by
          simpa only [Bool.not_not] using ht'
        have hp : xs.length % 2 = 1 := by
          simp only [List.length_cons] at hodd
          omega
        exact .cons hm h0 (.cons hm' h0' (by
          simpa only [Bool.not_not, List.append_eq] using ih htail hp hz))

end AlternatingCenteredWord

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CStarCorner
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unital C-star algebra cut out by a projection. Its identity
is the projection, and its norm is the ambient norm. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

def cstarCornerSubalgebra (e : P) (he : IsStarProjection e) : NonUnitalStarSubalgebra ℂ P where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' ha hb := by
    exact ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  mul_mem' ha hb := by
    constructor
    · rw [← mul_assoc, ha.1]
    · rw [mul_assoc, hb.2]
  smul_mem' c a ha := by
    constructor
    · rw [mul_smul_comm, ha.1]
    · rw [smul_mul_assoc, ha.2]
  star_mem' ha := by
    constructor
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha.2
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha.1

instance cstarCornerSubalgebra_closed (e : P) (he : IsStarProjection e) :
    IsClosed (cstarCornerSubalgebra e he : Set P) :=
  (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_eq (by fun_prop) continuous_id)

abbrev CStarCorner (e : P) (he : IsStarProjection e) := cstarCornerSubalgebra e he

namespace CStarCorner

variable (e : P) (he : IsStarProjection e)

instance instIsUnitalSubtypeMemNonUnitalStarSubalgebraComplex : IsUnital (CStarCorner e he) := by
  refine ⟨⟨⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩, ?_⟩⟩
  intro a
  exact ⟨Subtype.ext a.property.1, Subtype.ext a.property.2⟩

instance instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex : NormedRing (CStarCorner e he) := IsUnital.toNormedRing

instance instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra : Algebra ℂ (CStarCorner e he) := Algebra.ofModule smul_mul_assoc mul_smul_comm

instance instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra : NormedAlgebra ℂ (CStarCorner e he) where
  norm_smul_le := norm_smul_le

instance instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex : CStarAlgebra (CStarCorner e he) where

instance instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex : PartialOrder (CStarCorner e he) := CStarAlgebra.spectralOrder _

instance instStarOrderedRingSubtypeMemNonUnitalStarSubalgebraComplex : StarOrderedRing (CStarCorner e he) := CStarAlgebra.spectralOrderedRing _

@[simp] theorem coe_one : ((1 : CStarCorner e he) : P) = e := by
  have h := congrArg (fun a : CStarCorner e he => (a : P))
    (one_mul (⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩ : CStarCorner e he))
  exact (1 : CStarCorner e he).property.2.symm.trans h

/-- Every ambient compression is an element of the corner. -/
def compress (a : P) : CStarCorner e he := ⟨e * a * e, by
  constructor
  · calc
      e * (e * a * e) = (e * e) * a * e := by noncomm_ring
      _ = e * a * e := by rw [he.isIdempotentElem.eq]
  · rw [mul_assoc, he.isIdempotentElem.eq]⟩

@[simp] theorem coe_compress (a : P) : (compress e he a : P) = e * a * e := rfl

end CStarCorner
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialExpectations
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace-pairing description of conditional expectation. Its uniqueness,
bimodule law, tower law, and Hilbert projection formula are derived here. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The minimal trace-pairing data for expectation onto a tracial subalgebra.
Existence is required only when a subalgebra is realized as a von Neumann
subalgebra; no existence assertion for arbitrary star subalgebras is made. -/
structure TracialExpectation (τ : P →ₗ[ℂ] ℂ) (A : StarSubalgebra ℂ P) where
  map : P →ₗ[ℂ] P
  range : ∀ x, map x ∈ A
  pairing : ∀ x c, c ∈ A → τ (c * map x) = τ (c * x)

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {A : StarSubalgebra ℂ P}
  (E : TracialExpectation τ A)

variable (hf : ∀ x, τ (star x * x) = 0 → x = 0)

include hf

/-- The trace pairing determines each expectation value uniquely. -/
theorem eq_of_pairings (x y : P) (hy : y ∈ A)
    (hxy : ∀ c, c ∈ A → τ (c * x) = τ (c * y)) : E.map x = y :=
  expectation_eq_of_trace_pairings τ A hf E.map E.range E.pairing x y hy hxy

/-- Left bimodularity follows from the trace-pairing characterization alone. -/
theorem map_mul_left (a x : P) (ha : a ∈ A) : E.map (a * x) = a * E.map x := by
  apply E.eq_of_pairings hf _ _ (A.mul_mem ha (E.range x))
  intro c hc
  simpa only [mul_assoc] using (E.pairing x (c * a) (A.mul_mem hc ha)).symm

/-- Right bimodularity additionally uses traciality. -/
theorem map_mul_right (htr : ∀ x y, τ (x * y) = τ (y * x))
    (x b : P) (hb : b ∈ A) : E.map (x * b) = E.map x * b := by
  apply E.eq_of_pairings hf _ _ (A.mul_mem (E.range x) hb)
  intro c hc
  calc
    τ (c * (x * b)) = τ ((b * c) * x) := by rw [← mul_assoc, htr, mul_assoc]
    _ = τ ((b * c) * E.map x) := (E.pairing x (b * c) (A.mul_mem hb hc)).symm
    _ = τ (c * (E.map x * b)) := by rw [mul_assoc, htr, mul_assoc]

end TracialExpectation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerExpectations
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting a tracial expectation to a corner. The normalized corner
trace and the restricted expectation are constructed from the ambient ones. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CStarCorner

variable (p : P) (hp : IsStarProjection p)

/-- The part of an ambient unital star algebra lying in the corner. -/
def subalgebra (A : StarSubalgebra ℂ P) (hpA : p ∈ A) :
    StarSubalgebra ℂ (CStarCorner p hp) where
  carrier := {x | (x : P) ∈ A}
  zero_mem' := A.zero_mem
  one_mem' := by
    change ((1 : CStarCorner p hp) : P) ∈ A
    rw [coe_one]
    exact hpA
  add_mem' := fun ha hb => A.add_mem ha hb
  mul_mem' := fun ha hb => A.mul_mem ha hb
  algebraMap_mem' c := by
    change ((algebraMap ℂ (CStarCorner p hp) c : CStarCorner p hp) : P) ∈ A
    rw [Algebra.algebraMap_eq_smul_one]
    change c • ((1 : CStarCorner p hp) : P) ∈ A
    rw [coe_one]
    exact A.smul_mem hpA c
  star_mem' := by
    intro a ha
    change star (a : P) ∈ A
    exact star_mem ha

@[simp] theorem mem_subalgebra (A : StarSubalgebra ℂ P) (hpA : p ∈ A)
    (x : CStarCorner p hp) : x ∈ subalgebra p hp A hpA ↔ (x : P) ∈ A := Iff.rfl

/-- Normalize the ambient trace by the trace of the corner identity. -/
def normalizedTrace (τ : P →ₗ[ℂ] ℂ) : CStarCorner p hp →ₗ[ℂ] ℂ where
  toFun x := (τ p)⁻¹ * τ (x : P)
  map_add' x y := by simp only [NonUnitalStarSubalgebra.coe_add, map_add, mul_add]
  map_smul' c x := by
    change (τ p)⁻¹ * τ (c • (x : P)) = c * ((τ p)⁻¹ * τ (x : P))
    rw [map_smul, smul_eq_mul]
    ring

@[simp] theorem normalizedTrace_apply (τ : P →ₗ[ℂ] ℂ) (x : CStarCorner p hp) :
    normalizedTrace p hp τ x = (τ p)⁻¹ * τ (x : P) := rfl

theorem normalizedTrace_tracial (τ : P →ₗ[ℂ] ℂ)
    (htr : ∀ x y, τ (x * y) = τ (y * x)) (x y : CStarCorner p hp) :
    normalizedTrace p hp τ (x * y) = normalizedTrace p hp τ (y * x) := by
  change (τ p)⁻¹ * τ ((x : P) * (y : P)) = (τ p)⁻¹ * τ ((y : P) * (x : P))
  rw [htr]

end CStarCorner

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P}
  (E : TracialExpectation τ C)
  (hf : ∀ x, τ (star x * x) = 0 → x = 0)
  (htr : ∀ x y, τ (x * y) = τ (y * x))
  (p : P) (hp : IsStarProjection p) (hpC : p ∈ C)

include hf htr hpC in
/-- Bimodularity makes the ambient expectation preserve the corner. -/
theorem map_mem_corner (x : CStarCorner p hp) :
    E.map (x : P) ∈ cstarCornerSubalgebra p hp := by
  constructor
  · rw [← E.map_mul_left hf p (x : P) hpC, x.property.1]
  · rw [← E.map_mul_right hf htr (x : P) p hpC, x.property.2]

/-- The restriction is trace preserving for the normalized corner trace. -/
def corner : TracialExpectation (CStarCorner.normalizedTrace p hp τ)
    (CStarCorner.subalgebra p hp C hpC) where
  map :=
    { toFun := fun x => ⟨E.map (x : P), E.map_mem_corner hf htr p hp hpC x⟩
      map_add' := fun x y => Subtype.ext (E.map.map_add (x : P) (y : P))
      map_smul' := fun c x => Subtype.ext (E.map.map_smul c (x : P)) }
  range x := E.range (x : P)
  pairing x c hc := by
    change (τ p)⁻¹ * τ ((c : P) * E.map (x : P)) =
      (τ p)⁻¹ * τ ((c : P) * (x : P))
    rw [E.pairing (x : P) (c : P) hc]

@[simp] theorem corner_map_coe (x : CStarCorner p hp) :
    ((E.corner hf htr p hp hpC).map x : P) = E.map (x : P) := rfl

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded Borel spectral calculus input, specialized to the centered
arc of a Haar rotation in a finite dihedral von Neumann algebra. Blackadar,
Operator Algebras, I.6.2.4 and I.6.2.8, supply the calculus and commutation;
integration against its Haar spectral measure gives the stated moments.

The interface is local to the specified trace and algebra. Its intended
application has the normal finite trace and the von Neumann algebra generated
by the two symmetries. No existence assertion is made for an arbitrary C-star
subalgebra or an arbitrary linear functional. The corner estimates below are
proved from the spectral data, rather than included in the published input. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- Exactly the spectral data of the centered arc used in the argument. -/
structure DihedralSpectralArc (τ : P →ₗ[ℂ] ℂ) (C : StarSubalgebra ℂ P)
    (w d : Pˣ) (θ : ℝ) where
  element : P
  mem : element ∈ C
  selfAdjoint : star element = element
  norm_le : ‖element‖ ≤ 1
  commute_rotation : Commute element (w : P)
  commute_reflection : Commute element (d : P)
  rotation_moment : ∀ l : ℤ, τ (element * (↑(w ^ l) : P)) = arcFourierIntegral θ l
  reflection_moment : ∀ l : ℤ, τ ((element * (↑(w ^ l) : P)) * (d : P)) = 0
  square_moment : τ (element * element) = ((θ / Real.pi) * (1 - θ / Real.pi) : ℝ)
  square_reflection_moment : τ ((element * element) * (d : P)) = 0

namespace DihedralSpectralArc

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P} {w d : Pˣ} {θ : ℝ}
  (F : DihedralSpectralArc τ C w d θ)

theorem halfProjection_commutes :
    Commute F.element (dihedralHalfProjection d) := by
  change F.element * ((1 / 2 : ℂ) • (1 + (d : P))) =
    ((1 / 2 : ℂ) • (1 + (d : P))) * F.element
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    F.commute_reflection.eq]

end DihedralSpectralArc
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCutMoments
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from the continuous Haar functional calculus to the actual
open spectral projection, using its bounded strong resolvent limit. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorTrace (Ω : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ H Ω)

omit [CompleteSpace H] in
@[simp] theorem vectorTrace_apply (Ω : H) (T : H →L[ℂ] H) :
    vectorTrace Ω T = inner ℂ Ω (T Ω) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeWordInnerProducts
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inner-product recursion for reduced words. Freeness alone supplies
orthogonality at different first factors and contraction of matching first
letters. These are the algebraic identities needed for the tensor model. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {A D : StarSubalgebra ℂ R}

omit [Algebra ℂ R] [StarModule ℂ R] in
theorem star_list_prod (xs : List R) :
    star xs.prod = (xs.reverse.map star).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.reverse_cons, ih]

theorem AlternatingCenteredWord.star_reverse_append
    (hstar : ∀ x, τ (star x) = star (τ x))
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys) :
    ∃ s, AlternatingCenteredWord τ A D s (xs.reverse.map star ++ ys) := by
  induction hxs generalizing ys with
  | nil side => exact ⟨!side, by simpa using hys⟩
  | @cons side x xs hx hx0 hxs ih =>
    have hxstar : AlternatingCenteredWord τ A D side (star x :: ys) :=
      .cons (star_mem hx) (by rw [hstar, hx0, star_zero]) hys
    obtain ⟨s, hs⟩ := ih (ys := star x :: ys) (by simpa using hxstar)
    refine ⟨s, ?_⟩
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append] using hs

theorem ScalarFree.trace_of_nonempty (hf : ScalarFree τ A D)
    {side : Bool} {xs : List R} (hx : AlternatingCenteredWord τ A D side xs)
    (hne : xs ≠ []) : τ xs.prod = 0 := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs => exact hf side x xs hx

theorem ScalarFree.trace_opposite_words (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x))
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys)
    (hne : xs ≠ [] ∨ ys ≠ []) : τ (star xs.prod * ys.prod) = 0 := by
  obtain ⟨s, hs⟩ := hxs.star_reverse_append hstar hys
  have hn : xs.reverse.map star ++ ys ≠ [] := by
    simp only [ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff,
      List.reverse_eq_nil_iff]
    tauto
  have h := hf.trace_of_nonempty hs hn
  simpa only [List.prod_append, ← star_list_prod] using h

theorem ScalarFree.trace_centered_sandwich (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x))
    {side : Bool} {xs ys : List R} {b : R}
    (hxs : AlternatingCenteredWord τ A D (!side) xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys)
    (hb : b ∈ if side then A else D) (hb0 : τ b = 0) :
    τ (star xs.prod * b * ys.prod) = 0 := by
  have hy : AlternatingCenteredWord τ A D side (b :: ys) := .cons hb hb0 hys
  have h := hf.trace_opposite_words hstar hxs (by simpa using hy)
    (Or.inr (List.cons_ne_nil b ys))
  simpa only [List.prod_cons, mul_assoc] using h

theorem ScalarFree.trace_matching_heads (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {xs ys : List R} {a b : R}
    (ha : a ∈ if side then A else D) (hb : b ∈ if side then A else D)
    (hxs : AlternatingCenteredWord τ A D (!side) xs)
    (hys : AlternatingCenteredWord τ A D (!side) ys) :
    τ (star (a :: xs).prod * (b :: ys).prod) =
      τ (star a * b) * τ (star xs.prod * ys.prod) := by
  have hsa : star a ∈ (if side then A else D : StarSubalgebra ℂ R) :=
    star_mem (s := (if side then A else D : StarSubalgebra ℂ R)) ha
  have hab : star a * b ∈ (if side then A else D : StarSubalgebra ℂ R) :=
    (if side then A else D : StarSubalgebra ℂ R).mul_mem hsa hb
  have hc := traceCentered_mem τ (if side then A else D) hab
  have hz := hf.trace_centered_sandwich hstar hxs hys hc
    (traceCentered_trace τ hτ (star a * b))
  have he : star (a :: xs).prod * (b :: ys).prod =
      star xs.prod * traceCentered τ (star a * b) * ys.prod +
        τ (star a * b) • (star xs.prod * ys.prod) := by
    calc
      _ = star xs.prod * (star a * b) * ys.prod := by
        simp only [List.prod_cons, star_mul]
        noncomm_ring
      _ = star xs.prod * (traceCentered τ (star a * b) +
          τ (star a * b) • 1) * ys.prod := by rw [traceCentered_add]
      _ = _ := by
        simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [he, map_add, hz, map_smul, zero_add, smul_eq_mul]

/-- The scalar product of two equally oriented centered words. Unequal
lengths give zero, including a nonempty word paired with the vacuum. -/
def centeredWordPairing (τ : R →ₗ[ℂ] ℂ) : List R → List R → ℂ
  | [], [] => 1
  | a :: xs, b :: ys => τ (star a * b) * centeredWordPairing τ xs ys
  | _, _ => 0

theorem ScalarFree.trace_same_words (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D side ys) :
    τ (star xs.prod * ys.prod) = centeredWordPairing τ xs ys := by
  induction hxs generalizing ys with
  | nil side =>
    cases hys with
    | nil => simpa [centeredWordPairing] using hτ
    | @cons _ y ys hy hy0 hys =>
      simpa only [centeredWordPairing] using
        hf.trace_opposite_words hstar (.nil (!side)) (by simpa using
          (AlternatingCenteredWord.cons hy hy0 hys)) (Or.inr (List.cons_ne_nil y ys))
  | @cons side x xs hx hx0 hxs ih =>
    cases hys with
    | nil =>
      simpa only [centeredWordPairing] using
        hf.trace_opposite_words hstar (.cons hx hx0 hxs) (.nil (!side))
          (Or.inl (List.cons_ne_nil x xs))
    | @cons _ y ys hy hy0 hys =>
      rw [hf.trace_matching_heads hstar hτ hx hy hxs hys, ih hys]
      rfl

omit [StarModule ℂ R] in
theorem centeredWordPairing_eq_zero_of_length_ne {xs ys : List R}
    (h : xs.length ≠ ys.length) : centeredWordPairing τ xs ys = 0 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact (h rfl).elim
    | cons => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hn : xs.length ≠ ys.length := by simpa using h
      simp only [centeredWordPairing, ih hn, mul_zero]

theorem ScalarFree.trace_words_of_length_ne (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {side : Bool} {xs ys : List R}
    (hxs : AlternatingCenteredWord τ A D side xs)
    (hys : AlternatingCenteredWord τ A D side ys) (h : xs.length ≠ ys.length) :
    τ (star xs.prod * ys.prod) = 0 := by
  rw [hf.trace_same_words hstar hτ hxs hys, centeredWordPairing_eq_zero_of_length_ne h]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreePairWords
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regrouped free-product words have centered pairs internally and
unrestricted endpoints. Their trace pairing is the tensor product pairing. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {A D : StarSubalgebra ℂ R}

/-- A sequence of centered `A,D` pairs, including the empty sequence. -/
inductive CenteredPairWord (τ : R →ₗ[ℂ] ℂ) (A D : StarSubalgebra ℂ R) : List R → Prop
  | nil : CenteredPairWord τ A D []
  | cons {a d : R} {xs : List R} (ha : a ∈ A) (hd : d ∈ D)
      (ha0 : τ a = 0) (hd0 : τ d = 0) (hxs : CenteredPairWord τ A D xs) :
      CenteredPairWord τ A D (a :: d :: xs)

namespace CenteredPairWord

theorem alternating {xs : List R} (h : CenteredPairWord τ A D xs) :
    AlternatingCenteredWord τ A D true xs := by
  induction h with
  | nil => exact .nil true
  | cons ha hd ha0 hd0 _ ih =>
    exact .cons ha ha0 (.cons hd hd0 ih)

theorem alternating_append {xs : List R} (h : CenteredPairWord τ A D xs)
    {r : R} (hr : r ∈ A) (hr0 : τ r = 0) :
    AlternatingCenteredWord τ A D true (xs ++ [r]) := by
  induction h with
  | nil => exact .cons hr hr0 (.nil false)
  | cons ha hd ha0 hd0 _ ih =>
    exact .cons ha ha0 (.cons hd hd0 ih)

theorem even_length {xs : List R} (h : CenteredPairWord τ A D xs) :
    ∃ n : ℕ, xs.length = 2 * n := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | cons _ _ _ _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [List.length_cons]; omega⟩

end CenteredPairWord

theorem ScalarFree.trace_pairWords_right_centered (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {r : R} (hr : r ∈ A) (hr0 : τ r = 0) :
    τ (star xs.prod * ys.prod * r) = 0 := by
  have hlen : xs.length ≠ (ys ++ [r]).length := by
    obtain ⟨n, hn⟩ := hxs.even_length
    obtain ⟨m, hm⟩ := hys.even_length
    simp only [List.length_append, List.length_singleton]
    omega
  have h := hf.trace_words_of_length_ne hstar hτ hxs.alternating
    (hys.alternating_append hr hr0) hlen
  simpa only [List.prod_append, List.prod_singleton, mul_assoc] using h

theorem ScalarFree.trace_pairWords_centered_middle (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x))
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {q r : R}
    (hq : q ∈ D) (hq0 : τ q = 0) (hr : r ∈ A) (hτ : τ 1 = 1) :
    τ (star xs.prod * q * ys.prod * r) = 0 := by
  have h0 := hf.trace_centered_sandwich hstar hxs.alternating hys.alternating
    (side := false) hq hq0
  have h1 := hf.trace_centered_sandwich hstar hxs.alternating
    (hys.alternating_append (traceCentered_mem τ A hr) (traceCentered_trace τ hτ r))
    (side := false) hq hq0
  have h1' : τ (star xs.prod * q * ys.prod * traceCentered τ r) = 0 := by
    simpa only [List.prod_append, List.prod_singleton, mul_assoc] using h1
  calc
    _ = τ (star xs.prod * q * ys.prod * traceCentered τ r) +
        τ r * τ (star xs.prod * q * ys.prod) := by
      conv_lhs => rw [← traceCentered_add τ r]
      rw [mul_add, mul_smul_comm, mul_one, map_add, map_smul, smul_eq_mul]
    _ = 0 := by rw [h1', h0, mul_zero, add_zero]

/-- Full endpoints factor off from the inner product of centered pair words. -/
theorem ScalarFree.trace_pairWords_endpoints (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {q r : R} (hq : q ∈ D) (hr : r ∈ A) :
    τ (star xs.prod * q * ys.prod * r) =
      τ q * τ r * centeredWordPairing τ xs ys := by
  have h0 := hf.trace_pairWords_centered_middle hstar hxs hys
    (traceCentered_mem τ D hq) (traceCentered_trace τ hτ q) hr hτ
  have h1 := hf.trace_pairWords_right_centered hstar hτ hxs hys
    (traceCentered_mem τ A hr) (traceCentered_trace τ hτ r)
  have he : τ (star xs.prod * ys.prod * r) =
      τ r * centeredWordPairing τ xs ys := by
    calc
      _ = τ (star xs.prod * ys.prod * traceCentered τ r) +
          τ r * τ (star xs.prod * ys.prod) := by
        conv_lhs => rw [← traceCentered_add τ r]
        rw [mul_add, mul_smul_comm, mul_one, map_add, map_smul, smul_eq_mul]
      _ = _ := by rw [h1, zero_add, hf.trace_same_words hstar hτ
        hxs.alternating hys.alternating]
  calc
    _ = τ (star xs.prod * traceCentered τ q * ys.prod * r) +
        τ q * τ (star xs.prod * ys.prod * r) := by
      conv_lhs => rw [← traceCentered_add τ q]
      rw [mul_add, add_mul, add_mul, mul_smul_comm, mul_one, smul_mul_assoc,
        smul_mul_assoc, map_add, map_smul, smul_eq_mul]
    _ = _ := by rw [h0, zero_add, he, mul_assoc]

/-- Interleave two equally long lists of letters in their original order. -/
def pairWord : {n : ℕ} → (Fin n → R) → (Fin n → R) → List R
  | 0, _, _ => []
  | _ + 1, a, d => a 0 :: d 0 :: pairWord (Fin.tail a) (Fin.tail d)

omit [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
@[simp] theorem length_pairWord {n : ℕ} (a d : Fin n → R) :
    (pairWord a d).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pairWord, List.length_cons, ih]; omega

theorem CenteredPairWord.of_pairWord {n : ℕ} (a d : Fin n → R)
    (ha : ∀ i, a i ∈ A) (hd : ∀ i, d i ∈ D)
    (ha0 : ∀ i, τ (a i) = 0) (hd0 : ∀ i, τ (d i) = 0) :
    CenteredPairWord τ A D (pairWord a d) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    exact .cons (ha 0) (hd 0) (ha0 0) (hd0 0)
      (ih _ _ (fun i => ha i.succ) (fun i => hd i.succ)
        (fun i => ha0 i.succ) (fun i => hd0 i.succ))

omit [StarModule ℂ R] in
theorem centeredWordPairing_pairWord {n : ℕ} (a d b e : Fin n → R) :
    centeredWordPairing τ (pairWord a d) (pairWord b e) =
      (∏ i, τ (star (a i) * b i)) * ∏ i, τ (star (d i) * e i) := by
  induction n with
  | zero => simp [pairWord, centeredWordPairing]
  | succ n ih =>
    simp only [pairWord, centeredWordPairing, ih, Fin.prod_univ_succ, Fin.tail]
    ring

/-- The actual trace inner product of words with unrestricted endpoints. -/
theorem ScalarFree.trace_full_pairWords (hf : ScalarFree τ A D)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hτ : τ 1 = 1)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    {xs ys : List R} (hxs : CenteredPairWord τ A D xs)
    (hys : CenteredPairWord τ A D ys) {d e b c : R}
    (hd : d ∈ D) (he : e ∈ D) (hb : b ∈ A) (hc : c ∈ A) :
    τ (star (d * xs.prod * b) * (e * ys.prod * c)) =
      τ (star d * e) * τ (star b * c) * centeredWordPairing τ xs ys := by
  calc
    _ = τ (star b * (star xs.prod * (star d * e) * ys.prod * c)) := by
      congr 1
      simp only [star_mul]
      noncomm_ring
    _ = τ (star xs.prod * (star d * e) * ys.prod * (c * star b)) := by
      rw [htr]
      congr 1
      noncomm_ring
    _ = τ (star d * e) * τ (c * star b) * centeredWordPairing τ xs ys :=
      hf.trace_pairWords_endpoints hstar hτ hxs hys
        (D.mul_mem (star_mem (s := D) hd) he)
        (A.mul_mem hc (star_mem (s := A) hb))
    _ = _ := by rw [htr c (star b)]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixExtension
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise two-factor matrix-automorphism extension input. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

/-- Algebraic conjugation of a letter in the other factor. -/
def matrixConjugateLetter (c : D) : D :=
  ι (u : Matrix α α ℂ) * c * star (ι (u : Matrix α α ℂ))

@[simp] theorem matrixConjugateLetter_one (c : D) :
    matrixConjugateLetter D ι 1 c = c := by
  simp [matrixConjugateLetter]

theorem matrixConjugateLetter_mul (v : Matrix.unitaryGroup α ℂ) (c : D) :
    matrixConjugateLetter D ι (u * v) c =
      matrixConjugateLetter D ι u (matrixConjugateLetter D ι v c) := by
  simp only [matrixConjugateLetter, Submonoid.coe_mul, map_mul, star_mul, mul_assoc]

@[simp] theorem matrixConjugateLetter_inv (c : D) :
    matrixConjugateLetter D ι u⁻¹ (matrixConjugateLetter D ι u c) = c := by
  rw [← matrixConjugateLetter_mul, inv_mul_cancel, matrixConjugateLetter_one]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductAutomorphisms
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic extensions become actual automorphisms by tracial L² density.
The only extension input is the two-factor published embedding specialization. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The bounded factor algebra, before taking its tracial L² closure. -/
def factorAlgebra (A D : StarSubalgebra ℂ P) : StarSubalgebra ℂ P :=
  StarAlgebra.adjoin ℂ ((A : Set P) ∪ (D : Set P))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_OrthogonalWordLevels
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal word-level inclusions turn the proved off-diagonal block
vanishing into actual preservation of each full word level. -/

noncomputable section
namespace KadisonSimilarity

variable {W : ℕ → Type*} [∀ n, NormedAddCommGroup (W n)]
  [∀ n, InnerProductSpace ℂ (W n)] [∀ n, CompleteSpace (W n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual isometric word inclusions with orthogonal ranges and dense linear
span. No operator invariance is built into these geometric data. -/
structure OrthogonalWordLevels (W : ℕ → Type*) [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℂ (W n)] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  inclusion : ∀ n, W n →ₗᵢ[ℂ] H
  orthogonal : ∀ n m, n ≠ m → ∀ x y, inner ℂ (inclusion n x) (inclusion m y) = 0
  dense_span : (Submodule.span ℂ (⋃ n, Set.range (inclusion n))).topologicalClosure = ⊤

namespace OrthogonalWordLevels

variable (U : OrthogonalWordLevels W H)

def coordinate (n : ℕ) : H →L[ℂ] W n := (U.inclusion n).toContinuousLinearMap.adjoint

@[simp] theorem coordinate_inclusion_self (n : ℕ) (x : W n) :
    U.coordinate n (U.inclusion n x) = x := by
  exact congrArg (fun T : W n →L[ℂ] W n => T x) (U.inclusion n).adjoint_comp_self

end OrthogonalWordLevels

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordModel
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reduced-word part of the published free-product construction.

Ricard–Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2–3 of
arXiv:math/0505302, constructs the reduced free-product Hilbert space as the
orthogonal sum of alternating centered tensor words. Regrouping the first
and last factors gives the coordinates below. The input is only this word
construction, without any operator invariance or commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite alternating product, in its prescribed left-to-right order. -/
def alternatingProduct {n : ℕ} (a b : Fin n → P) : P :=
  (List.ofFn (fun i => a i * b i)).prod

@[simp] theorem alternatingProduct_zero (a b : Fin 0 → P) :
    alternatingProduct a b = 1 := by simp [alternatingProduct]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeWordHilbert
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gram matrices of the regrouped free-product word vectors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] tensorWordSpace

section Products
variable {R : Type*} [Monoid R]

theorem prod_pairWord {n : ℕ} (a d : Fin n → R) :
    (pairWord a d).prod = (List.ofFn (fun i => a i * d i)).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairWord, List.prod_cons, ih, List.ofFn_succ, Fin.tail, mul_assoc]

end Products

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedWordDensity
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary algebraic generation implies density of centered reduced words.
This is an algebraic centering argument, independent of freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

theorem alternatingProduct_cons {n : ℕ} (a c : Fin (n + 1) → P) :
    alternatingProduct a c = a 0 * c 0 *
      alternatingProduct (fun i => a i.succ) (fun i => c i.succ) := by
  simp only [alternatingProduct, List.ofFn_succ, List.prod_cons]

open scoped Pointwise
open TracialCornerGeometry

namespace CenteredWordSpan

variable (τ : P →ₗ[ℂ] ℂ) (A D : StarSubalgebra ℂ P)

def words : Set P := {x | ∃ (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D),
    (∀ i, τ (a i : P) = 0) ∧ (∀ i, τ (c i : P) = 0) ∧
      x = (d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P)}

def span : Submodule ℂ P := Submodule.span ℂ (words τ A D)

theorem word_mem (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, τ (a i : P) = 0) (hc : ∀ i, τ (c i : P) = 0) :
    (d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P) ∈ span τ A D :=
  Submodule.subset_span ⟨n, d, b, a, c, ha, hc, rfl⟩

theorem base_mem (b : A) : (b : P) ∈ span τ A D := by
  simpa only [alternatingProduct_zero, OneMemClass.coe_one, one_mul, mul_one] using
    word_mem τ A D 0 1 b Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

theorem one_mem : (1 : P) ∈ span τ A D := base_mem τ A D 1

theorem other_mul_word (x : D) (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, τ (a i : P) = 0) (hc : ∀ i, τ (c i : P) = 0) :
    (x : P) * ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)) ∈ span τ A D := by
  simpa only [MulMemClass.coe_mul, mul_assoc] using word_mem τ A D n (x * d) b a c ha hc

/-- Centering the first two letters reduces all remaining products to a
shorter word. -/
theorem base_mul_word (hτ : τ 1 = 1) (n : ℕ) (x : A) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, τ (a i : P) = 0) (hc : ∀ i, τ (c i : P) = 0) :
    (x : P) * ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)) ∈ span τ A D := by
  induction n generalizing x d b with
  | zero =>
    let x₀ : A := ⟨traceCentered τ (x : P), traceCentered_mem τ A x.property⟩
    let d₀ : D := ⟨traceCentered τ (d : P), traceCentered_mem τ D d.property⟩
    have hxd : (x₀ : P) * (d₀ : P) * (b : P) ∈ span τ A D := by
      simpa only [alternatingProduct_cons, alternatingProduct_zero, OneMemClass.coe_one,
        one_mul, mul_one, Fin.cons_zero] using
        word_mem τ A D 1 1 b (Fin.cons x₀ Fin.elim0) (Fin.cons d₀ Fin.elim0)
          (by intro i; fin_cases i; exact traceCentered_trace τ hτ x)
          (by intro i; fin_cases i; exact traceCentered_trace τ hτ d)
    have hdb : (d₀ : P) * (b : P) ∈ span τ A D := by
      simpa only [alternatingProduct_zero, mul_one] using
        word_mem τ A D 0 d₀ b Fin.elim0 Fin.elim0
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hxb := base_mem τ A D (x * b)
    have heq : (x : P) * (d : P) * (b : P) =
        (x₀ : P) * (d₀ : P) * (b : P) +
        τ (x : P) • ((d₀ : P) * (b : P)) + τ (d : P) • ((x : P) * (b : P)) := by
      dsimp only [x₀, d₀]
      simp only [traceCentered, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      module
    simpa only [alternatingProduct_zero, mul_one, ← mul_assoc, heq,
      MulMemClass.coe_mul] using
      (span τ A D).add_mem ((span τ A D).add_mem hxd ((span τ A D).smul_mem _ hdb))
        ((span τ A D).smul_mem _ hxb)
  | succ n ih =>
    let x₀ : A := ⟨traceCentered τ (x : P), traceCentered_mem τ A x.property⟩
    let d₀ : D := ⟨traceCentered τ (d : P), traceCentered_mem τ D d.property⟩
    let w := alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)
    have hxd : (x₀ : P) * (d₀ : P) * w ∈ span τ A D := by
      simpa only [alternatingProduct_cons, OneMemClass.coe_one, one_mul, Fin.cons_zero,
        Fin.cons_succ, w, mul_assoc] using
        word_mem τ A D (n + 2) 1 b (Fin.cons x₀ a) (Fin.cons d₀ c)
          (by intro i; refine Fin.cases ?_ (fun j => ha j) i
              exact traceCentered_trace τ hτ x)
          (by intro i; refine Fin.cases ?_ (fun j => hc j) i
              exact traceCentered_trace τ hτ d)
    have hdw : (d₀ : P) * w ∈ span τ A D := by
      simpa only [w, mul_assoc] using word_mem τ A D (n + 1) d₀ b a c ha hc
    have hxw : (x : P) * w ∈ span τ A D := by
      have h := ih (x * a 0) (c 0) b (fun i => a i.succ) (fun i => c i.succ)
        (fun i => ha i.succ) (fun i => hc i.succ)
      simpa only [w, alternatingProduct_cons, MulMemClass.coe_mul, mul_assoc] using h
    have heq : (x : P) * (d : P) * w = (x₀ : P) * (d₀ : P) * w +
        τ (x : P) • ((d₀ : P) * w) + τ (d : P) • ((x : P) * w) := by
      dsimp only [x₀, d₀]
      simp only [traceCentered, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      module
    have hres : (x : P) * (d : P) * w ∈ span τ A D := by
      rw [heq]
      exact (span τ A D).add_mem
        ((span τ A D).add_mem hxd ((span τ A D).smul_mem _ hdw))
          ((span τ A D).smul_mem _ hxw)
    simpa only [w, mul_assoc] using hres

/-- Left multiplication by either generating algebra preserves the full span. -/
theorem factor_mul (hτ : τ 1 = 1) {x y : P}
    (hx : x ∈ (A : Set P) ∪ (D : Set P)) (hy : y ∈ span τ A D) :
    x * y ∈ span τ A D := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, d, b, a, c, ha, hc, rfl⟩ := hy
    rcases hx with hx | hx
    · exact base_mul_word τ A D hτ n ⟨x, hx⟩ d b a c ha hc
    · exact other_mul_word τ A D ⟨x, hx⟩ n d b a c ha hc
  | zero => simpa only [mul_zero] using (span τ A D).zero_mem
  | add a b _ _ ha hb => simpa only [mul_add] using (span τ A D).add_mem ha hb
  | smul r a _ ha => simpa only [mul_smul_comm] using (span τ A D).smul_mem r ha

/-- The elements preserving a given word span form an ordinary subalgebra. -/
def preservingAlgebra : Subalgebra ℂ P where
  carrier := {x | ∀ y ∈ span τ A D, x * y ∈ span τ A D}
  zero_mem' := by intro y _; simpa only [zero_mul] using (span τ A D).zero_mem
  one_mem' := by intro y hy; simpa only [one_mul] using hy
  add_mem' := by
    intro a b ha hb y hy
    simpa only [add_mul] using (span τ A D).add_mem (ha y hy) (hb y hy)
  mul_mem' := by intro a b ha hb y hy; simpa only [mul_assoc] using ha _ (hb y hy)
  algebraMap_mem' r := by
    intro y hy
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using
      (span τ A D).smul_mem r hy

/-- Centered normal forms span the ordinary star algebra generated by the factors. -/
theorem generated_mem (hτ : τ 1 = 1) {x : P} (hx : x ∈ factorAlgebra A D) :
    x ∈ span τ A D := by
  have hstable : (factorAlgebra A D).toSubalgebra ≤ preservingAlgebra τ A D := by
    rw [factorAlgebra, StarAlgebra.adjoin_toSubalgebra]
    simp only [Set.union_star, StarMemClass.star_coe_eq, Set.union_self]
    exact Algebra.adjoin_le (fun a ha y hy => factor_mul τ A D hτ ha hy)
  simpa only [mul_one] using hstable hx 1 (one_mem τ A D)

end CenteredWordSpan

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarCornerLetters
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Haar powers in a tracial corner. Their adjoints give the
orthonormal first-letter sequence used in the propagation argument. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {q : P} {hq : IsStarProjection q}

/-- Integer powers are taken in the unital corner, whose identity is `q`. -/
def haarCornerPower (z : unitary (CStarCorner q hq)) (k : ℤ) : P :=
  (((z ^ k : unitary (CStarCorner q hq)) : CStarCorner q hq) : P)

@[simp] theorem haarCornerPower_zero (z : unitary (CStarCorner q hq)) :
    haarCornerPower z 0 = q := by
  simp only [haarCornerPower, zpow_zero, OneMemClass.coe_one, CStarCorner.coe_one]

@[simp] theorem haarCornerPower_mul (z : unitary (CStarCorner q hq)) (i j : ℤ) :
    haarCornerPower z i * haarCornerPower z j = haarCornerPower z (i + j) := by
  change (((z ^ i * z ^ j : unitary (CStarCorner q hq)) : CStarCorner q hq) : P) = _
  rw [← zpow_add]
  rfl

@[simp] theorem star_haarCornerPower (z : unitary (CStarCorner q hq)) (k : ℤ) :
    star (haarCornerPower z k) = haarCornerPower z (-k) := by
  change (((star (z ^ k) : unitary (CStarCorner q hq)) : CStarCorner q hq) : P) = _
  rw [Unitary.star_eq_inv, ← zpow_neg]
  rfl

@[simp] theorem mul_haarCornerPower (z : unitary (CStarCorner q hq)) (k : ℤ) :
    q * haarCornerPower z k = haarCornerPower z k :=
  ((z ^ k : unitary (CStarCorner q hq)) : CStarCorner q hq).property.1

@[simp] theorem haarCornerPower_mul_support (z : unitary (CStarCorner q hq)) (k : ℤ) :
    haarCornerPower z k * q = haarCornerPower z k :=
  ((z ^ k : unitary (CStarCorner q hq)) : CStarCorner q hq).property.2

/-- The coefficient `a⁻¹ᐟ²`, embedded in the complex scalars. -/
def haarCornerCoefficient (a : ℝ) : ℂ := ((Real.sqrt a)⁻¹ : ℝ)

@[simp] theorem star_haarCornerCoefficient (a : ℝ) :
    star (haarCornerCoefficient a) = haarCornerCoefficient a := by
  simp only [haarCornerCoefficient, Complex.star_def, Complex.conj_ofReal]

/-- Positive Haar powers, normalized in the ambient tracial Hilbert norm. -/
def haarCornerLetter (z : unitary (CStarCorner q hq)) (a : ℝ) (n : ℕ) : P :=
  haarCornerCoefficient a • haarCornerPower z ((n : ℤ) + 1)

@[simp] theorem support_mul_haarCornerLetter (z : unitary (CStarCorner q hq))
    (a : ℝ) (n : ℕ) : q * haarCornerLetter z a n = haarCornerLetter z a n := by
  simp only [haarCornerLetter, mul_smul_comm, mul_haarCornerPower]

@[simp] theorem haarCornerLetter_mul_support (z : unitary (CStarCorner q hq))
    (a : ℝ) (n : ℕ) : haarCornerLetter z a n * q = haarCornerLetter z a n := by
  simp only [haarCornerLetter, smul_mul_assoc, haarCornerPower_mul_support]

@[simp] theorem star_haarCornerLetter (z : unitary (CStarCorner q hq))
    (a : ℝ) (n : ℕ) : star (haarCornerLetter z a n) =
      haarCornerCoefficient a • haarCornerPower z (-((n : ℤ) + 1)) := by
  simp only [haarCornerLetter, star_smul, star_haarCornerCoefficient, star_haarCornerPower]

variable (τ : P →ₗ[ℂ] ℂ) (z : unitary (CStarCorner q hq)) {a : ℝ}

/-- Haar moments for the corner trace `τ(·)/a`; the zero moment is supplied
by `τ q = a` in the following lemmas. -/
def HaarCornerMoments (a : ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 → (a : ℂ)⁻¹ * τ (haarCornerPower z k) = 0

/-- Normalized Haar moments give the unnormalized ambient trace formula. -/
theorem haarCornerPower_trace (ha : 0 < a) (htrace : τ q = (a : ℂ))
    (hhaar : HaarCornerMoments τ z a) (k : ℤ) :
    τ (haarCornerPower z k) = if k = 0 then (a : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa only [haarCornerPower_zero, ↓reduceIte] using htrace
  · have h := hhaar k hk
    have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hz := (mul_eq_zero.mp h).resolve_left (inv_ne_zero hane)
    simpa only [hk, ↓reduceIte] using hz

theorem haarCornerLetter_trace_zero (ha : 0 < a) (htrace : τ q = (a : ℂ))
    (hhaar : HaarCornerMoments τ z a) (n : ℕ) : τ (haarCornerLetter z a n) = 0 := by
  have hn : (n : ℤ) + 1 ≠ 0 := by omega
  simp only [haarCornerLetter, map_smul, haarCornerPower_trace τ z ha htrace hhaar,
    hn, ↓reduceIte, smul_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ScalarFreeMonotone
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting either algebra preserves scalar freeness. -/

namespace KadisonSimilarity
variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  {τ : A →ₗ[ℂ] ℂ} {P Q P' Q' : StarSubalgebra ℂ A}

theorem AlternatingCenteredWord.mono (hP : P ≤ P') (hQ : Q ≤ Q')
    {side : Bool} {xs : List A} (h : AlternatingCenteredWord τ P Q side xs) :
    AlternatingCenteredWord τ P' Q' side xs := by
  induction h with
  | nil side => exact .nil side
  | @cons side x xs hm hz _ ih =>
    refine .cons ?_ hz ih
    cases side
    · exact hQ hm
    · exact hP hm

end KadisonSimilarity

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordRange
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base expectation on the algebra generated by the other free factor
and one centered symmetry. The only density datum is the ordinary reduced
word span; the two-dimensional expectation range is proved. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- Alternating words in centered other-factor letters and one fixed symmetry.
`true` means that the next letter comes from the other factor. -/
inductive CenteredSymmetryWord (τ : P →ₗ[ℂ] ℂ) (D : StarSubalgebra ℂ P) (s : P) :
    Bool → List P → Prop
  | nil (side : Bool) : CenteredSymmetryWord τ D s side []
  | other {d : P} {xs : List P} (hd : d ∈ D) (hzero : τ d = 0)
      (tail : CenteredSymmetryWord τ D s false xs) :
      CenteredSymmetryWord τ D s true (d :: xs)
  | symmetry {xs : List P} (tail : CenteredSymmetryWord τ D s true xs) :
      CenteredSymmetryWord τ D s false (s :: xs)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralColumns
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dihedral columns and reduced-word columns agree on the completed
tracial base space. Their normalizations are derived from the trace; equality
of the two realizations is needed only on bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

section Algebra
variable {P : Type*} [Ring P] [StarRing P]

/-- An involution, regarded as a unit with itself as inverse. -/
def symmetryUnit (s : P) (hsquare : s * s = 1) : Pˣ := ⟨s, s, hsquare, hsquare⟩

omit [StarRing P] in
@[simp] theorem symmetryUnit_coe (s : P) (hsquare : s * s = 1) :
    (symmetryUnit s hsquare : P) = s := rfl

omit [StarRing P] in
@[simp] theorem symmetryUnit_inv (s : P) (hsquare : s * s = 1) :
    (symmetryUnit s hsquare)⁻¹ = symmetryUnit s hsquare := by ext; rfl

@[simp] theorem symmetryUnit_star (s : P) (hsquare : s * s = 1) (hstar : star s = s) :
    star (symmetryUnit s hsquare) = symmetryUnit s hsquare := by
  apply Units.ext
  exact hstar

/-- The reflection associated to a projection, written without scalar
coercions so that its algebraic identities apply in any star ring. -/
def projectionReflection (p : P) : P := p + p - 1

@[simp] theorem projectionReflection_star (p : P) (hp : IsStarProjection p) :
    star (projectionReflection p) = projectionReflection p := by
  simp only [projectionReflection, star_sub, star_add, star_one, hp.isSelfAdjoint.star_eq]

@[simp] theorem projectionReflection_sq (p : P) (hp : IsStarProjection p) :
    projectionReflection p * projectionReflection p = 1 := by
  simp only [projectionReflection, sub_mul, mul_sub, add_mul, mul_add,
    one_mul, mul_one, hp.isIdempotentElem.eq]
  noncomm_ring

end Algebra

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryDilation
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered symmetry tests for contractions. The selfadjoint two-by-two
dilation has opposite diagonal entries, so its normalized trace vanishes
for every linear functional. Applying it to the selfadjoint off-diagonal
matrix of an arbitrary contraction yields a four-by-four symmetry with
the original contraction as one entry. This avoids any extra spectral
trace-equality hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder Matrix

variable {A : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

local instance instNonUnitalContinuousFunctionalCalculusRealIsSelfAdjoint_solutions : NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance instNonnegSpectrumClassReal_solutions : NonnegSpectrumClass ℝ A := CStarAlgebra.instNonnegSpectrumClass

theorem selfAdjoint_defect_nonneg (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    0 ≤ 1 - a ^ 2 := by
  have hsq : 0 ≤ a ^ 2 := by
    simpa only [ha.star_eq, pow_two] using star_mul_self_nonneg a
  rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg _ hsq,
    pow_two, ha.norm_mul_self]
  exact (sq_le_one_iff₀ (norm_nonneg a)).mpr hn

theorem selfAdjoint_defect_sqrt_commutes (a : A) :
    Commute (CFC.sqrt (1 - a ^ 2)) a := by
  have hc : Commute (1 - a ^ 2) a := by
    show (1 - a ^ 2) * a = a * (1 - a ^ 2)
    noncomm_ring
  simpa only [CFC.sqrt] using hc.cfcₙ_nnreal NNReal.sqrt

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSymmetryExtraction
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered symmetry dilation is tested on actual finite Hilbert
arrays. Its original entry is recovered by coordinate insertion and
projection, both contractive. Thus no matrix-size factor enters the
commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- An off-diagonal block of an operator on finite Hilbert arrays. -/
def matrixEntryCompression {n m : ℕ} (i : Fin m) (j : Fin n)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies K m) : H →L[ℂ] K :=
  (PiLp.proj 2 (fun _ : Fin m => K) i).comp (T.comp (copyInsert j))

@[simp] theorem matrixEntryCompression_apply {n m : ℕ} (i : Fin m) (j : Fin n)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies K m) (x : H) :
    matrixEntryCompression i j T x = T (PiLp.single 2 j x) i := rfl

@[simp] theorem matrixEntryCompression_matrixOperator {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (i j : Fin n) :
    matrixEntryCompression i j (matrixOperator X) = X i j := by
  ext x
  simp [matrixEntryCompression_apply, matrixOperator_apply, PiLp.single_apply, apply_ite]

variable [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

/-- A C-star matrix acts entrywise on actual finite Hilbert sums. -/
def representedMatrix (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) A) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  matrixOperator (fun i j => σ (X i j))

/-- Entrywise application of the original representation to ordinary matrices. -/
def entryMatrixHom (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) :
    Matrix (Fin n) (Fin n) A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) (H →L[ℂ] H) where
  toAlgHom := σ.toAlgHom.mapMatrix
  map_star' X := by
    apply Matrix.ext
    intro i j
    change σ (star (X j i)) = star (σ (X j i))
    exact map_star σ (X j i)

/-- The concrete matrix action is a unital star representation. -/
def representedMatrixHom (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A →⋆ₐ[ℂ]
      (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
  ((operatorMatrixRepresentation n).comp (entryMatrixHom σ n)).comp
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom

@[simp] theorem representedMatrixHom_apply (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) A) :
    representedMatrixHom σ n X = representedMatrix σ X := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DenseFamilyIsometry
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a map on a total family from its Gram matrix. This construction
allows the family to have linear relations. -/

noncomputable section
namespace KadisonSimilarity

variable {J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem dense_span_of_scalar_tests [CompleteSpace E] (v : J → E)
    (h : ∀ f : E →L[ℂ] ℂ, (∀ i, f (v i) = 0) → f = 0) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hf : innerSL ℂ x = 0 := h _ (fun i =>
    Submodule.inner_left_of_mem_orthogonal
      ((Submodule.span ℂ (Set.range v)).le_topologicalClosure
        (Submodule.subset_span ⟨i, rfl⟩)) hx)
  exact inner_self_eq_zero.mp (congrArg (fun f : E →L[ℂ] ℂ => f x) hf)

omit [CompleteSpace F] in
theorem inner_linearCombination_eq (v : J → E) (w : J → F)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) (x y : J →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ w x) (Finsupp.linearCombination ℂ w y) =
      inner ℂ (Finsupp.linearCombination ℂ v x) (Finsupp.linearCombination ℂ v y) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

omit [CompleteSpace F] in
theorem norm_linearCombination_eq (v : J → E) (w : J → F)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) (x : J →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ w x‖ = ‖Finsupp.linearCombination ℂ v x‖ := by
  have he := congrArg Complex.re (inner_linearCombination_eq v w h x x)
  have hn : ‖Finsupp.linearCombination ℂ w x‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ v x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact he
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w x),
    norm_nonneg (Finsupp.linearCombination ℂ v x)]

theorem denseRange_linearCombination (v : J → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  change Dense (Set.range (Finsupp.linearCombination ℂ v))
  change Dense ((Finsupp.linearCombination ℂ v).range : Set E)
  rw [Finsupp.range_linearCombination]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hv

omit [CompleteSpace F] in
theorem continuousLinearMap_eq_zero_of_total (v : J → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (f : E →L[ℂ] F) (hf : ∀ i, f (v i) = 0) : f = 0 := by
  have hs : Submodule.span ℂ (Set.range v) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hf i
  have hc := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hs f.isClosed_ker
  rw [hv] at hc
  ext x
  exact hc (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ClosedFamilySpan
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual closed spans and elementary tensors of total families. -/

noncomputable section
namespace KadisonSimilarity

variable {I J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def closedFamilySpan (v : I → E) : ClosedSubmodule ℂ E :=
  (Submodule.span ℂ (Set.range v)).closure

def closedFamilyVector (v : I → E) (i : I) : closedFamilySpan v :=
  ⟨v i, (Submodule.span ℂ (Set.range v)).le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)⟩

omit [CompleteSpace E] in
@[simp] theorem closedFamilyVector_coe (v : I → E) (i : I) :
    (closedFamilyVector v i : E) = v i := rfl

omit [CompleteSpace E] in
theorem closedFamilySpan_le (v : I → E) (S : ClosedSubmodule ℂ E)
    (h : ∀ i, v i ∈ S) : (closedFamilySpan v).toSubmodule ≤ S.toSubmodule := by
  apply (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) S.isClosed
  rintro _ ⟨i, rfl⟩
  exact h i

theorem closedFamilyVector_total (v : I → E) :
    (Submodule.span ℂ (Set.range (closedFamilyVector v))).topologicalClosure = ⊤ := by
  apply dense_span_of_scalar_tests
  intro f hf
  let g := f.comp (closedFamilySpan v).toSubmodule.orthogonalProjectionOnto
  have hs : Submodule.span ℂ (Set.range v) ≤ g.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f ((closedFamilySpan v).toSubmodule.orthogonalProjectionOnto
      (closedFamilyVector v i : E)) = 0
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact hf i
  have hc := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hs g.isClosed_ker
  ext x
  change f x = 0
  have hx := hc x.property
  change f ((closedFamilySpan v).toSubmodule.orthogonalProjectionOnto (x : E)) = 0 at hx
  simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hx

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.NuclearUltrapower_HilbertUltraproduct
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower

/-- Bounded scalar families have a genuine ultralimit. No countable completeness
or separability hypothesis is used. -/
theorem hilbert_tendsto_ultralimit_of_bounded {ι : Type u} (ω : Ultrafilter ι)
    {F : Type v} [NormedAddCommGroup F] [ProperSpace F] (f : ι → F)
    (hf : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) :
    Tendsto f (ω : Filter ι) (𝓝 (limUnder (ω : Filter ι) f)) := by
  obtain ⟨C, hC⟩ := hf
  apply tendsto_nhds_limUnder
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : F) C).ultrafilter_le_nhds'
    (Ultrafilter.map f ω) (by
      change {i | f i ∈ Metric.closedBall 0 C} ∈ (ω : Filter ι)
      exact Filter.Eventually.of_forall (fun i => by simpa using hC i))
  exact ⟨x, hx⟩

/-- A type synonym for bounded Hilbert families, equipped below with the
ultralimit semi-inner-product (not with the supremum norm). -/
def UltraPreHilbert {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] (_ω : Ultrafilter ι) := lp E ∞

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι)

instance instAddCommGroupSubtypePreLpMemAddSubgroup : AddCommGroup (UltraPreHilbert E ω) := inferInstanceAs (AddCommGroup (lp E ∞))
instance instModuleComplexSubtypePreLpMemAddSubgroup : Module ℂ (UltraPreHilbert E ω) := inferInstanceAs (Module ℂ (lp E ∞))

def family (x : UltraPreHilbert E ω) : lp E ∞ := x

omit [∀ i, InnerProductSpace ℂ (E i)] in
@[simp] theorem family_add (x y : UltraPreHilbert E ω) :
    family ω (x + y) = family ω x + family ω y := rfl
@[simp] theorem family_smul (r : ℂ) (x : UltraPreHilbert E ω) :
    family ω (r • x) = r • family ω x := rfl

theorem inner_tendsto (x y : UltraPreHilbert E ω) :
    Tendsto (fun i => inner ℂ (family ω x i) (family ω y i)) (ω : Filter ι)
      (𝓝 (limUnder (ω : Filter ι) (fun i => inner ℂ (family ω x i) (family ω y i)))) := by
  apply hilbert_tendsto_ultralimit_of_bounded
  refine ⟨‖family ω x‖ * ‖family ω y‖, fun i => ?_⟩
  exact (norm_inner_le_norm _ _).trans (mul_le_mul
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) (norm_nonneg _) (norm_nonneg _))

@[instance_reducible] def core : PreInnerProductSpace.Core ℂ (UltraPreHilbert E ω) where
  inner x y := limUnder (ω : Filter ι) (fun i => inner ℂ (family ω x i) (family ω y i))
  conj_inner_symm x y := by
    exact tendsto_nhds_unique ((inner_tendsto ω y x).star.congr
      (fun i => inner_conj_symm (family ω x i) (family ω y i))) (inner_tendsto ω x y)
  re_inner_nonneg x := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((Complex.continuous_re.tendsto _).comp (inner_tendsto ω x x))
      (Filter.Eventually.of_forall (fun i => (inner_self_nonneg (𝕜 := ℂ) (x := family ω x i))))
  add_left x y z := by
    apply tendsto_nhds_unique (inner_tendsto ω (x + y) z)
    simpa only [family_add, lp.coeFn_add, Pi.add_apply, inner_add_left] using
      (inner_tendsto ω x z).add (inner_tendsto ω y z)
  smul_left x y r := by
    apply tendsto_nhds_unique (inner_tendsto ω (r • x) y)
    simpa only [family_smul, lp.coeFn_smul, Pi.smul_apply, inner_smul_left] using
      (inner_tendsto ω x y).const_mul (starRingEnd ℂ r)

instance instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup : SeminormedAddCommGroup (UltraPreHilbert E ω) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ (core ω)

instance instInnerProductSpaceComplexSubtypePreLpMemAddSubgroup : InnerProductSpace ℂ (UltraPreHilbert E ω) := InnerProductSpace.ofCore (core ω)

@[simp] theorem inner_def (x y : UltraPreHilbert E ω) :
    inner ℂ x y = limUnder (ω : Filter ι)
      (fun i => inner ℂ (family ω x i) (family ω y i)) := rfl

/-- The seminorm is exactly the ultralimit of pointwise norms. -/
theorem norm_tendsto (x : UltraPreHilbert E ω) :
    Tendsto (fun i => ‖family ω x i‖) (ω : Filter ι) (𝓝 ‖x‖) := by
  have h := ((Complex.continuous_re.tendsto _).comp (inner_tendsto ω x x)).sqrt
  convert h using 1
  · funext i
    exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _
  · exact congrArg (fun t => 𝓝 t) (by rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) x]; rfl)

end UltraPreHilbert

/-- The Hilbert ultraproduct, implemented as the Hausdorff completion of bounded
families for the ultralimit seminorm. This is equivalent to the standard
norm-null quotient, but gives completeness without a separate lifting argument. -/
abbrev HilbertUltraproduct {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι) :=
  UniformSpace.Completion (UltraPreHilbert E ω)

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

/-- Uniformly bounded operator families act on bounded vector families. -/
def mapLinear (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    UltraPreHilbert E ω →ₗ[ℂ] UltraPreHilbert F ω where
  toFun x := (⟨fun i => T i (family ω x i), memℓp_infty
    ⟨‖T‖ * ‖family ω x‖, by
      rintro _ ⟨i, rfl⟩
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
        (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) (norm_nonneg _) (norm_nonneg _))⟩⟩ : lp F ∞)
  map_add' x y := by apply Subtype.ext; funext i; exact map_add (T i) _ _
  map_smul' c x := by apply Subtype.ext; funext i; exact map_smul (T i) _ _

@[simp] theorem family_map (T : lp (fun i => E i →L[ℂ] F i) ∞)
    (x : UltraPreHilbert E ω) (i : ι) :
    family ω (mapLinear ω T x) i = T i (family ω x i) := rfl

/-- Eventual, rather than uniform, bounds suffice after passing to the ultralimit. -/
theorem mapLinear_norm_le (T : lp (fun i => E i →L[ℂ] F i) ∞) (C : ℝ)
    (hT : ∀ᶠ i in (ω : Filter ι), ‖T i‖ ≤ C) (x : UltraPreHilbert E ω) :
    ‖mapLinear ω T x‖ ≤ C * ‖x‖ := by
  apply le_of_tendsto_of_tendsto (norm_tendsto ω (mapLinear ω T x))
    ((norm_tendsto ω x).const_mul C)
  exact hT.mono (fun i hi => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))

def mapContinuous (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    UltraPreHilbert E ω →L[ℂ] UltraPreHilbert F ω :=
  (mapLinear ω T).mkContinuous ‖T‖ (mapLinear_norm_le ω T ‖T‖
    (Filter.Eventually.of_forall (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero T i)))

end UltraPreHilbert

namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

/-- The induced operator on the completed Hilbert ultraproduct. -/
def map (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct F ω :=
  (UltraPreHilbert.mapContinuous ω T).completion

@[simp] theorem map_coe (T : lp (fun i => E i →L[ℂ] F i) ∞)
    (x : UltraPreHilbert E ω) :
    map ω T (x : HilbertUltraproduct E ω) =
    (UltraPreHilbert.mapLinear ω T x : HilbertUltraproduct F ω) :=
  ContinuousLinearMap.completion_apply_coe _ _

end HilbertUltraproduct

end NuclearUltrapower

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (ω : Ultrafilter ι)

local instance instIsBoundedSMulComplexContinuousLinearMapId (i : ι) : IsBoundedSMul ℂ (E i →L[ℂ] E i) :=
  NormedSpace.toIsBoundedSMul

omit [∀ i, CompleteSpace (E i)] in
theorem map_zero  : map (E := E) (F := E) ω (0 : lp (fun i => E i →L[ℂ] E i) ∞) = 0 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [map_coe]
    have he : UltraPreHilbert.mapLinear (E := E) (F := E) ω 0 x = 0 := by
      apply Subtype.ext; funext i
      change (0 : E i →L[ℂ] E i) (UltraPreHilbert.family ω x i) = 0
      rfl
    rw [he, UniformSpace.Completion.coe_zero]
    rfl

omit [∀ i, CompleteSpace (E i)] in
theorem map_add (T U : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (T + U) = map (E := E) (F := E) ω T + map (E := E) (F := E) ω U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simp only [add_apply, map_coe, ← UniformSpace.Completion.coe_add]
    congr 1

theorem map_smul (c : ℂ) (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    map (E := E) (F := E) ω (SMul.smul c T) = c • map (E := E) (F := E) ω T := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (map (E := E) (F := E) ω (SMul.smul c T)).continuous
      (c • map (E := E) (F := E) ω T).continuous
  | ih x =>
    have he : UltraPreHilbert.mapLinear (E := E) (F := E) ω (SMul.smul c T) x =
        c • UltraPreHilbert.mapLinear (E := E) (F := E) ω T x := by
      apply Subtype.ext
      funext i
      rfl
    rw [map_coe, smul_apply, map_coe,
      ← UniformSpace.Completion.coe_smul, he]

theorem map_mul (T U : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (T * U) = map (E := E) (F := E) ω T * map (E := E) (F := E) ω U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    change map ω (T * U) (x : HilbertUltraproduct E ω) = map ω T (map ω U x)
    rw [map_coe, map_coe, map_coe]
    congr 1

theorem map_star (T : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (star T) = star (map (E := E) (F := E) ω T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [map_coe, UniformSpace.Completion.inner_coe, UltraPreHilbert.inner_def]
    congr 1
    funext i
    simp only [UltraPreHilbert.family_map, lp.coeFn_star, Pi.star_apply]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Bounded operator products and adjoints descend to the Hilbert ultraproduct. -/
def operatorRep : lp (fun i => E i →L[ℂ] E i) ∞ →⋆ₙₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  toFun := map (E := E) (F := E) ω
  map_zero' := map_zero ω
  map_add' := map_add ω
  map_smul' := map_smul ω
  map_mul' := map_mul ω
  map_star' := map_star ω

@[simp] theorem operatorRep_apply (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    operatorRep ω T = map (E := E) (F := E) ω T := rfl

end HilbertUltraproduct
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_DominatedFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated factorization for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace HochschildDomination
universe u v
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

@[nolint unusedArguments]
def PreHilbert (_φ _ψ : M →ₚ[ℂ] ℂ) := M

namespace PreHilbert
variable (φ ψ : M →ₚ[ℂ] ℂ)
instance instAddCommGroup : AddCommGroup (PreHilbert φ ψ) := inferInstanceAs (AddCommGroup M)
instance instModuleComplex : Module ℂ (PreHilbert φ ψ) := inferInstanceAs (Module ℂ M)

end PreHilbert

end HochschildDomination

open scoped InnerProductSpace ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_HilbertFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert factorization for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable (M : Type u) [CStarAlgebra M]

structure SharedHilbertFactor (B : M →L[ℂ] StrongDual ℂ M) where
  H : Type u
  group : NormedAddCommGroup H
  inner : InnerProductSpace ℂ H
  complete : CompleteSpace H
  left : H →L[ℂ] StrongDual ℂ M
  right : M →L[ℂ] H
  pairing : ∀ a b,B a b=left (right b) a

attribute [instance] SharedHilbertFactor.group SharedHilbertFactor.inner SharedHilbertFactor.complete

end HochschildNormalPart

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tracial matrix towers from actual embedded matrix algebras

The matrix-stage geometry is constructed from nested trace-preserving matrix
embeddings in a tracial Hilbert representation. Density of centered trace-zero
stages is derived by orthogonal projection from density of the full stages.
-/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Raw nested matrix embeddings, with density stated for their represented
algebra vectors. No Hilbert coefficient identity is part of this data. -/
structure NestedTracialMatrices (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) where
  embedding : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] R
  trace_embedding : ∀ s a, τ (embedding s a) =
    (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace a
  inclusion : ∀ s t, s ≤ t → Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] Matrix (A t) (A t) ℂ
  compatible : ∀ s t h a, embedding t (inclusion s t h a) = embedding s a
  dense : Dense (⋃ s, Set.range (fun a => V (embedding s a)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GNSTracialGeometry
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial GNS representation supplies the Hilbert geometry
used in the free-corner argument. Trace-preserving homomorphisms induce
isometric embeddings which intertwine the concrete left actions. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The canonical algebra vector in the completed GNS space. -/
def gnsTracialVector (τ : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] τ.GNS :=
  UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp τ.toPreGNS.toLinearMap

@[simp] theorem gnsTracialVector_apply (τ : A →ₚ[ℂ] ℂ) (a : A) :
    gnsTracialVector τ a = (τ.toPreGNS a : τ.GNS) := rfl

theorem gnsTracialVector_inner (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    inner ℂ (gnsTracialVector τ a) (gnsTracialVector τ b) = τ (star a * b) := by
  simp only [gnsTracialVector_apply, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS]

theorem gnsTracialVector_dense (τ : A →ₚ[ℂ] ℂ) : DenseRange (gnsTracialVector τ) :=
  UniformSpace.Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe τ.PreGNS)

@[simp] theorem gnsTracialVector_left (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    τ.gnsStarAlgHom a (gnsTracialVector τ b) = gnsTracialVector τ (a * b) := by
  change τ.gnsNonUnitalStarAlgHom a (τ.toPreGNS b : τ.GNS) =
    (τ.toPreGNS (a * b) : τ.GNS)
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerConstants
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant Hilbert vectors retain both their norm and the action of every
constant bounded operator inside the actual Hilbert ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower
open scoped ENNReal Topology

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A constant bounded family, with the ordinary supremum-norm domain. -/
def boundedConstant {E : Type*} [NormedAddCommGroup E] (x : E) : lp (fun _ : ι => E) ∞ :=
  ⟨fun _ => x, memℓp_infty ⟨‖x‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩⟩

@[simp] theorem boundedConstant_apply {E : Type*} [NormedAddCommGroup E] (x : E) (i : ι) :
    boundedConstant (ι := ι) x i = x := rfl

/-- The ultralimit seminorm of a constant family is its original norm. -/
def constantPreHilbert (ω : Ultrafilter ι) : H →ₗᵢ[ℂ] UltraPreHilbert (fun _ : ι => H) ω where
  toFun := fun x => boundedConstant x
  map_add' x y := by apply Subtype.ext; funext i; rfl
  map_smul' c x := by apply Subtype.ext; funext i; rfl
  norm_map' x := by
    exact tendsto_nhds_unique (UltraPreHilbert.norm_tendsto ω (boundedConstant x))
      tendsto_const_nhds

/-- The isometric constant-vector inclusion in the completed Hilbert ultrapower. -/
def constantHilbertInclusion (ω : Ultrafilter ι) :
    H →ₗᵢ[ℂ] HilbertUltraproduct (fun _ : ι => H) ω :=
  UniformSpace.Completion.toComplₗᵢ.comp (constantPreHilbert ω)

omit [CompleteSpace H] in
@[simp] theorem constantHilbertInclusion_apply (ω : Ultrafilter ι) (x : H) :
    constantHilbertInclusion ω x =
      ((constantPreHilbert ω x : UltraPreHilbert (fun _ : ι => H) ω) :
        HilbertUltraproduct (fun _ : ι => H) ω) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSubalgebraModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal algebra generated inside the ultrapower is represented on
its own tracial GNS space. Restriction of the positive trace and its exact
Hilbert-space identification require no further analytic input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- Restrict the actual positive functional to a closed star subalgebra. -/
def restrictedPositiveTrace : L →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp L.subtype.toLinearMap)
    (fun _a ha => τ.map_nonneg ha)

@[simp] theorem restrictedPositiveTrace_apply (a : L) :
    restrictedPositiveTrace τ L a = τ (a : P) := rfl

theorem restrictedPositiveTrace_tracial
    (htr : ∀ a b : P, τ (a * b) = τ (b * a)) (a b : L) :
    restrictedPositiveTrace τ L (a * b) = restrictedPositiveTrace τ L (b * a) :=
  htr a b

theorem restrictedPositiveTrace_faithful
    (hf : ∀ a : P, τ (star a * a) = 0 → a = 0)
    (a : L) (ha : restrictedPositiveTrace τ L (star a * a) = 0) : a = 0 := by
  apply Subtype.ext
  exact hf a ha

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GeneratedEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual copies of the two factors inside their generated algebra.
The range identifications align the GNS recovery operator with the factor
generation, freeness, and matrix tower used by the local theorem. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

omit [PartialOrder P] [StarOrderedRing P] in
theorem range_codRestrict_eq_comap (φ : A →⋆ₐ[ℂ] P) (hφ : ∀ a, φ a ∈ L) :
    (φ.codRestrict L hφ).range = φ.range.comap L.subtype := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

omit [PartialOrder P] [StarOrderedRing P] in
theorem codRestrict_range_isClosed (φ : A →⋆ₐ[ℂ] P) (hφ : ∀ a, φ a ∈ L)
    (hclosed : IsClosed (φ.range : Set P)) :
    IsClosed ((φ.codRestrict L hφ).range : Set L) := by
  rw [range_codRestrict_eq_comap]
  exact hclosed.preimage continuous_subtype_val

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero padding of Hilbert arrays

The coordinate inclusion along an arbitrary finite injection is isometric.
Extension of an operator by zero consequently preserves scalar commutator
norms and the norms of their matrix amplifications. No dimension factor occurs.
-/

noncomputable section
namespace KadisonSimilarity

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

/-- The actual zero extension along an injection of finite coordinate sets. -/
def copyEmbeddingMap (e : Fin r ↪ Fin m) :
    HilbertCopies H r →L[ℂ] HilbertCopies H m :=
  ∑ i : Fin r, (copyInsert (e i)).comp (PiLp.proj 2 (fun _ : Fin r => H) i)

end Coordinates

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixConjugateAutomorphism
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix conjugation as an actual star-algebra automorphism of the factor. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry

variable {P : Type*} [CStarAlgebra P] (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

def matrixConjugationAut : D ≃⋆ₐ[ℂ] D :=
  Unitary.conjStarAlgAut ℂ D ⟨ι (u : Matrix α α ℂ), Unitary.map_mem ι u.property⟩

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTracialGNS
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized matrix traces and their actual GNS Hilbert spaces. The GNS
space of `M_n(A)` is identified with the square array of copies of the GNS
space of `A`; its algebra vectors have entries `n^(-1/2) V(a_ij)`. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

/-- Coordinatewise dense maps stay dense in a finite Hilbert sum. -/
theorem denseRange_hilbert_entries {J D B : Type*} [Fintype J]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (f : D → B) (hf : DenseRange f) :
    DenseRange (fun x : J → D => WithLp.toLp 2 (fun j => f (x j))) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : J => B)).symm
  have hpi : DenseRange (Pi.map (fun _ : J => f)) := DenseRange.piMap (fun _ => hf)
  exact e.surjective.denseRange.comp hpi e.continuous

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

local instance instNonUnitalContinuousFunctionalCalculusRealCStarMatrixFinIsSelfAdjoint_solutions : NonUnitalContinuousFunctionalCalculus ℝ
    (CStarMatrix (Fin n) (Fin n) A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance instNonnegSpectrumClassRealCStarMatrixFin_solutions : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The normalized sum of the diagonal functionals. -/
def normalizedMatrixTraceLinear (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] ℂ where
  toFun X := (∑ i : Fin n, τ (X i i)) / (n : ℂ)
  map_add' X Y := by
    simp only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib, add_div]
  map_smul' c X := by
    simp only [CStarMatrix.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul,
      ← Finset.mul_sum]
    ring

omit [NeZero n] in
/-- Positivity of a matrix gives positivity of each diagonal entry. -/
theorem matrix_diagonal_nonneg (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ X) (i : Fin n) : 0 ≤ X i i := by
  have hs := CFC.sqrt_nonneg X
  have he : X = star (CFC.sqrt X) * CFC.sqrt X := by
    rw [hs.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self X hX]
  rw [he, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _

/-- The normalized matrix trace as a positive linear functional. -/
def normalizedMatrixTrace (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (normalizedMatrixTraceLinear τ n) (fun X hX =>
    div_nonneg (Finset.sum_nonneg fun i _ => τ.map_nonneg (matrix_diagonal_nonneg X hX i))
      (by positivity))

@[simp] theorem normalizedMatrixTrace_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τ n X = (∑ i : Fin n, τ (X i i)) / (n : ℂ) := rfl

/-- Entrywise formula for the matrix GNS inner product. -/
theorem normalizedMatrixTrace_star_mul (τ : A →ₚ[ℂ] ℂ)
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τ n (star X * Y) =
      (n : ℂ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n, τ (star (X i j) * Y i j) := by
  simp only [normalizedMatrixTrace_apply, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, map_sum]
  rw [Finset.sum_comm]
  ring

/-- Normalization converting the array norm into normalized tracial L² norm. -/
def matrixGNSScale (n : ℕ) : ℝ := (Real.sqrt n)⁻¹

theorem matrixGNSScale_pos : 0 < matrixGNSScale n := by
  unfold matrixGNSScale
  exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)))

omit [NeZero n] in
theorem matrixGNSScale_sq : matrixGNSScale n ^ 2 = (n : ℝ)⁻¹ := by
  rw [matrixGNSScale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixUnitFamilies
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partial-isometry frames constructed from an actual unital matrix
star homomorphism. No frame-existence assumption is used. -/

noncomputable section
namespace KadisonSimilarity

variable {P α : Type*} [CStarAlgebra P] [Fintype α] [DecidableEq α]

/-- The image of an ordinary matrix unit in the ambient C-star algebra. -/
def embeddedMatrixUnit (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i j : α) : P :=
  ι (Matrix.single i j 1)

@[simp] theorem embeddedMatrixUnit_star (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i j : α) :
    star (embeddedMatrixUnit ι i j) = embeddedMatrixUnit ι j i := by
  unfold embeddedMatrixUnit
  rw [← map_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

theorem embeddedMatrixUnit_mul (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i j k l : α) :
    embeddedMatrixUnit ι i j * embeddedMatrixUnit ι k l =
      if j = k then embeddedMatrixUnit ι i l else 0 := by
  unfold embeddedMatrixUnit
  rw [← map_mul]
  by_cases h : j = k
  · subst k
    simp
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) i j k h (1 : ℂ)]
    simp only [map_zero, h, ↓reduceIte]

/-- Diagonal matrix units are actual star projections. -/
theorem embeddedMatrixUnit_isStarProjection (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i : α) :
    IsStarProjection (embeddedMatrixUnit ι i i) := by
  refine ⟨?_, ?_⟩
  · change embeddedMatrixUnit ι i i * embeddedMatrixUnit ι i i = _
    simp [embeddedMatrixUnit_mul]
  · exact embeddedMatrixUnit_star ι i i

/-- The diagonal images resolve the unit because the embedding is unital. -/
theorem sum_embeddedMatrixUnit_diagonal (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) :
    ∑ i : α, embeddedMatrixUnit ι i i = 1 := by
  unfold embeddedMatrixUnit
  rw [← map_sum, Matrix.sum_single_one, map_one]

/-- The precise finite-frame data consumed by full-column coordinates. -/
structure MatrixUnitColumnFamily (P α : Type*) [CStarAlgebra P]
    [Fintype α] [DecidableEq α] where
  corner : P
  corner_projection : IsStarProjection corner
  column : α → P
  initial : ∀ i j, star (column i) * column j = if i = j then corner else 0
  resolution : ∑ i, column i * star (column i) = 1
  base : α
  base_column : column base = corner

/-- Taking a single column of embedded matrix units supplies the full frame. -/
def matrixUnitColumnFamilyOfEmbedding (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i₀ : α) :
    MatrixUnitColumnFamily P α where
  corner := embeddedMatrixUnit ι i₀ i₀
  corner_projection := embeddedMatrixUnit_isStarProjection ι i₀
  column i := embeddedMatrixUnit ι i i₀
  initial i j := by
    rw [embeddedMatrixUnit_star, embeddedMatrixUnit_mul]
  resolution := by
    simp only [embeddedMatrixUnit_star, embeddedMatrixUnit_mul, ↓reduceIte]
    exact sum_embeddedMatrixUnit_diagonal ι
  base := i₀
  base_column := rfl

@[simp] theorem matrixUnitColumnFamilyOfEmbedding_corner
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i₀ : α) :
    (matrixUnitColumnFamilyOfEmbedding ι i₀).corner = ι (Matrix.single i₀ i₀ 1) := rfl

@[simp] theorem matrixUnitColumnFamilyOfEmbedding_column
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i₀ i : α) :
    (matrixUnitColumnFamilyOfEmbedding ι i₀).column i = ι (Matrix.single i i₀ 1) := rfl

/-- Normalized trace preservation gives the reciprocal-dimension trace of
all the diagonal projections, and hence of the chosen initial corner. -/
theorem trace_embeddedMatrixUnit_diagonal
    (τ : P →ₗ[ℂ] ℂ) (ι : Matrix α α ℂ →⋆ₐ[ℂ] P)
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) (i : α) :
    τ (embeddedMatrixUnit ι i i) = 1 / (Fintype.card α : ℂ) := by
  rw [embeddedMatrixUnit, htrace, Matrix.trace_single_eq_same, mul_one, one_div]

/-- The frame together with the corner trace used in small-corner estimates. -/
structure TracialMatrixUnitColumnFamily (τ : P →ₗ[ℂ] ℂ) (α : Type*)
    [Fintype α] [DecidableEq α] extends MatrixUnitColumnFamily P α where
  trace_corner : τ corner = 1 / (Fintype.card α : ℂ)

/-- A trace-preserving unital matrix embedding supplies both frame and trace. -/
def tracialMatrixUnitColumnFamilyOfEmbedding
    (τ : P →ₗ[ℂ] ℂ) (ι : Matrix α α ℂ →⋆ₐ[ℂ] P)
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) (i₀ : α) :
    TracialMatrixUnitColumnFamily τ α where
  toMatrixUnitColumnFamily := matrixUnitColumnFamilyOfEmbedding ι i₀
  trace_corner := trace_embeddedMatrixUnit_diagonal τ ι htrace i₀

namespace MatrixUnitColumnFamily

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Relabeling a finite frame preserves its initial projection and resolution. -/
def reindex (F : MatrixUnitColumnFamily P α) (e : β ≃ α) : MatrixUnitColumnFamily P β where
  corner := F.corner
  corner_projection := F.corner_projection
  column i := F.column (e i)
  initial i j := by simpa using F.initial (e i) (e j)
  resolution := (e.sum_comp (fun i => F.column i * star (F.column i))).trans F.resolution
  base := e.symm F.base
  base_column := by simpa only [e.apply_symm_apply] using F.base_column

@[simp] theorem reindex_corner (F : MatrixUnitColumnFamily P α) (e : β ≃ α) :
    (F.reindex e).corner = F.corner := rfl

@[simp] theorem reindex_column (F : MatrixUnitColumnFamily P α) (e : β ≃ α) (i : β) :
    (F.reindex e).column i = F.column (e i) := rfl

end MatrixUnitColumnFamily

namespace TracialMatrixUnitColumnFamily

variable {τ : P →ₗ[ℂ] ℂ} {β : Type*} [Fintype β] [DecidableEq β]

/-- The normalized corner trace is preserved when a finite frame is relabeled. -/
def reindex (F : TracialMatrixUnitColumnFamily τ α) (e : β ≃ α) :
    TracialMatrixUnitColumnFamily τ β where
  toMatrixUnitColumnFamily := F.toMatrixUnitColumnFamily.reindex e
  trace_corner := by
    change τ F.corner = 1 / (Fintype.card β : ℂ)
    rw [Fintype.card_congr e]
    exact F.trace_corner

end TracialMatrixUnitColumnFamily

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHalfProjectionData
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered reflection used by the dihedral test is constructed from a
half-trace projection. Completing a smaller projection by an orthogonal
projection of the complementary trace supplies that projection; no centered
symmetry is assumed in this algebraic step. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

@[simp] theorem star_projectionReflection {p : P} (hp : IsStarProjection p) :
    star (projectionReflection p) = projectionReflection p :=
  projectionReflection_star p hp

@[simp] theorem projectionReflection_mul_self {p : P} (hp : IsStarProjection p) :
    projectionReflection p * projectionReflection p = 1 :=
  projectionReflection_sq p hp

/-- Taking the half projection of the constructed reflection recovers the
original projection exactly. -/
@[simp] theorem dihedralHalfProjection_projectionReflection {p : P}
    (hp : IsStarProjection p) :
    dihedralHalfProjection (symmetryUnit (projectionReflection p)
      (projectionReflection_mul_self hp)) = p := by
  change (1 / 2 : ℂ) • (1 + (p + p - 1)) = p
  module

/-- Minimal half-projection data, before constructing the reflection. The
existence of this data is supplied by projection completion in the intended
finite factor; the next constructor derives it from an actual complement. -/
structure HalfTraceProjectionData (τ : P →ₗ[ℂ] ℂ) (e : P) where
  projection : P
  isProjection : IsStarProjection projection
  trace_half : τ projection = (1 / 2 : ℂ)
  left_support : projection * e = e
  right_support : e * projection = e

namespace HalfTraceProjectionData

variable {τ : P →ₗ[ℂ] ℂ} {e : P} (Q : HalfTraceProjectionData τ e)

/-- The actual centered reflection obtained from the completed projection. -/
def reflection : P := projectionReflection Q.projection

@[simp] theorem reflection_star : star Q.reflection = Q.reflection :=
  star_projectionReflection Q.isProjection

@[simp] theorem reflection_square : Q.reflection * Q.reflection = 1 :=
  projectionReflection_mul_self Q.isProjection

end HalfTraceProjectionData
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerTransport
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner unitaries and completed half projections are transported along
the actual trace-preserving factor embedding. This retains their concrete
support projections inside the conjugated free copy. -/

noncomputable section
namespace KadisonSimilarity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B)

/-- A unital star homomorphism restricts to a unital homomorphism between
the actual corners of corresponding projections. -/
def cornerStarAlgHom (e : A) (he : IsStarProjection e) :
    CStarCorner e he →⋆ₐ[ℂ] CStarCorner (φ e) (he.map φ) where
  toFun x := ⟨φ (x : A), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (by simp only [CStarCorner.coe_one])
  map_add' x y := Subtype.ext (map_add φ (x : A) (y : A))
  map_mul' x y := Subtype.ext (map_mul φ (x : A) (y : A))
  commutes' c := Subtype.ext (by
    change φ ((algebraMap ℂ (CStarCorner e he) c : CStarCorner e he) : A) =
      ((algebraMap ℂ (CStarCorner (φ e) (he.map φ)) c :
        CStarCorner (φ e) (he.map φ)) : B)
    simp only [Algebra.algebraMap_eq_smul_one]
    change φ (c • ((1 : CStarCorner e he) : A)) =
      c • ((1 : CStarCorner (φ e) (he.map φ)) : B)
    rw [CStarCorner.coe_one, CStarCorner.coe_one, map_smul])
  map_star' x := Subtype.ext (map_star φ (x : A))

@[simp] theorem cornerStarAlgHom_coe (e : A) (he : IsStarProjection e)
    (x : CStarCorner e he) : (cornerStarAlgHom φ e he x : B) = φ (x : A) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInputTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of the discharged tracial inputs

These are coordinate changes through actual star algebra equivalences.
The concrete normal representation is retained as algebraic data; neither
rounding nor existence of a right support is assumed in the concrete model.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

section Concrete
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

/-- A faithful normal realization with precisely this represented range
supplies the star equivalence; no tracial input is needed for this step. -/
def equivalenceOfConcreteRange (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hinj : Function.Injective ρ) (hrange : ρ.range = P.toStarSubalgebra) :
    A ≃⋆ₐ[ℂ] P.toStarSubalgebra :=
  StarAlgEquiv.ofBijective (ρ.codRestrict P.toStarSubalgebra (fun a => by
    rw [← hrange]
    exact ⟨a, rfl⟩))
    ⟨(StarAlgHom.injective_codRestrict _ _ _).mpr hinj, by
      intro b
      have hb : (b : H →L[ℂ] H) ∈ ρ.range := by
        rw [hrange]
        exact b.property
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-preserving homomorphisms induce homomorphisms of the actual
tracial quotients. In particular this realizes Q^ω inside P^ω. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower TracialUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Apply a star homomorphism at every coordinate of a bounded sequence. -/
def boundedSequenceStarHom (φ : A →⋆ₐ[ℂ] B) : (ℕ →ᵇ A) →⋆ₐ[ℂ] (ℕ →ᵇ B) where
  toFun x := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => φ (x i))
    ‖x‖ (fun i => (NonUnitalStarAlgHom.norm_apply_le φ (x i)).trans (x.norm_coe_le_norm i))
  map_one' := by ext i; exact map_one φ
  map_mul' x y := by ext i; exact map_mul φ (x i) (y i)
  map_zero' := by ext i; exact map_zero φ
  map_add' x y := by ext i; exact map_add φ (x i) (y i)
  commutes' c := by ext i; exact φ.commutes c
  map_star' x := by ext i; exact map_star φ (x i)

@[simp] theorem boundedSequenceStarHom_apply (φ : A →⋆ₐ[ℂ] B) (x : ℕ →ᵇ A) (i : ℕ) :
    boundedSequenceStarHom φ x i = φ (x i) := rfl

end KadisonSimilarity

end

end OAI
end


