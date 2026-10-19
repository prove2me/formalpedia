-- Prove2me | Definitions.Def_OAIE3v2B105
-- name    : OAIE3v2B105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:30:30.249161+00:00
-- url     : https://prove2.me/theorems/59d5d2ea-44d4-40e5-9d3c-7b972cb7ca84
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 107 of 311
-- statement:
--   Definitions bundle 107 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B093` of this split.
--
--   Modules: `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedOriginalSampleQuadratureUniformBounds.lean`, `Estimates/AllocatedPartitionedProfileJet.lean`, `Estimates/AllocatedRelativeChildSliceGeometry.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/NormalizedCoefficientRemainder.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/RealifiedTripleLayers.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/WeightedOrbitNormalization.lean`, `Geometry/MultidegreeCoordinateSplit.lean`, `Geometry/RealSquarefreeCoordinates.lean`, `Lattices/CoefficientIntegerFloorRemainder.lean`, `Lattices/LatticeOrderedGenerators.lean`, `Linear/AllocatedFixedKernelCover.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/CentralBasisPowerCover.lean`, `Nilpotent/BlockLayerBracket.lean`, `Nilpotent/SquarefreeBracketCoefficients.lean`, `Polynomial/AdditiveTriplePolynomialRestriction.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/MultiaffineTriplePolynomial.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/RealBlockPolynomialEval.lean`, `Polynomial/SquarefreeTopDegree.lean`, `Polynomial/WeightedLieDegreeLengthSpan.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Probability/AllocatedSlicedIdealDensity.lean`, `Sampling/AllocatedActiveGridPlateau.lean`, `Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`, `Sampling/RationalForecastGridTail.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B093

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem eval_weightedDilation (w : σ → ℕ) (r : R) (x : σ → R)
    (p : VectorPolynomial σ R V) :
    eval x (weightedDilation w r p) = eval (fun i => r ^ w i * x i) p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedDilation_monomial, map_smul, eval_monomial,
    weighted_monomial_dilation, smul_smul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketCoefficients
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMonomial_lie_coefficient (a b c : SquarefreeIndex ι) (x y : L) :
    squarefreePolynomialEquiv (⁅squarefreeMonomial a x, squarefreeMonomial b y⁆) c =
      if a.val + b.val = c.val then ⁅x, y⁆ else 0 := by
  by_cases hs : a.val + b.val = c.val
  · have hd : Disjoint a.val.support b.val.support :=
      (squarefreeExponent_add_iff a.val b.val a.property b.property).mp (hs.symm ▸ c.property)
    rw [if_pos hs, squarefreeMonomial_lie_disjoint a b hd]
    have he : a.disjointAdd b hd = c := Subtype.ext hs
    rw [he, squarefreePolynomialEquiv_monomial_self]
  · rw [if_neg hs]
    by_cases hd : Disjoint a.val.support b.val.support
    · rw [squarefreeMonomial_lie_disjoint a b hd]
      exact squarefreePolynomialEquiv_monomial_ne _ c
        (fun h => hs (congrArg Subtype.val h)) _
    · rw [squarefreeMonomial_lie_overlap a b hd, map_zero, Pi.zero_apply]

theorem squarefree_lie_coefficient (x y : SquarefreePolynomial ι L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv ⁅x, y⁆ c =
      ∑ a : SquarefreeIndex ι, ∑ b : SquarefreeIndex ι,
        if a.val + b.val = c.val then
          ⁅squarefreePolynomialEquiv x a, squarefreePolynomialEquiv y b⁆ else 0 := by
  conv_lhs => rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  simp only [map_sum, Finset.sum_apply, squarefreeMonomial_lie_coefficient]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

theorem SquarefreeIndex.ofFinset_add_complement [DecidableEq ι] (S T : Finset ι) (hST : S ⊆ T) :
    (ofFinset S).val + (ofFinset (T \ S)).val = (ofFinset T).val := by
  classical
  ext i
  simp only [Finsupp.add_apply, ofFinset_apply, Finset.mem_sdiff]
  by_cases hi : i ∈ S
  · simp only [hi, hST hi, not_true_eq_false, and_false, ite_true, ite_false, add_zero]
  · by_cases hj : i ∈ T <;> simp [hi, hj]

theorem SquarefreeIndex.blockDegree_ofFinset [DecidableEq σ] (π : ι → σ)
    (S : Finset ι) (i : σ) :
    blockDegree π (ofFinset S).val i = (S.filter fun j => π j = i).card := by
  classical
  rw [blockDegree_apply]
  simp only [ofFinset_apply]
  have h : (fun j => if π j = i then (if j ∈ S then 1 else 0) else 0) =
      (fun j => if j ∈ S ∧ π j = i then 1 else 0) := by
    funext j
    split_ifs <;> simp_all
  rw [h]
  have hs : (Finset.univ.filter fun j => j ∈ S ∧ π j = i) =
      S.filter (fun j => π j = i) := by ext j; simp
  simpa only [Finset.sum_boole, Nat.cast_id] using congrArg Finset.card hs

theorem SquarefreeIndex.blockDegree_support [DecidableEq σ] (π : ι → σ)
    (a : SquarefreeIndex ι) (i : σ) :
    blockDegree π a.val i = (a.val.support.filter fun j => π j = i).card := by
  rw [← blockDegree_ofFinset π a.val.support i, ofFinset_support]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]

noncomputable def squarefreeSplitSubsetEquiv (π : ι → σ) (c : SquarefreeIndex ι)
    (a b : σ → ℕ) (hc : blockDegree π c.val = a + b) :
    SquarefreeSplit π c a b ≃
      {T : Finset ι // T ⊆ c.val.support ∧ ∀ i, (T.filter fun j => π j = i).card = a i} where
  toFun p := ⟨p.val.1.val.support, by
    refine ⟨SquarefreeIndex.support_subset_of_add _ _ _ p.property.1, ?_⟩
    intro i
    rw [← SquarefreeIndex.blockDegree_support π p.val.1 i, p.property.2.1]⟩
  invFun T := by
    let u := SquarefreeIndex.ofFinset T.val
    let v := SquarefreeIndex.ofFinset (c.val.support \ T.val)
    have huv : u.val + v.val = c.val := by
      have h := SquarefreeIndex.ofFinset_add_complement T.val c.val.support T.property.1
      simpa only [SquarefreeIndex.ofFinset_support] using h
    have hu : blockDegree π u.val = a := by
      ext i
      exact (SquarefreeIndex.blockDegree_ofFinset π T.val i).trans (T.property.2 i)
    have hv : blockDegree π v.val = b := by
      have h := congrArg (blockDegree π) huv
      rw [blockDegree_add, hu, hc] at h
      exact add_left_cancel h
    exact ⟨(u, v), huv, hu, hv⟩
  left_inv p := squarefreeSplit_ext π c a b _ _ (SquarefreeIndex.ofFinset_support p.val.1)
  right_inv T := Subtype.ext (SquarefreeIndex.support_ofFinset T.val)

theorem card_squarefreeSplit (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (hc : blockDegree π c.val = a + b) :
    Fintype.card (SquarefreeSplit π c a b) = blockSplitMultiplicity a b := by
  classical
  rw [Fintype.card_congr (squarefreeSplitSubsetEquiv π c a b hc), card_blockSubsets]
  unfold blockSplitMultiplicity
  apply Finset.prod_congr rfl
  intro i _
  rw [← SquarefreeIndex.blockDegree_support π c i, hc, Pi.add_apply]

omit [Fintype σ] [DecidableEq ι] [DecidableEq σ] in
theorem squarefreeSplit_degree (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (p : SquarefreeSplit π c a b) : blockDegree π c.val = a + b := by
  rw [← p.property.1, blockDegree_add, p.property.2.1, p.property.2.2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeMonomial_component_mem (x : SquarefreePolynomial ι L)
    (hx : x ∈ F.squarefreeAdaptedModule π) (a : SquarefreeIndex ι) :
    squarefreeMonomial a (squarefreePolynomialEquiv x a) ∈ F.squarefreeAdaptedModule π := by
  by_cases ha : a.val = 0
  · rw [(hx a).2 ha, map_zero]
    exact (F.squarefreeAdaptedModule π).zero_mem
  · exact F.squarefreeMonomial_mem_adapted π a ha _ (hx a).1

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeOrderedGenerators
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem leadingCoordinateSubgroup_le_zmultiples (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    he.leadingCoordinateSubgroup hnil Γ j ≤ AddSubgroup.zmultiples ((l : ℚ)⁻¹) := by
  rintro q ⟨g, hg, _, rfl⟩
  obtain ⟨z, hz⟩ := (mem_denominatorGrid_iff l hl _).mp
    (hgrid ((bchSubgroupCoordinates_repr e Γ g).mpr hg))
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨z j, ?_⟩
  simpa only [zsmul_eq_mul, div_eq_mul_inv, Basis.equivFun_apply] using (hz j).symm

theorem leadingCoordinateSubgroup_isAddCyclic (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    IsAddCyclic (he.leadingCoordinateSubgroup hnil Γ j) :=
  AddSubgroup.isAddCyclic_of_le (he.leadingCoordinateSubgroup_le_zmultiples hnil Γ l hl hgrid j)

theorem exists_tail_generator (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    ∃ a ∈ Γ, a.coord ∈ basisTail e j.val ∧
      ∀ g ∈ Γ, g.coord ∈ basisTail e j.val →
        ∃ n : ℤ, ((a ^ n)⁻¹ * g).coord ∈ basisTail e (j.val + 1) := by
  let H := he.leadingCoordinateSubgroup hnil Γ j
  let : IsAddCyclic H := he.leadingCoordinateSubgroup_isAddCyclic hnil Γ l hl hgrid j
  obtain ⟨q, hq⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp inferInstance
  have hqmem : q ∈ H := hq ▸ AddSubgroup.mem_zmultiples q
  obtain ⟨a, ha, hat, haq⟩ := hqmem
  refine ⟨a, ha, hat, ?_⟩
  intro g hg hgt
  have hcoord : e.repr g.coord j ∈ H := ⟨g, hg, hgt, rfl⟩
  rw [← hq] at hcoord
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hcoord
  refine ⟨n, (mem_basisTail_succ_iff e j _).mpr ⟨?_, ?_⟩⟩
  · let T := NilpotentLieBCHGroup.subgroup (hnil := hnil) (he.tailIdeal j.val).toLieSubalgebra
    exact T.mul_mem (T.inv_mem (T.zpow_mem hat n)) hgt
  · change e.repr (lieBCH s (-((a ^ n).coord)) g.coord) j = 0
    rw [he.bch_low_coordinate hnil j.val _ hgt j le_rfl]
    simp only [map_neg, Finsupp.neg_apply, NilpotentLieBCHGroup.coord_zpow,
      map_zsmul, Finsupp.smul_apply, haq, hn, neg_add_cancel]

end Erdos3.IsCentralLieBasis

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem exists_ordered_lattice_generators (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin d → NilpotentLieBCHGroup L s hnil,
      (∀ j, a j ∈ Γ) ∧ (∀ j, (a j).coord ∈ basisTail e j.val) ∧
      ∀ g ∈ Γ, ∃ z : Fin d → ℤ, orderedZpowProduct a z = g := by
  classical
  choose a ha hat hpeel using fun j => he.exists_tail_generator hnil Γ l hl hgrid j
  have hfactor (k i : ℕ) (hik : i + k = d)
      (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Γ) (hgt : g.coord ∈ basisTail e i) :
      ∃ z : Fin d → ℤ, orderedGroupTailProduct (fun j => a j ^ z j) i = g := by
    induction k generalizing i g with
    | zero =>
        have hi : i = d := by omega
        subst i
        refine ⟨fun _ => 0, ?_⟩
        rw [orderedGroupTailProduct_terminal _ le_rfl]
        apply NilpotentLieBCHGroup.ext
        have hz : g.coord = 0 := by
          simpa only [basisTail_terminal, Submodule.mem_bot] using hgt
        exact hz.symm
    | succ k ih =>
        have hi : i < d := by omega
        let j : Fin d := ⟨i, hi⟩
        obtain ⟨n, hn⟩ := hpeel j g hg hgt
        let r := (a j ^ n)⁻¹ * g
        have hr : r ∈ Γ := Γ.mul_mem (Γ.inv_mem (Γ.zpow_mem (ha j) n)) hg
        obtain ⟨z, hz⟩ := ih (i + 1) (by omega) r hr hn
        let u := Function.update z j n
        have huj : u j = n := by simp [u]
        have hu : orderedGroupTailProduct (fun j => a j ^ u j) (i + 1) =
            orderedGroupTailProduct (fun j => a j ^ z j) (i + 1) := by
          apply orderedGroupTailProduct_congr
          intro v hv
          have hvj : v ≠ j := by
            intro h
            subst v
            change i + 1 ≤ i at hv
            omega
          change a v ^ Function.update z j n v = a v ^ z v
          rw [Function.update_of_ne hvj]
        refine ⟨u, ?_⟩
        change orderedGroupTailProduct (fun j => a j ^ u j) j.val = g
        rw [orderedGroupTailProduct_step, huj]
        change a j ^ n * orderedGroupTailProduct (fun j => a j ^ u j) (i + 1) = g
        rw [hu, hz]
        exact mul_inv_cancel_left (a j ^ n) g
  refine ⟨a, ha, hat, ?_⟩
  intro g hg
  exact hfactor d 0 (by omega) g hg (by simp [basisTail_zero])

theorem exists_surjective_orderedZpowProduct (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin d → Γ, Function.Surjective (orderedZpowProduct a) := by
  obtain ⟨a, ha, _, hgen⟩ := he.exists_ordered_lattice_generators hnil Γ l hl hgrid
  refine ⟨fun j => ⟨a j, ha j⟩, ?_⟩
  intro g
  obtain ⟨z, hz⟩ := hgen g g.property
  refine ⟨z, Subtype.ext ?_⟩
  change Γ.subtype (orderedZpowProduct (fun j => ⟨a j, ha j⟩) z) = g.val
  rw [orderedZpowProduct_map]
  exact hz

end Erdos3.IsCentralLieBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CentralBasisPowerCover
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem subgroupPowerCover_index_le (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ d := by
  obtain ⟨a, ha⟩ := he.exists_surjective_orderedZpowProduct hnil Γ l hl hgrid
  have h := powerSubgroup_index_le_of_ordered_generators a ha m hm
  simpa only [Subgroup.relIndex, subgroupPowerCover_subgroupOf] using h

end Erdos3.IsCentralLieBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSquarefreeCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem realSquarefreeMonomial_self (a : SquarefreeIndex ι) (x : ℝ ⊗[ℚ] L) :
    realSquarefreePolynomialEquiv ((squarefreeMonomial a).baseChange ℝ x) a = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      squarefreePolynomialEquiv_monomial_self]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realSquarefreeMonomial_ne (a c : SquarefreeIndex ι) (hac : a ≠ c) (x : ℝ ⊗[ℚ] L) :
    realSquarefreePolynomialEquiv ((squarefreeMonomial a).baseChange ℝ x) c = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      squarefreePolynomialEquiv_monomial_ne a c hac, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealBlockPolynomialEval
namespace OAI

section

namespace Erdos3

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def blockMonomial (π : ι → σ) (a : σ → ℕ) : L →ₗ[ℚ] SquarefreePolynomial ι L := by
  classical
  exact squarefreePolynomialEquiv.symm.toLinearMap.comp
    (LinearMap.pi fun c : SquarefreeIndex ι => if blockDegree π c.val = a then LinearMap.id else 0)

theorem blockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (blockMonomial π a x) c =
      if blockDegree π c.val = a then x else 0 := by
  classical
  simp only [blockMonomial, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

noncomputable def factorialBlockMonomial (π : ι → σ) (a : σ → ℕ) :
    L →ₗ[ℚ] SquarefreePolynomial ι L :=
  (multidegreeFactorial a : ℚ) • blockMonomial π a

theorem factorialBlockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (factorialBlockMonomial π a x) c =
      if blockDegree π c.val = a then (multidegreeFactorial a : ℚ) • x else 0 := by
  simp only [factorialBlockMonomial, LinearMap.smul_apply, map_smul, Pi.smul_apply,
    blockMonomial_coefficient, smul_ite, smul_zero]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem realFactorialBlockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] L) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv ((factorialBlockMonomial π a).baseChange ℝ x) c =
      if blockDegree π c.val = a then (multidegreeFactorial a : ℚ) • x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      factorialBlockMonomial_coefficient]
    by_cases h : blockDegree π c.val = a
    · simp only [h, ite_true, TensorProduct.tmul_smul]
    · simp only [h, ite_false, TensorProduct.tmul_zero]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy]
    split_ifs <;> simp only [smul_add, add_zero]

noncomputable def realBlockPolynomialEval (π : ι → σ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (x : σ → ℚ) : ℝ ⊗[ℚ] SquarefreePolynomial ι L :=
  ∑ a ∈ (coefficients p).support,
    (a.prod fun i n => x i ^ n) • (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p a)

theorem realBlockPolynomialEval_coefficient (π : ι → σ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (x : σ → ℚ) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (realBlockPolynomialEval π p x) c =
      ((blockExponent π c.val).prod fun i n => x i ^ n) •
        ((multidegreeFactorial (blockDegree π c.val) : ℚ) •
          coefficients p (blockExponent π c.val)) := by
  classical
  simp only [realBlockPolynomialEval, map_sum, Finset.sum_apply, map_rat_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single (blockExponent π c.val)]
  · simp only [realFactorialBlockMonomial_coefficient, blockExponent_apply, ite_true]
  · intro a _ ha
    rw [realFactorialBlockMonomial_coefficient]
    have hca : blockDegree π c.val ≠ (fun i => a i) := by
      intro h
      apply ha
      ext i
      exact (congrFun h i).symm
    rw [if_neg hca, smul_zero]
  · intro hc
    rw [Finsupp.notMem_support_iff.mp hc, map_zero, map_zero, Pi.zero_apply, smul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeComponent (a : SquarefreeIndex ι) :
    F.SquarefreeAlgebra π →ₗ[ℚ] F.SquarefreeAlgebra π where
  toFun x := ⟨squarefreeMonomial a (squarefreePolynomialEquiv x.val a),
    F.squarefreeMonomial_component_mem π x.val x.property a⟩
  map_add' x y := by
    apply Subtype.ext
    change squarefreeMonomial a (squarefreePolynomialEquiv (x.val + y.val) a) = _
    simp only [map_add, Pi.add_apply]
    rfl
  map_smul' r x := by
    apply Subtype.ext
    change squarefreeMonomial a (squarefreePolynomialEquiv (r • x.val) a) = _
    simp only [map_smul, Pi.smul_apply]
    rfl

theorem sum_squarefreeComponent (x : F.SquarefreeAlgebra π) :
    ∑ a : SquarefreeIndex ι, F.squarefreeComponent π a x = x := by
  classical
  apply Subtype.ext
  change (F.squarefreeAdaptedSubalgebra π).incl (∑ a, F.squarefreeComponent π a x) = x.val
  rw [map_sum]
  exact sum_squarefreeMonomial x.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeMultidegreeLayer (c : ι → ℕ) : Submodule ℚ (F.SquarefreeAlgebra π) :=
  (squarefreeSupportModule (fun a : SquarefreeIndex ι => c ≤ fun i => a.val i)).comap
    (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap

theorem squarefreeMultidegreeLayer_antitone : Antitone (F.squarefreeMultidegreeLayer π) := by
  intro c d h x hx a ha
  exact hx a (fun hd => ha (h.trans hd))

theorem squarefreeMultidegreeLayer_lie_mem {c d : ι → ℕ} {x y : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeMultidegreeLayer π c) (hy : y ∈ F.squarefreeMultidegreeLayer π d) :
    ⁅x, y⁆ ∈ F.squarefreeMultidegreeLayer π (c + d) := by
  apply squarefreeSupportModule_lie_mem (x := x.val) (y := y.val) ?_ hx hy
  intro a b hab ha hb i
  exact Nat.add_le_add (ha i) (hb i)

theorem squarefreeMultidegreeLayer_le_degree (c : ι → ℕ) (n : ℕ) (h : n ≤ ∑ i, c i) :
    F.squarefreeMultidegreeLayer π c ≤ F.squarefreeDegreeLayer π n := by
  intro x hx a ha
  apply hx a
  intro hca
  exact ha (h.trans (Finset.sum_le_sum fun i _ => hca i))

theorem squarefreeComponent_mem_multidegree (a : SquarefreeIndex ι) (x : F.SquarefreeAlgebra π) :
    F.squarefreeComponent π a x ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) := by
  exact squarefreeMonomial_mem_support a (fun _ => le_rfl) _

theorem squarefreeComponent_eq_zero_of_degree {n : ℕ} {x : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeDegreeLayer π n) (a : SquarefreeIndex ι) (ha : ¬n ≤ ∑ i, a.val i) :
    F.squarefreeComponent π a x = 0 := by
  apply Subtype.ext
  change squarefreeMonomial a (squarefreePolynomialEquiv x.val a) = 0
  have hz : squarefreePolynomialEquiv x.val a = 0 := hx a ha
  rw [hz, map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonProductLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) :=
  (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n)

theorem comparisonProductLayer_antitone : Antitone (F.comparisonProductLayer π) :=
  fun _ _ h _ hx => ⟨F.ordinary.antitone h hx.1, F.squarefreeDegreeLayer_antitone π h hx.2⟩

theorem comparisonProductLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonProductLayer π i) (hy : y ∈ F.comparisonProductLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonProductLayer π (i + j) :=
  ⟨F.ordinary.lie_mem hx.1 hy.1, F.squarefreeDegreeLayer_lie_mem π hx.2 hy.2⟩

theorem comparisonProductLayer_terminal :
    F.comparisonProductLayer π (max s (Fintype.card ι) + 1) = ⊥ := by
  change (F.ordinary.layer _).prod ((F.squarefreeOrdinaryFiltration π).layer _) = ⊥
  rw [F.ordinary.layer_eq_bot_above_step (by omega),
    (F.squarefreeOrdinaryFiltration π).layer_eq_bot_above_step (by omega)]
  ext x
  simp only [Submodule.mem_prod, Submodule.mem_bot, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeMultidegreeLayer_zero : F.squarefreeMultidegreeLayer π 0 = ⊤ := by
  apply top_unique
  intro x _ a ha
  exact False.elim (ha (fun _ => Nat.zero_le _))

theorem squarefreeMultidegreeLayer_terminal (c : ι → ℕ) (hc : ¬c ≤ (fun _ => 1)) :
    F.squarefreeMultidegreeLayer π c = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Subtype.ext
  apply squarefreePolynomialEquiv.injective
  ext a
  exact hx a (fun hca => hc (fun i => (hca i).trans (a.property i)))

theorem squarefree_degree_eq (n : ℕ) :
    F.squarefreeDegreeLayer π n =
      ⨆ (c : ι → ℕ) (_hc : n ≤ ∑ i, c i), F.squarefreeMultidegreeLayer π c := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← F.sum_squarefreeComponent π x]
    apply Submodule.sum_mem
    intro a _
    by_cases ha : n ≤ ∑ i, a.val i
    · have hle : F.squarefreeMultidegreeLayer π (fun i => a.val i) ≤
          ⨆ (c : ι → ℕ) (_hc : n ≤ ∑ i, c i), F.squarefreeMultidegreeLayer π c :=
        le_iSup_of_le (fun i => a.val i) (le_iSup_of_le ha le_rfl)
      exact hle (F.squarefreeComponent_mem_multidegree π a x)
    · rw [F.squarefreeComponent_eq_zero_of_degree π hx a ha]
      exact Submodule.zero_mem _
  · apply iSup_le
    intro c
    apply iSup_le
    intro hc
    exact F.squarefreeMultidegreeLayer_le_degree π c n hc

noncomputable def squarefreeMultidegreeFiltration :
    MultidegreeLieFiltration ι (F.SquarefreeAlgebra π) (Fintype.card ι) (fun _ => 1) where
  ordinary := F.squarefreeOrdinaryFiltration π
  layer := F.squarefreeMultidegreeLayer π
  antitone := F.squarefreeMultidegreeLayer_antitone π
  zero_eq_top := F.squarefreeMultidegreeLayer_zero π
  lie_mem := F.squarefreeMultidegreeLayer_lie_mem π
  terminal := F.squarefreeMultidegreeLayer_terminal π
  degree_eq := F.squarefree_degree_eq π

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeLayerMap (a : SquarefreeIndex ι) :
    F.layer (blockDegree π a.val) →ₗ[ℚ] F.SquarefreeAlgebra π := by
  classical
  exact if ha : a.val = 0 then 0 else
    { toFun := fun v => ⟨squarefreeMonomial a v.val, F.squarefreeMonomial_mem_adapted π a ha v.val v.property⟩
      map_add' := fun v w => Subtype.ext (map_add (squarefreeMonomial a) v.val w.val)
      map_smul' := fun r v => Subtype.ext (map_smul (squarefreeMonomial a) r v.val) }

theorem squarefreeLayerMap_zero (a : SquarefreeIndex ι) (ha : a.val = 0)
    (v : F.layer (blockDegree π a.val)) : F.squarefreeLayerMap π a v = 0 := by
  simp only [squarefreeLayerMap, dif_pos ha, LinearMap.zero_apply]

theorem squarefreeLayerMap_coe (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : F.layer (blockDegree π a.val)) :
    (F.squarefreeLayerMap π a v).val = squarefreeMonomial a v.val := by
  simp only [squarefreeLayerMap, dif_neg ha, LinearMap.coe_mk, AddHom.coe_mk]

theorem squarefreeLayerMap_mem (a : SquarefreeIndex ι) (v : F.layer (blockDegree π a.val)) :
    F.squarefreeLayerMap π a v ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) := by
  by_cases ha : a.val = 0
  · rw [F.squarefreeLayerMap_zero π a ha]
    exact Submodule.zero_mem _
  · change (F.squarefreeLayerMap π a v).val ∈ squarefreeSupportModule _
    rw [F.squarefreeLayerMap_coe π a ha]
    exact squarefreeMonomial_mem_support a (fun _ => le_rfl) v.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem factorialBlockMonomial_mem_adapted (a : σ → ℕ) (ha : a ≠ 0)
    (x : L) (hx : x ∈ F.layer a) :
    factorialBlockMonomial π a x ∈ F.squarefreeAdaptedModule π := by
  classical
  intro c
  rw [factorialBlockMonomial_coefficient]
  by_cases hca : blockDegree π c.val = a
  · rw [if_pos hca]
    refine ⟨?_, ?_⟩
    · rw [hca]
      exact (F.layer a).smul_mem _ hx
    · intro hc
      apply False.elim
      apply ha
      rw [hc, blockDegree_zero] at hca
      exact hca.symm
  · rw [if_neg hca]
    exact ⟨(F.layer _).zero_mem, fun _ => rfl⟩

noncomputable def blockLayerMap (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] F.SquarefreeAlgebra π where
  toFun x := ⟨factorialBlockMonomial π a x.val,
    F.factorialBlockMonomial_mem_adapted π a ha x.val x.property⟩
  map_add' x y := Subtype.ext (map_add (factorialBlockMonomial π a) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (factorialBlockMonomial π a) r x.val)

theorem blockLayerMap_coe (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    (F.blockLayerMap π a ha x).val = factorialBlockMonomial π a x.val := rfl

theorem blockLayerMap_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.blockLayerMap π a ha x ∈ F.squarefreeDegreeLayer π (∑ i, a i) := by
  classical
  intro c hc
  change squarefreePolynomialEquiv (factorialBlockMonomial π a x.val) c = 0
  rw [factorialBlockMonomial_coefficient]
  apply if_neg
  intro hca
  apply hc
  have ht : (∑ i, a i) = ∑ j, c.val j := by
    rw [← hca]
    exact blockDegree_total π c.val
  exact ht.le

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTripleLayers
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedSubalgebra (c : σ → ℕ) : LieSubalgebra ℚ L :=
  (F.weightedLayer c 1).toLieSubalgebra

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem additiveTripleLayer_coordinates (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {n : ℕ} {x : L × L × L} (hx : x ∈ F.additiveTripleLayer i c n) :
    x.1 ∈ F.ordinary.layer n ∧ x.2.1 ∈ F.ordinary.layer n ∧ x.2.2 ∈ F.ordinary.layer n := by
  have ha := F.weightedLayer_le_ordinary c hc n hx.1
  have hb := hx.2.1.2
  have hc' := hx.2.2.2
  have heq := tripleAssemble_decompose x
  rw [← heq]
  exact ⟨(F.ordinary.layer n).add_mem ((F.ordinary.layer n).add_mem ha hb) hc',
    (F.ordinary.layer n).add_mem ha hb, (F.ordinary.layer n).add_mem ha hc'⟩

theorem additiveTripleLayer_terminal (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleLayer i c (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨h₁, h₂, h₃⟩ := F.additiveTripleLayer_coordinates i c hc hx
  simp only [F.ordinary.terminal, Submodule.mem_bot] at h₁ h₂ h₃
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

theorem additiveTripleLayer_top_relation (i : σ) (c : σ → ℕ)
    (htop : F.weightedLayer c s = ⊥) {x : L × L × L}
    (hx : x ∈ F.additiveTripleLayer i c s) : x.1 = x.2.1 + x.2.2 := by
  have h : tripleNeutral x ∈ F.weightedLayer c s := hx.1
  rw [htop, LieSubmodule.mem_bot] at h
  change x.2.1 + x.2.2 - x.1 = 0 at h
  exact (sub_eq_zero.mp h).symm

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleFiltration (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    NilpotentLieFiltration (F.additiveTripleSubalgebra i hi c hc) s where
  layer n := (F.additiveTripleLayer i c n).comap (F.additiveTripleSubalgebra i hi c hc).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.additiveTripleLayer_antitone i c h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.additiveTripleLayer_lie_mem i hi c hc hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    have h : (x : L × L × L) ∈ F.additiveTripleLayer i c (s + 1) := hx
    rw [F.additiveTripleLayer_terminal i c hc, Submodule.mem_bot] at h
    exact h

theorem additiveTripleProjections_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {n : ℕ}
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer n) :
    F.additiveTripleFirst i hi c hc x ∈ F.ordinary.layer n ∧
    F.additiveTripleSecond i hi c hc x ∈ F.ordinary.layer n ∧
    F.additiveTripleThird i hi c hc x ∈ F.ordinary.layer n :=
  F.additiveTripleLayer_coordinates i c hc hx

theorem additiveTripleTop_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (htop : F.weightedLayer c s = ⊥)
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer s) :
    F.additiveTripleFirst i hi c hc x =
      F.additiveTripleSecond i hi c hc x + F.additiveTripleThird i hi c hc x :=
  F.additiveTripleLayer_top_relation i c htop hx

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem tripleToPi_injective : Function.Injective (tripleToPi (L := L)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem additiveTripleToPi_injective (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    Function.Injective (F.additiveTripleToPi i hi c hc) :=
  fun _ _ h => Subtype.ext (tripleToPi_injective h)

end MultidegreeLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def WeightedAdapted (c : σ → ℕ) (v : τ → ℕ) (p : VectorPolynomial τ ℚ L) : Prop :=
  ∀ a, coefficients p a ∈ F.weightedLayer c (Finsupp.weight v a)

theorem weightedAdapted_substitute (c : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (c i)) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted p) : F.WeightedAdapted c v (VectorPolynomial.substitute f p) := by
  intro a
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro b _
  by_cases hc : (MvPolynomial.aeval (R := ℚ) f (MvPolynomial.monomial b 1)).coeff a = 0
  · rw [hc, zero_smul]
    exact LieSubmodule.zero_mem _
  · apply Submodule.smul_mem
    have hb : coefficients p b ∈ F.weightedLayer c (Finsupp.weight c b) :=
      F.layer_le_weightedLayer c (fun i => b i) _ (by rw [multidegreeWeight_finsupp]) (hp b)
    exact F.weightedLayer_antitone c
      (aeval_monomial_weightedSupport f c v hf b (MvPolynomial.mem_support_iff.mpr hc)) hb

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem additiveTriple_top_group_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (htop : F.weightedLayer c s = ⊥)
    (g : (F.additiveTripleFiltration i hi c hc).Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).subgroup s) :
    (NilpotentLieBCHGroup.map (F.additiveTripleFirst i hi c hc) g : F.Group) =
      NilpotentLieBCHGroup.map (F.additiveTripleSecond i hi c hc) g *
      NilpotentLieBCHGroup.map (F.additiveTripleThird i hi c hc) g := by
  apply NilpotentLieBCHGroup.ext
  change F.additiveTripleFirst i hi c hc g.coord =
    lieBCH s (F.additiveTripleSecond i hi c hc g.coord) (F.additiveTripleThird i hi c hc g.coord)
  rw [lieBCH_eq_add_of_lie_eq_zero F.ordinary.lowerCentralSeries_eq_bot
    (F.ordinary.top_layer_central (F.additiveTripleProjections_mem i hi c hc hg).2.1 _)]
  exact F.additiveTripleTop_relation i hi c hc htop hg

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {τ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients_mem (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (a : τ →₀ ℕ) :
    coefficients q a ∈ F.dilationPairSubalgebra r := by
  by_cases ha : a = 0
  · rw [ha, hq0]
    exact (F.dilationPairSubalgebra r).zero_mem
  · have hpos : 0 < Finsupp.weight w a :=
      NilpotentLieFiltration.positive_weight_of_ne_zero w hw ha
    exact F.dilationPairLayer_antitone r (Nat.succ_le_of_lt hpos) (hq a)

noncomputable def restrictDilationPairPolynomial (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    VectorPolynomial τ ℚ (F.dilationPairSubalgebra r) :=
  restrictCoefficients (F.dilationPairSubalgebra r).toSubmodule q
    (F.dilationPair_coefficients_mem r w hw q hq hq0)

theorem restrictDilationPairPolynomial_eval (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℚ) :
    (eval (V := F.dilationPairSubalgebra r) x
      (F.restrictDilationPairPolynomial r w hw q hq hq0) : L × L) = eval x q :=
  eval_restrictCoefficients (F.dilationPairSubalgebra r).toSubmodule q
    (F.dilationPair_coefficients_mem r w hw q hq hq0) x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedNormalizationLog (p : VectorPolynomial τ ℚ L) (a b : F.Group) :
    VectorPolynomial τ ℚ L :=
  lieBCH s (lieBCH s (monomial 0 (-a.coord)) p) (monomial 0 (-b.coord))

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem adaptedBasis_weight_pos (i : ι) : 0 < ω i := by
  by_contra hi
  have hb : b i ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hz := (F.mem_layer_iff_basis_coordinates b ω hlayers 1 (b i)).mp hb i (by omega)
  simp at hz

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

include hlayers

theorem realSymbolRepresentative_constant (x : F.RealPolynomialSymbol w) :
    coefficients (F.realSymbolRepresentative b ω hlayers w x) 0 = 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  change (b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w x) 0) i = 0
  apply F.realSymbolRepresentative_coefficient_of_ne
  rw [map_zero]
  exact (F.adaptedBasis_weight_pos b ω hlayers i).ne

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedBasisSplitting_real_coordinate (x : ℝ ⊗[ℚ] F.AssociatedGraded) (i : ι) :
    (b.baseChange ℝ).repr
      ((F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ x) i =
      ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul]
    exact congrArg (fun q : ℚ => q • a) (F.gradedBasisSplitting_coordinate b ω hlayers x i)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeTopDegree
namespace OAI

section

namespace Erdos3

noncomputable def SquarefreeIndex.full (ι : Type*) [Fintype ι] : SquarefreeIndex ι :=
  ⟨Finsupp.equivFunOnFinite.symm (fun _ => 1), fun _ => le_rfl⟩

theorem SquarefreeIndex.full_apply {ι : Type*} [Fintype ι] (i : ι) :
    (full ι).val i = 1 := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdditiveTriplePolynomialRestriction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem additiveTriple_coefficients_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (a : τ →₀ ℕ) :
    coefficients q a ∈ F.additiveTripleSubalgebra i hi c hc := by
  by_cases ha : a = 0
  · rw [ha, hq0]
    exact (F.additiveTripleSubalgebra i hi c hc).zero_mem
  · have hpos : 0 < Finsupp.weight w a :=
      NilpotentLieFiltration.positive_weight_of_ne_zero w hw ha
    exact F.additiveTripleLayer_antitone i c (Nat.succ_le_of_lt hpos) (hq a)

noncomputable def restrictAdditiveTriplePolynomial (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    VectorPolynomial τ ℚ (F.additiveTripleSubalgebra i hi c hc) :=
  restrictCoefficients (F.additiveTripleSubalgebra i hi c hc).toSubmodule q
    (F.additiveTriple_coefficients_mem i hi c hc w hw q hq hq0)

theorem restrictAdditiveTriplePolynomial_adapted (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.additiveTripleFiltration i hi c hc).Adapted w
      (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) := by
  apply ((F.additiveTripleFiltration i hi c hc).adapted_iff_coefficients w _).mpr
  intro a
  change (coefficients (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) a : L × L × L) ∈
    F.additiveTripleLayer i c (Finsupp.weight w a)
  rw [restrictAdditiveTriplePolynomial, coefficients_restrictCoefficients]
  exact hq a

theorem restrictAdditiveTriplePolynomial_eval (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℚ) :
    (eval (V := F.additiveTripleSubalgebra i hi c hc) x
      (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) : L × L × L) = eval x q :=
  eval_restrictCoefficients (F.additiveTripleSubalgebra i hi c hc).toSubmodule q
    (F.additiveTriple_coefficients_mem i hi c hc w hw q hq hq0) x

noncomputable def restrictAdditiveTripleOrbit (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) : (F.additiveTripleFiltration i hi c hc).PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0)
    (F.restrictAdditiveTriplePolynomial_adapted i hi c hc w hw q hq hq0)

theorem restrictAdditiveTripleOrbit_eval (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℤ) :
    (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w x
      (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0)).coord : L × L × L) =
      eval (fun j => (x j : ℚ)) q :=
  F.restrictAdditiveTriplePolynomial_eval i hi c hc w hw q hq hq0 _

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateSplit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem split_substitution_adapted (i : σ) (u : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.ordinary.Adapted (fun _ : Option σ => 1)
      (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) :=
  F.ordinary.adapted_substitute (fun _ => 1) (fun _ => 1) _
    (splitCoordinatePolynomial_support i u hu) (F.adapted_ordinary hp)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffineTriplePolynomial
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ V : Type*} [DecidableEq σ] [AddCommGroup V] [Module ℚ V]

noncomputable def splitTriple (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) : VectorPolynomial (Option σ) ℚ (V × V × V) :=
  pair (substitute (splitCoordinatePolynomial i (u + v)) p)
    (pair (substitute (splitCoordinatePolynomial i u) p)
      (substitute (splitCoordinatePolynomial i v) p))

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem splitTriple_neutral (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleNeutral (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) a +
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a = _
  rw [h]
  abel

theorem splitTriple_left (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleLeft (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
        VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair, map_sub, Finsupp.sub_apply]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a = _
  rw [h]
  abel

theorem splitTriple_right (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleRight (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p -
        VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair, map_sub, Finsupp.sub_apply]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) a = _
  rw [h]
  abel

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

theorem replicated_blockDegree_full {σ : Type*} [Fintype σ] (bound : σ → ℕ) :
    blockDegree (fun j : ReplicatedIndex bound => j.1)
      (SquarefreeIndex.full (ReplicatedIndex bound)).val = bound := by
  ext i
  rw [replicated_blockDegree_apply]
  simp only [SquarefreeIndex.full_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def rationalOutputDensity {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : ℝ :=
  Fintype.card (J → ZMod N) * finiteImageMass p (fun x j => (Y x j : ZMod N)) b

noncomputable def rationalInactiveForecast {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (b : J → ZMod N) : ℝ :=
  gridVolume * inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCoefficientRemainder
namespace OAI

section

namespace Erdos3

open Module Submodule

namespace VectorPolynomial

theorem canonicalCoefficientSample_integer_remainder {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
    ∃ z : ℤ, (c ⟨j, d⟩).val i - normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (mixedArrayRegroup (I j) (Fin (n j)) _ (a j) d)) i = z := by
  have he := congrArg (fun y => euclideanCoefficientEquiv U y j d) hc
  simp only [canonicalCoefficientSample, AddEquiv.apply_symm_apply, euclideanCoefficientEquiv_mk] at he
  have hm := normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace (U j)) (b j) (hb j)
    ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, d⟩)) _ he.symm
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice (J j) _).mp hm i
  exact ⟨z, hz.symm⟩

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BlockLayerBracket
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem blockMonomial_lie_coefficient [DecidableEq ι] [DecidableEq σ] (π : ι → σ) (a b : σ → ℕ)
    (x y : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv ⁅blockMonomial π a x, blockMonomial π b y⁆ c =
      Fintype.card (SquarefreeSplit π c a b) • ⁅x, y⁆ := by
  classical
  rw [squarefree_lie_coefficient]
  simp only [blockMonomial_coefficient]
  have hterm (u v : SquarefreeIndex ι) :
      (if u.val + v.val = c.val then
        ⁅if blockDegree π u.val = a then x else 0,
          if blockDegree π v.val = b then y else 0⁆ else 0) =
      if u.val + v.val = c.val ∧ blockDegree π u.val = a ∧ blockDegree π v.val = b
        then ⁅x, y⁆ else 0 := by
    by_cases hs : u.val + v.val = c.val <;>
      by_cases hu : blockDegree π u.val = a <;>
      by_cases hv : blockDegree π v.val = b <;> simp [hs, hu, hv]
  simp_rw [hterm]
  rw [← Fintype.sum_prod_type']
  rw [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const]

theorem blockMonomial_lie (π : ι → σ) (a b : σ → ℕ) (x y : L) :
    ⁅blockMonomial π a x, blockMonomial π b y⁆ =
      blockSplitMultiplicity a b • blockMonomial π (a + b) ⁅x, y⁆ := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext c
  rw [blockMonomial_lie_coefficient, map_nsmul, Pi.smul_apply, blockMonomial_coefficient]
  by_cases hc : blockDegree π c.val = a + b
  · rw [if_pos hc, card_squarefreeSplit π c a b hc]
  · have hz : Fintype.card (SquarefreeSplit π c a b) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun p => hc (squarefreeSplit_degree π c a b p)⟩
    rw [hz, zero_smul, if_neg hc, smul_zero]

theorem factorialBlockMonomial_lie (π : ι → σ) (a b : σ → ℕ) (x y : L) :
    ⁅factorialBlockMonomial π a x, factorialBlockMonomial π b y⁆ =
      factorialBlockMonomial π (a + b) ⁅x, y⁆ := by
  simp only [factorialBlockMonomial, LinearMap.smul_apply, smul_lie, lie_smul, blockMonomial_lie]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
  have h := congrArg (fun n : ℕ => (n : ℚ)) (multidegreeFactorial_split a b)
  simp only [Nat.cast_mul] at h
  rw [mul_comm (multidegreeFactorial b : ℚ) (multidegreeFactorial a : ℚ), h]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem blockLayerMap_lie (a b : σ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (x : F.layer a) (y : F.layer b) :
    ⁅F.blockLayerMap π a ha x, F.blockLayerMap π b hb y⁆ =
      F.blockLayerMap π (a + b) hab ⟨⁅x.val, y.val⁆, F.lie_mem x.property y.property⟩ := by
  apply Subtype.ext
  exact factorialBlockMonomial_lie π a b x.val y.val

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_active (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    allocatedPrincipalSides B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩ = S.value := by
  simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
    layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
    integerAxisSideLength, hactive, ↓reduceIte]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedIntegerProfileCenters (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileCenter (layerIntegerPrincipalSlots B j i)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)

noncomputable def allocatedIntegerProfileWidths (R σ : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileWidth (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (R j/4) (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedIntegerProfileScales (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  fun d => (basisAxisScale (basis j) i : ℝ)/monomialScale (layerSamplerBox B U basis S) d.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedContinuousProfileCenters (R : Fin m → ℝ) (j : Fin m) (i : I j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileCenter (layerContinuousPrincipalSlots B j i)
    (principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card)

noncomputable def allocatedContinuousProfileWidths (R σ : Fin m → ℝ) (j : Fin m) (i : I j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileWidth (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (R j/4) (principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedContinuousProfileScales (j : Fin m) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  fun d => 1 / monomialScale (layerSamplerBox B U basis S) d.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedAxisProfilePolynomial (R σ : Fin m → ℝ) :
    (a : LayerSamplerAxis I n) → (SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) →
    MvPolynomial (LayerSamplerVariables G I n B) ℝ
  | ⟨j, .inl i⟩, r => monomialArrayPolynomial Subtype.val (fun e =>
      allocatedContinuousProfileCenters B R j i e + allocatedContinuousProfileWidths B R σ j i e * r e)
  | ⟨j, .inr i⟩, r => monomialArrayPolynomial Subtype.val (fun e =>
      allocatedIntegerProfileCenters B R j i e + allocatedIntegerProfileWidths B R σ j i e * r e)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

noncomputable def allocatedPhysicalCubeRoot : LayerSamplerVariables G I n B → ℤ :=
  fun k => c k + Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k

noncomputable def allocatedPhysicalCubeDirections : Matrix α (LayerSamplerVariables G I n B) ℤ :=
  fun i => Sum.elim (fun g => (x g (some i) : ℤ)) (fun j => (y j (some i) : ℤ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

noncomputable def allocatedPhysicalRootBudget : ℝ :=
  (∑ k, |(c k : ℝ)|) + Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Output" => (Σ _a : Active, Unit)

noncomputable def allocatedFixedPathPrincipal
    (r : Coeff → ℝ) (a : Active) (b : B a.val) : ℝ :=
  (allocatedAxisProfilePolynomial B R σ a.val (fun e => r ⟨a, e⟩)).coeff
    (canonicalPrincipalExponent degree a.val b) / R a.val.1

noncomputable def allocatedFixedPathShift (r : Coeff → ℝ) (a : Active) : ℝ :=
  (allocatedAxisProfilePolynomial B R σ a.val (fun e => r ⟨a, e⟩)).coeff 0 / R a.val.1

noncomputable def allocatedFixedPathLiftDensity
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) : (Output → ℝ) → ℝ :=
  jointSlicedPrincipalDensity hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (allocatedFixedPathPrincipal B P R σ r) lower width (allocatedFixedPathShift B P R σ r)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

noncomputable def allocatedSampleNormalizedCoefficients (sample : Sample) :
    (a : LayerSamplerAxis I n) → SamplerCoefficientSlot G B degree a → ℝ
  | ⟨j, .inl i⟩, e => (sample j).1 i e / allocatedContinuousProfileScales B U basis S j e
  | ⟨j, .inr i⟩, e => ((sample j).2 i e : ℝ) / allocatedIntegerProfileScales B U basis S j i e

noncomputable def allocatedSampleProfileNoise (sample : Sample) :
    (a : LayerSamplerAxis I n) → SamplerCoefficientSlot G B degree a → ℝ
  | ⟨j, .inl i⟩, e =>
    (allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ e -
      allocatedContinuousProfileCenters B R j i e) / allocatedContinuousProfileWidths B R σ j i e
  | ⟨j, .inr i⟩, e =>
    (allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
      allocatedIntegerProfileCenters B R j i e) / allocatedIntegerProfileWidths B R σ j i e

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

def allocatedShortAxis (L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L ^ (j.val + 1)

noncomputable instance allocatedShortAxisDecidable (L : ℕ) :
    DecidablePred (allocatedShortAxis (I := I) U basis L) := Classical.decPred _

variable (P : LayerSamplerAxis I n → Prop)

noncomputable def allocatedSampleRestrictedProfileNoise (sample : Sample) :
    ActiveProfileCoefficientIndex G B degree P → ℝ :=
  fun e => allocatedSampleProfileNoise B U basis S sample e.1.val e.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

def allocatedOriginalSampleInactiveCoefficients
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ :=
  fun a d => (sample (selected a).1).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientIntegerFloorRemainder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientSample_floor_coefficient_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
    (c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i =
      (⌊(c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i⌋ : ℤ) := by
  obtain ⟨z, hz⟩ := canonicalCoefficientSample_integer_remainder U b hb o a c hc j d i
  rw [mixedLiftCoefficient_eq, hz, Int.floor_intCast]

theorem canonicalCoefficientSample_floor_polynomial_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (i : J j) :
    coefficientRowPolynomial U c j i =
      mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j) i +
        MvPolynomial.map (Int.castRingHom ℝ) (coefficientIntegerFloorPolynomial U b o a c j i) ∧
      (coefficientIntegerFloorPolynomial U b o a c j i).totalDegree ≤ j.val + 1 := by
  refine ⟨?_, coefficientIntegerFloorPolynomial_degree U b o a c j i⟩
  rw [coefficientIntegerFloorPolynomial, integerMonomialArrayPolynomial_map]
  change (∑ d : BoundedCoefficientExponent K (j.val + 1), MvPolynomial.monomial d.val ((c ⟨j,d⟩).val i)) = _
  unfold mixedLiftPolynomial monomialArrayPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_add]
  apply congrArg (MvPolynomial.monomial d.val)
  have hd := canonicalCoefficientSample_floor_coefficient_remainder U b hb o a c hc j d i
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLieDegreeLengthSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem weightedLieDegreeLengthSpan_top_le_ker {A : Type*} [AddCommGroup A] [Module ℚ A]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma I, lieTreeWeight w a = s → a.length = r → η (lieTreeEval v a) = 0) :
    weightedLieDegreeLengthSpan v w s r ≤ η.ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, hk, rfl⟩
  change η (lieTreeEval v a) = 0
  by_cases hd : lieTreeWeight w a = s
  · by_cases hr : a.length = r
    · exact hzero a hd hr
    · have hm := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inr ⟨hd.symm, by omega⟩), Submodule.mem_bot] at hm
      rw [hm, map_zero]
  · have hm := F.lieTreeEval_mem_length v w hv a
    rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hm
    rw [hm, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

def allocatedGridIntegerAxis : gridAxes → Σ j : Fin m, Fin (n j)
  | ⟨⟨_, Sum.inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, Sum.inr i⟩, _⟩ => ⟨j, i⟩

local notation "ig" => allocatedGridIntegerAxis B U b S

def allocatedActiveGrid (a : gridAxes) : Prop :=
  S.value ^ ((ig a).1.val + 1) < basisAxisScale (b (ig a).1) (ig a).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def fixedSpatialKernelOriginalForecastDensity (sample : Sample) : Domain → ℝ :=
  binaryDensity (fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1))
    (allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG

noncomputable def fixedSpatialKernelSliceOriginalForecastDensity (sample : Sample) : Domain → ℝ :=
  fixedSpatialKernelOriginalForecastDensity B U basis S e W L frame h0slice h1slice
    hB lowerP widthP sample

end Erdos3.VectorPolynomial

end

end OAI
end


