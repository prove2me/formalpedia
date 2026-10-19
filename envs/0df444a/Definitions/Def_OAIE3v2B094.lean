-- Prove2me | Definitions.Def_OAIE3v2B094
-- name    : OAIE3v2B094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:03.36698+00:00
-- url     : https://prove2.me/theorems/d9f92845-fbc9-4e7c-a263-7a9351d4b542
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 95 of 311
-- statement:
--   Definitions bundle 95 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B075` of this split.
--
--   Modules: `Dynamics/RationalHeightBudget.lean`, `Dynamics/RationalLieQuotientBudget.lean`, `Estimates/BoundedFreeWords.lean`, `Estimates/ControlledLinearSubspaceLift.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/RationalImageIntersections.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RealifiedReconstruction.lean`, `Geometry/ConjugationCoordinates.lean`, `Lattices/ConjugatedLatticeGrids.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/CanonicalRankCompatibility.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/RationalSpanCoordinates.lean`, `Linear/SpanKernelGenerators.lean`, `Nilpotent/BCHChartCutoffSmooth.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/RationalBCHProducts.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/ShiftedPolynomialIdeals.lean`, `Sampling/RealGridRationalLift.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B075

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalHeightBudget
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_rational_section_exp_height {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ) (hsurj : Function.Surjective A.mulVec)
    {H : ℕ} (hHpos : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ S : Matrix κ ι ℚ, A * S = 1 ∧ ∀ i j,
      ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 5) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section A hsurj hHpos hA
  refine ⟨S, hS, fun i j => ?_⟩
  have hbudget := rationalSolveHeight_le_budget (Fintype.card ι) H hp hdim hH
  constructor
  · exact (show ((S i j).num.natAbs : ℝ) ≤ rationalSolveHeight (Fintype.card ι) H from
      by exact_mod_cast (hSH i j).1).trans hbudget
  · exact (show ((S i j).den : ℝ) ≤ rationalSolveHeight (Fintype.card ι) H from
      by exact_mod_cast (hSH i j).2).trans hbudget

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeWordCoefficients_truncation (s : ℕ) (p : FreeAlgebra ℚ X) (w : FreeMonoid X) :
    freeWordCoefficients (freeTruncation s p) w =
      if w.length ≤ s then freeWordCoefficients p w else 0 := by
  classical
  apply freeAlgebra_linear_induction (fun p =>
    freeWordCoefficients (freeTruncation s p) w =
      if w.length ≤ s then freeWordCoefficients p w else 0)
  · simp
  · intro p q hp hq
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  · intro r p hp
    simp only [map_smul, Finsupp.smul_apply, hp]
    split_ifs <;> simp
  · intro v
    rw [freeTruncation_word]
    by_cases hv : v = w
    · subst v
      split_ifs <;> simp
    · split_ifs <;> simp [freeWordCoefficients_word, hv]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem freeLieTruncation_associativeExpansion (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieAssociativeExpansion (freeLieTruncation s p) =
      freeTruncation s (freeLieAssociativeExpansion p) := by
  rw [← wordPolynomialEmbedding_freeLieExpansion, freeLieTruncation_expansion,
    wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_freeLieExpansion]

theorem freeLieTruncation_support_length (s : ℕ) (p : FreeLieAlgebra ℚ X)
    {w : FreeSemigroup X} (hw : w ∈ (freeLieWordExpansion (freeLieTruncation s p)).coeff.support) :
    w.length ≤ s := by
  have h := Finsupp.mem_support_iff.mp hw
  rw [freeLieTruncation_expansion, wordTruncation_coeff] at h
  by_contra hlen
  exact h (if_neg hlen)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanKernelGenerators
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem exists_bounded_kernel_projection (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ P : Matrix κ κ ℚ,
      LinearMap.range P.mulVecLin = LinearMap.ker A.mulVecLin ∧
      ∀ i j, RationalHeightLE (P i j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, rows, _, hsurj, hker⟩ := exists_independent_defining_rows A
  let R := A.submatrix rows id
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section R hsurj hH
    (fun i j => hA (rows i) j)
  refine ⟨r, hr, 1 - S * R, (range_kernel_projection R S hS).trans hker, ?_⟩
  intro i j
  have hI : RationalHeightLE ((1 : Matrix κ κ ℚ) i j) 1 := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
    · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  have hprod := rationalHeightLE_matrix_mul S R hSH (fun i j => hA (rows i) j) i j
  have hout := hI.sub hprod
  simpa only [Matrix.sub_apply, Fintype.card_fin, rationalKernelHeight, mul_one,
    mul_assoc] using hout

omit [DecidableEq ι] in

theorem exists_bounded_rational_kernel_family (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ v : Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)) → (κ → ℚ),
        LinearIndependent ℚ v ∧ Submodule.span ℚ (Set.range v) = LinearMap.ker A.mulVecLin ∧
        ∀ i j, RationalHeightLE (v i j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, P, hP, hPH⟩ := exists_bounded_kernel_projection A hH hA
  have hspan : Submodule.span ℚ (Set.range P.col) = LinearMap.ker A.mulVecLin := by
    rw [← Matrix.range_mulVecLin, hP]
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range P.col)
  rw [hspan] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨r, hr, v, hli, hvspan, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := hv i
  rw [← hk]
  exact hPH j k

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype κ]

section Rational

variable {V W ι η κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype κ] [Fintype η]

theorem exists_bounded_span_kernel_generators (e : Basis ι ℚ V) (f : Basis η ℚ W)
    (P : V →ₗ[ℚ] W) (v : κ → V) {H B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H)
    (hPv : ∀ i j, RationalHeightLE (f.repr (P (v i)) j) B) :
    ∃ r : ℕ, r ≤ Fintype.card η ∧ ∃ z : κ → V,
      Submodule.span ℚ (Set.range z) = Submodule.span ℚ (Set.range v) ⊓ LinearMap.ker P ∧
      ∀ i j, RationalHeightLE (e.repr (z i) j)
        ((Fintype.card κ + 1) * (rationalKernelHeight r B * H) ^ Fintype.card κ) := by
  classical
  let A : Matrix η κ ℚ := fun i j => f.repr (P (v j)) i
  obtain ⟨r, hr, Q, hQ, hQH⟩ := exists_bounded_kernel_projection A hB (fun i j => hPv j i)
  refine ⟨r, hr, fun i => finiteCombination v (Q.col i), ?_, ?_⟩
  · rw [← finiteCombination_kernel_image v P, ← finiteCombination_constraint_kernel f P v,
      ← hQ, Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro i j
    exact linearMap_coordinate_height (Pi.basisFun ℚ κ) e (finiteCombination v)
      (by intro a b; rw [finiteCombination_basis]; exact hv a b)
      (Q.col i) (fun a => hQH a i) j

end Rational
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem exists_bounded_image_equations (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, Function.Surjective D.mulVec ∧
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧
        ∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H) := by
  obtain ⟨t, ht, v, hli, hspan, hv⟩ := exists_bounded_rational_kernel_family Aᵀ hH
    (fun i j => hA j i)
  have hD := kernel_equations_of_transpose_kernel A v hli hspan
  refine ⟨t, ht, Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin), ?_, v, hD.1, hD.2, hv⟩
  simpa only [Module.finrank_pi] using (LinearMap.ker Aᵀ.mulVecLin).finrank_le

theorem exists_bounded_quotient_presentation (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H)) := by
  obtain ⟨t, ht, d, hd, D, hsurj, hker, hD⟩ := exists_bounded_image_equations A hH hA
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section D hsurj
    (rationalKernelHeight_pos t hH) hD
  exact ⟨t, ht, d, hd, D, S, hker, hS, hD, by simpa only [Fintype.card_fin] using hSH⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem map_lieBCHList (φ : L →ₗ⁅ℚ⁆ M) (s : ℕ) (f : X → L) (xs : List X) :
    φ (lieBCHList s f xs) = lieBCHList s (fun x => φ (f x)) xs := by
  induction xs with
  | nil => exact map_zero φ
  | cons x xs ih => simp only [lieBCHList, map_lieBCH, ih]

theorem lieBCHList_group_prod (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) :
    ((xs.map (fun x => (⟨f x⟩ : NilpotentLieBCHGroup L s hnil))).prod).coord =
      lieBCHList s f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, NilpotentLieBCHGroup.coord_mul, lieBCHList, ih]

noncomputable def bchProductLiePolynomial (s : ℕ) (xs : List X) : FreeLieAlgebra ℚ X :=
  freeLieTruncation s (lieBCHList s (FreeLieAlgebra.of ℚ) xs)

theorem bchProductLiePolynomial_eval (s : ℕ)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (f : X → L) (xs : List X) :
    FreeLieAlgebra.lift ℚ f (bchProductLiePolynomial s xs) = lieBCHList s f xs := by
  rw [bchProductLiePolynomial, lift_freeLieTruncation f hnil, map_lieBCHList]
  congr 1
  funext x
  exact FreeLieAlgebra.lift_of_apply _ _

theorem bchProductLiePolynomial_support_length (s : ℕ) (xs : List X)
    {w : FreeSemigroup X} (hw : w ∈ (freeLieWordExpansion (bchProductLiePolynomial s xs)).coeff.support) :
    w.length ≤ s := freeLieTruncation_support_length s _ hw

end Erdos3

end

section

namespace Erdos3

variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

namespace NilpotentAlgebraFiltration

variable {s : ℕ} (F : NilpotentAlgebraFiltration A s) (f : X → A)

theorem lieBCHList_mem (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    lieBCHList s f xs ∈ F.layer 1 := by
  induction xs with
  | nil => exact (F.layer 1).zero_mem
  | cons x xs ih =>
    rw [lieBCHList, F.lieBCH_eq (hf x) ih]
    exact F.bch_mem le_rfl (hf x) ih

theorem exp_lieBCHList (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    IsNilpotent.exp (lieBCHList s f xs) = (xs.map (fun x => IsNilpotent.exp (f x))).prod := by
  induction xs with
  | nil => exact IsNilpotent.exp_zero
  | cons x xs ih =>
    rw [lieBCHList, F.lieBCH_eq (hf x) (F.lieBCHList_mem f hf xs),
      exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hf x) (F.lieBCHList_mem f hf xs),
      ih, List.map_cons, List.prod_cons]

theorem bchProductPolynomial_formula (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    FreeAlgebra.lift ℚ f (bchProductPolynomial s xs) = lieBCHList s f xs := by
  have hx := F.lieBCHList_mem f hf xs
  have hn := F.isNilpotent_of_mem le_rfl hx
  have hprod : (xs.map (fun x => finiteExp (s + 1) (f x))).prod =
      IsNilpotent.exp (lieBCHList s f xs) := by
    rw [F.exp_lieBCHList f hf xs]
    congr 1
    apply List.map_congr_left
    intro x _
    exact finiteExp_eq_exp (F.pow_eq_zero le_rfl (hf x))
  rw [bchProductPolynomial_eval, hprod,
    finiteLog_eq_log (F.pow_eq_zero le_rfl (F.exp_sub_one_mem_layer hx hn)),
    nilpotentLog_exp_sub_one hn]

end NilpotentAlgebraFiltration

theorem bchProductLiePolynomial_associativeExpansion (s : ℕ) (xs : List X) :
    freeLieAssociativeExpansion (bchProductLiePolynomial s xs) =
      freeTruncation s (bchProductPolynomial s xs) := by
  rw [bchProductLiePolynomial, freeLieTruncation_associativeExpansion]
  apply freeTruncation_eq_of_scaled_series_eq
  rw [← scaledFreeLieEval_eq, map_lieBCHList]
  have hf : (fun x : X => scaledFreeLieEval s (FreeLieAlgebra.of ℚ x)) = scaledFreeGenerator s := by
    funext x
    exact scaledFreeLieEval_of s x
  rw [hf]
  have h := (truncatedSeriesFiltration (A := FreeAlgebra ℚ X) s).bchProductPolynomial_formula
    (scaledFreeGenerator s) (scaledFreeGenerator_mem_layer s) xs
  rw [← h]
  have he : FreeAlgebra.lift ℚ (scaledFreeGenerator (X := X) s) =
      (truncatedSeriesMk s).comp freeScaleSeries := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [scaledFreeGenerator]
  rw [he]
  rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {X : Type*}

noncomputable def bchProductWordCoefficients (s : ℕ) (xs : List X) : FreeSemigroup X →₀ ℚ :=
  (freeLieWordExpansion (bchProductLiePolynomial s xs)).coeff

noncomputable def bchProductBracketSupport (s : ℕ) (xs : List X) : Finset (FreeSemigroup X) :=
  (bchProductWordCoefficients s xs).support

noncomputable def bchProductBracketCoefficient (s : ℕ) (xs : List X) (w : FreeSemigroup X) : ℚ :=
  bchProductWordCoefficients s xs w / w.length

theorem bchProductBracketSupport_length (s : ℕ) (xs : List X) {w : FreeSemigroup X}
    (hw : w ∈ bchProductBracketSupport s xs) : w.length ≤ s :=
  bchProductLiePolynomial_support_length s xs hw

theorem bchProductWordCoefficients_eq (s : ℕ) (xs : List X) (w : FreeSemigroup X) :
    bchProductWordCoefficients s xs w =
      if w.length ≤ s then freeWordCoefficients (bchProductPolynomial s xs) w.toFreeMonoid else 0 := by
  rw [bchProductWordCoefficients, ← freeWordCoefficients_embedding,
    wordPolynomialEmbedding_freeLieExpansion, bchProductLiePolynomial_associativeExpansion,
    freeWordCoefficients_truncation, freeSemigroup_toFreeMonoid_length]

theorem lieBCHList_bracket_formula {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (f : X → L) (xs : List X) :
    lieBCHList s f xs = ∑ w ∈ bchProductBracketSupport s xs,
      bchProductBracketCoefficient s xs w • dynkinWord f w := by
  rw [← bchProductLiePolynomial_eval s hnil f xs, ← dynkinProjection_lift]
  change (bchProductWordCoefficients s xs).sum
    (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) = _
  simp only [Finsupp.sum, bchProductBracketSupport, bchProductBracketCoefficient,
    smul_smul, div_eq_mul_inv]

variable {ι : Type*} [Fintype ι]

noncomputable def bchProductCoordinatePolynomial (c : ι → ι → ι → ℚ) (s : ℕ)
    (xs : List X) (k : ι) : MvPolynomial (X × ι) ℚ :=
  ∑ w ∈ bchProductBracketSupport s xs,
    C (bchProductBracketCoefficient s xs w) * dynkinCoordinatePolynomial c w k

theorem bchProductCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ) (s : ℕ)
    (xs : List X) (k : ι) :
    (bchProductCoordinatePolynomial c s xs k).totalDegree ≤ s := by
  apply totalDegree_finsetSum_le
  intro w hw
  have h := totalDegree_mul (C (bchProductBracketCoefficient s xs w)) (dynkinCoordinatePolynomial c w k)
  rw [totalDegree_C, zero_add] at h
  exact h.trans ((dynkinCoordinatePolynomial_totalDegree c w k).trans
    (bchProductBracketSupport_length s xs hw))

theorem bchProductCoordinatePolynomial_support_card [Fintype X]
    (c : ι → ι → ι → ℚ) (s : ℕ) (xs : List X) (k : ι) :
    (bchProductCoordinatePolynomial c s xs k).support.card ≤
      (s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s := by
  simpa only [Fintype.card_prod] using polynomial_support_card_le
    (bchProductCoordinatePolynomial c s xs k) (bchProductCoordinatePolynomial_totalDegree c s xs k)

theorem bchProductCoordinatePolynomial_eval {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (bchProductCoordinatePolynomial (lieStructureConstants e) s xs k) =
        e.repr (lieBCHList s f xs) k := by
  rw [lieBCHList_bracket_formula s hnil]
  simp only [bchProductCoordinatePolynomial, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, dynkinCoordinatePolynomial_eval,
    map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem bchProductCoordinatePolynomial_eval_over {R L : Type*} [CommRing R] [Algebra ℚ R]
    [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (bchProductCoordinatePolynomial c s xs k) = e.repr (lieBCHList s f xs) k := by
  change _ = e.coord k (lieBCHList s f xs)
  rw [lieBCHList_bracket_formula s hnil]
  simp only [bchProductCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L]

theorem exists_bounded_lie_quotient_coordinates {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (I : LieIdeal ℚ L) (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H) :
    ∃ t : ℕ, t ≤ Fintype.card η ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H)) := by
  classical
  let A : Matrix ι η ℚ := fun i j => e.repr (v j) i
  obtain ⟨t, ht, d, hd, D, S, hker, hDS, hD, hS⟩ := exists_bounded_quotient_presentation A hHpos hv
  have hker' : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap :=
    hker.trans (coordinate_span_matrix_range e v I.toSubmodule hspan)
  have hsurj : Function.Surjective D.mulVec := by
    intro y
    refine ⟨S *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]
  exact ⟨t, ht, d, hd, lieQuotientCoordinateBasis e I D hker' hsurj, D, S,
    lieQuotientCoordinateBasis_matrix e I D hker' hsurj, hDS, hD, hS⟩

theorem exists_bounded_lie_quotient_with_structure {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (I : LieIdeal ℚ L) (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∃ t : ℕ, t ≤ Fintype.card η ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        (∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H))) ∧
        ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
          (rationalLieStructureHeight (Fintype.card ι)
            (max H (max (rationalKernelHeight t H) (rationalSolveHeight d (rationalKernelHeight t H))))) := by
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS⟩ :=
    exists_bounded_lie_quotient_coordinates e I v hspan hHpos hv
  refine ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS, ?_⟩
  intro i j k
  rw [lieStructureConstants_quotient_matrix e b (lieQuotientMap I) S
    (by rw [hmatrix]; exact hDS), hmatrix]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hD u v).mono ((le_max_left _ _).trans (le_max_right _ _)))
    (fun u v => (hS u v).mono ((le_max_right _ _).trans (le_max_right _ _))) i j k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalLieQuotientBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι η L : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [LieRing L] [LieAlgebra ℚ L]

theorem exists_lie_quotient_basis_exp_height (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (v : η → L) (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule)
    {H : ℕ} (hHpos : 1 ≤ H) (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hm : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ b : Basis (Fin d) ℚ (L ⧸ I),
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45)) ∧
        ∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 51) ∧
          ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 51) := by
  classical
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS, hbracket⟩ :=
    exists_bounded_lie_quotient_with_structure e I v hspan hHpos hv hc
  have htp : (t : ℝ) ≤ p := (Nat.cast_le.mpr ht).trans hm
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hd).trans hn
  have hK := rationalKernelHeight_le_budget t H hp htp hH
  have hJ := rationalQuotientSectionHeight_le_exp t d H hp htp hdp hH
  have hC := rationalLieQuotientStructureHeight_le_exp (Fintype.card ι) t d H hp hn htp hdp hH
  refine ⟨d, hd, b, D, S, hmatrix, hDS, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hD i j).1).trans hK, (Nat.cast_le.mpr (hD i j).2).trans hK⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hS i j).1).trans hJ, (Nat.cast_le.mpr (hS i j).2).trans hJ⟩
  · intro i j k
    exact ⟨(Nat.cast_le.mpr (hbracket i j k).1).trans hC,
      (Nat.cast_le.mpr (hbracket i j k).2).trans hC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFreeWords
namespace OAI

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem bchProductBracketSupport_card_le (s : ℕ) (xs : List X) :
    (bchProductBracketSupport s xs).card ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  classical
  let t := (bchProductBracketSupport s xs).image FreeSemigroup.toFreeMonoid
  have h := freeWordSet_card_le t s (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [freeSemigroup_toFreeMonoid_length] using bchProductBracketSupport_length s xs hv)
  simpa only [t, Finset.card_image_of_injective _ FreeSemigroup.toFreeMonoid_injective] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include hnil

namespace NilpotentLieBCHGroup

theorem additive_remainder_mem (I : LieIdeal ℚ L) (r w : L) (hrw : ⁅r, w⁆ ∈ I) :
    (((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹).coord) ∈ I := by
  have hsum : quotientHom I (⟨r + w⟩ : NilpotentLieBCHGroup L s hnil) =
      quotientHom I (⟨r⟩ : NilpotentLieBCHGroup L s hnil) * quotientHom I (⟨w⟩ : NilpotentLieBCHGroup L s hnil) := by
    apply ext
    change lieQuotientMap I (r + w) = lieBCH s (lieQuotientMap I r) (lieQuotientMap I w)
    rw [map_add]
    apply (lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) ?_).symm
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hrw
  apply (lieQuotientMap_eq_zero I _).mp
  have h : quotientHom I
      ((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hsum]
    simp only [inv_mul_cancel_left, mul_inv_cancel]
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in

theorem bchSubgroupCoordinates_comap (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_bch (w : σ → ℕ) {p q : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) (hq : F.Adapted w q) : F.Adapted w (lieBCH s p q) := by
  apply (F.mem_adaptedSubmodule w _).mp
  exact lieBCH_mem (F.adaptedLieSubalgebra w) s
    ((F.mem_adaptedSubmodule w _).mpr hp) ((F.mem_adaptedSubmodule w _).mpr hq)

theorem adapted_degreeLE (w : σ → ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) : DegreeLE w s p := by
  intro α hα
  have h := F.antitone hα ((F.adapted_iff_coefficients w p).mp hp α)
  simpa only [F.terminal, Submodule.mem_bot] using h

end Erdos3.NilpotentLieFiltration


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

variable {F}

theorem PolynomialOrbit.degreeLE {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    DegreeLE w s p.log := F.adapted_degreeLE w p.adapted

end Erdos3.NilpotentLieFiltration


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem real_span_rational_family (P : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = P) :
    Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) = P.baseChange ℝ := by
  rw [← hspan, Submodule.baseChange_span, ← Set.range_comp]
  rfl

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_span_family_coordinates (e : Basis ι ℚ L) (v : κ → L) :
    (Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j)))).map
        (e.baseChange ℝ).equivFun.toLinearMap =
      Submodule.span ℝ (Set.range (fun j i => (e.repr (v j) i : ℝ))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j i
  exact rationalLieInclusion_coordinates e (v j) i

theorem real_span_family_mem_iff_coordinates (e : Basis ι ℚ L) (v : κ → L)
    (x : ℝ ⊗[ℚ] L) :
    x ∈ Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) ↔
      (e.baseChange ℝ).equivFun x ∈
        Submodule.span ℝ (Set.range (fun j i => (e.repr (v j) i : ℝ))) := by
  rw [← real_span_family_coordinates e v, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def coordinateBox (e : Basis ι ℝ L) (B : ℝ) : Set (NilpotentLieBCHGroup L s hnil) :=
  {g | ∀ i, |e.repr g.coord i| ≤ B}

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)

theorem homCoordinates_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    homCoordinates e f φ (rightTranslate e g v) =
      rightTranslate f (φ g) (homCoordinates e f φ v) := by
  simp only [homCoordinates, rightTranslate, Homeomorph.symm_apply_apply, map_mul]

theorem basisHomeomorph_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    basisHomeomorph e (g ^ n) = n • basisHomeomorph e g := by
  change e.equivFun (g ^ n).coord = n • e.equivFun g.coord
  rw [coord_pow, map_nsmul]

theorem homCoordinates_nsmul (n : ℕ) (v : ι → ℝ) :
    homCoordinates e f φ (n • v) = n • homCoordinates e f φ v := by
  have he : (basisHomeomorph (hnil := hnil) e).symm (n • v) =
      ((basisHomeomorph e).symm v) ^ n := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_pow]
  simp only [homCoordinates, he, map_pow, basisHomeomorph_pow]

theorem homCoordinates_natCast_smul (n : ℕ) (v : ι → ℝ) :
    homCoordinates e f φ ((n : ℝ) • v) = (n : ℝ) • homCoordinates e f φ v := by
  simpa only [Nat.cast_smul_eq_nsmul] using homCoordinates_nsmul e f φ n v

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotientMetricSpace_lipschitz_mk (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith 1 (QuotientGroup.mk : NilpotentLieBCHGroup L s hnil → _ ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact rightCosetMetricSpace_lipschitz_mk Γ hΓ

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem realificationMap_realificationHom
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hnil) :
    realificationMap (hnil := hnil) (hM := hM) φ (realificationHom g) =
      realificationHom (map (hM := hM) φ g) := by
  apply ext
  rfl

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Distance

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisQuotientDist (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (x y : _ ⧸ Γ) : ℝ :=
  letI := quotientMetricSpace e Γ hΓ
  dist x y

end Distance

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Quotient

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

theorem quotientMetricSpace_lipschitz_left (a : NilpotentLieBCHGroup L s hnil) {C : ℝ≥0}
    (hLip : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith C (fun x => a * x)) :
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith C (fun x : _ ⧸ Γ => a • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact lipschitz_quotient_left_smul Γ hΓ a hLip

end Quotient

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialIdeals
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem shiftedAdaptedSubmodule_antitone : Antitone (F.shiftedAdaptedSubmodule w) := by
  intro i j hij p hp α
  exact F.antitone (Nat.add_le_add_left hij _) (hp α)

theorem shiftedPolynomialIdeal_antitone : Antitone (F.shiftedPolynomialIdeal w) := by
  intro i j hij p hp
  exact F.shiftedAdaptedSubmodule_antitone w hij hp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_linear_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : M →ₗ[ℚ] L, Function.RightInverse σ φ ∧
      ∀ i j, RationalHeightLE (e.repr (σ (f j)) i) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section (LinearMap.toMatrix e f φ)
    (basisMatrix_surjective e f φ hφ) hH (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hentries i j)
  refine ⟨Matrix.toLin f e S, basisMatrix_section e f φ S hS, ?_⟩
  intro i j
  have heq := LinearMap.toMatrix_apply f e (Matrix.toLin f e S) i j
  rw [LinearMap.toMatrix_toLin] at heq
  rw [← heq]
  exact hSH i j

theorem exists_bounded_realified_linear_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : (ℝ ⊗[ℚ] M) →ₗ[ℝ] (ℝ ⊗[ℚ] L),
      Function.RightInverse σ (φ.baseChange ℝ) ∧
      ∀ i j, |(e.baseChange ℝ).repr (σ ((f.baseChange ℝ) j)) i| ≤
        (rationalSolveHeight (Fintype.card κ) H : ℝ) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f φ hφ hH hentries
  refine ⟨σ.baseChange ℝ, linearMap_baseChange_rightInverse φ σ hσ, ?_⟩
  intro i j
  rw [linearMap_baseChange_basis]
  exact (hσH i j).abs_real_le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem centralLieBasis_of_sorted_filtration {s : ℕ} (F : NilpotentLieFiltration L s)
    (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ) (hw : Monotone w)
    (hlayer : ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j})) :
    IsCentralLieBasis e := by
  intro j a
  have ha : a ∈ F.layer 1 := by simp [F.one_eq_top]
  have hj : e j ∈ F.layer (w j) := by
    rw [hlayer]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  have hbr := F.lie_mem ha hj
  rw [hlayer] at hbr
  rw [basisTail_eq_span]
  apply Submodule.span_mono (Set.image_mono ?_) hbr
  intro k hk
  change j.val + 1 ≤ k.val
  change 1 + w j ≤ w k at hk
  by_contra h
  have hkj : k ≤ j := by change k.val ≤ j.val; omega
  have hweight := hw hkj
  omega

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

include F

omit [FiniteDimensional ℚ L] in
theorem layer_eq_span_of_weighted_flag {d : ℕ} (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hbound : ∀ j, w j ≤ s + 1)
    (hlayer : ∀ i : Fin (s + 1),
      F.layer (i.val + 1) = Submodule.span ℚ (e '' {j | i.val < w j})) :
    ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j}) := by
  intro i
  cases i with
  | zero =>
      have hzero : F.layer 0 = ⊤ := by
        apply top_unique
        rw [← F.one_eq_top]
        exact F.antitone (by omega)
      simp only [hzero, Nat.zero_le, Set.ofPred_true, Set.image_univ, e.span_eq]
  | succ i =>
      by_cases hi : i < s + 1
      · simpa only [Nat.succ_le_iff] using hlayer ⟨i, hi⟩
      · have htail : F.layer (i + 1) = ⊥ := by
          apply bot_unique
          simpa only [F.terminal] using F.antitone (show s + 1 ≤ i + 1 by omega)
        have hempty : {j | i + 1 ≤ w j} = (∅ : Set (Fin d)) := by
          ext j
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          have := hbound j
          omega
        rw [htail, hempty, Set.image_empty, Submodule.span_empty]

theorem exists_sorted_adapted_basis :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧
      ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j}) := by
  let P : Fin (s + 1) → Submodule ℚ L := fun i => F.layer (i.val + 1)
  have hP : Antitone P := fun i j hij => F.antitone (Nat.add_le_add_right hij 1)
  obtain ⟨e, w, hw, hbound, hlayer⟩ := exists_sorted_weighted_flag_basis P hP
  exact ⟨e, w, hw, hbound, F.layer_eq_span_of_weighted_flag e w hbound hlayer⟩

theorem exists_central_basis :
    ∃ e : Basis (Fin (finrank ℚ L)) ℚ L, IsCentralLieBasis e := by
  obtain ⟨e, w, hw, _, hlayer⟩ := F.exists_sorted_adapted_basis
  exact ⟨e, centralLieBasis_of_sorted_filtration F e w hw hlayer⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_bounded_sorted_adapted_basis {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤) {H : ℕ}
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧ IsCentralLieBasis b ∧
      (∀ j k, RationalHeightLE (e.repr (b j) k) H) ∧
      ∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j}) := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let S : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let P : Fin (s + 1) → Submodule ℚ L := fun i => F.layer (i.val + 1)
  have hP : Antitone P := fun i j hij => F.antitone (Nat.add_le_add_right hij 1)
  have hSP (i : Fin (s + 1)) : Submodule.span ℚ (S ∩ (P i : Set L)) = P i :=
    span_inter_eq_of_spanning_family (P i) (v i) (hspan i) S (hv i)
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := F.one_eq_top.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hSP 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, hbound, hbS, hbP⟩ :=
    exists_sorted_flag_basis_from_spanning_set P hP S hS hSP
  have hlayer := F.layer_eq_span_of_weighted_flag b w hbound hbP
  exact ⟨b, w, hw, hbound, centralLieBasis_of_sorted_filtration F b w hw hlayer, hbS, hlayer⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem lie_basis_bracket_height (e : Basis ι ℚ L) {H K : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (v : L) (hv : ∀ j, RationalHeightLE (e.repr v j) K) (i k : ι) :
    RationalHeightLE (e.repr ⁅e i, v⁆ k)
      ((Fintype.card ι ^ 2 + 1) * (H * K) ^ (Fintype.card ι ^ 2)) := by
  classical
  rw [lie_coordinate_formula]
  have h := rationalHeightLE_sum
    (fun ab : ι × ι => lieStructureConstants e ab.1 ab.2 k * e.repr (e i) ab.1 * e.repr v ab.2)
    (fun ab => ((hc ab.1 ab.2 k).mul (basis_repr_height_one e i ab.1)).mul (hv ab.2))
  simpa only [Fintype.card_prod, ← pow_two, mul_one] using h

theorem exists_bounded_layer_spanning (e : Basis ι ℚ L) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) (n : ℕ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ v : Fin r → L,
      Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule ∧
      ∀ i j, RationalHeightLE (e.repr (v i) j) (lieCoordinateHeight (Fintype.card ι) H n) := by
  induction n with
  | zero =>
    apply exists_small_bounded_spanning_family e _ e
    · simp [e.span_eq]
    · intro i j
      exact (basis_repr_height_one e i j).mono (lieCoordinateHeight_pos _ _ _)
  | succ n ih =>
    obtain ⟨r, _, v, hvspan, hv⟩ := ih
    apply exists_small_bounded_spanning_family e _ (fun ij : ι × Fin r => ⁅e ij.1, v ij.2⁆)
    · exact span_basis_brackets_layer e v n hvspan
    · intro ij k
      exact (lie_basis_bracket_height e hc (v ij.2) (hv ij.2) ij.1 k).mono
        (lieCoordinateHeight_step _ _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K V W ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem basisBlockInvariant_ker (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0) :
    BasisBlockInvariant e c (LinearMap.ker T) := by
  intro a x hx
  change T (basisCoordinateProjection e {i | c i = a} x) = 0
  rw [basisBlockMap_commutes e f c d T hT a x, show T x = 0 from hx, map_zero]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_bounded_block_image_section {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S * A = A ∧
      (∀ i j, c i ≠ r j → S i j = 0) ∧
      ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  refine ⟨matrixBlockPart c r S, matrixBlockPart_image_section r c A S hblock hS,
    matrixBlockPart_off_block c r S, ?_⟩
  intro i j
  by_cases h : c i = r j
  · simpa only [matrixBlockPart, h, ↓reduceIte] using hSH i j
  · simpa only [matrixBlockPart, h, ↓reduceIte] using
      rationalHeightLE_zero (rationalKernelHeight_pos (Fintype.card ι) hH)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_real_block_span_defining_matrix {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H)) ∧
      (∀ i j, r i ≠ r j → Q i j = 0) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section r c A hblock hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hSr := real_matrix_image_section A S hS
  have hQr : Matrix.of (fun i j => (Q i j : ℝ)) =
      1 - Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hprod
  · intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg r h)
    have hprod : (A * S) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : r i = c k
      · exact (congrArg (fun x : ℚ => A i k * x)
          (hSb k j (fun hkj => hij (hik.trans hkj)))).trans (mul_zero _)
      · exact (congrArg (fun x : ℚ => x * S k j) (hblock i k hik)).trans (zero_mul _)
    simp only [Q, Matrix.sub_apply, Matrix.one_apply, hne, ↓reduceIte, hprod, sub_self]
  · ext x
    change Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ↔
      ∃ y, Matrix.of (fun i j => (A i j : ℝ)) *ᵥ y = x
    rw [hQr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨(fun i j => (S i j : ℝ)) *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ConjugationCoordinates
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem conjugationInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    conjugationInput a b ∈ denominatorGrid q := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  refine ⟨fun ji => ![za ji.2, zb ji.2, -za ji.2] ji.1, ?_⟩
  rintro ⟨j, i⟩
  have hai : (q : ℚ) * a i = (za i : ℚ) := hza i
  have hbi : (q : ℚ) * b i = (zb i : ℚ) := hzb i
  fin_cases j <;> simp [conjugationInput, Pi.smul_apply, smul_eq_mul, hai, hbi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def conjugationCoordinatePolynomial (e : Basis ι ℚ L) (s : ℕ) (i : ι) :
    MvPolynomial (Fin 3 × ι) ℚ :=
  bchProductCoordinatePolynomial (lieStructureConstants e) s [0, 1, 2] i

theorem conjugationCoordinatePolynomial_degree (e : Basis ι ℚ L) (s : ℕ) (i : ι) :
    (conjugationCoordinatePolynomial e s i).totalDegree ≤ s :=
  bchProductCoordinatePolynomial_totalDegree _ _ _ _

theorem conjugationCoordinatePolynomial_eval (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (z g : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (conjugationInput (e.equivFun z.coord) (e.equivFun g.coord))
      (conjugationCoordinatePolynomial e s i) = e.repr (z * g * z⁻¹).coord i := by
  let f : Fin 3 → NilpotentLieBCHGroup L s hnil := ![z, g, z⁻¹]
  have he := bchProductCoordinatePolynomial_eval e s hnil (fun j => (f j).coord) [0, 1, 2] i
  have hp := lieBCHList_group_prod s hnil (fun j => (f j).coord) [0, 1, 2]
  rw [← hp] at he
  have hmap : ([0, 1, 2].map (fun j => (⟨(f j).coord⟩ : NilpotentLieBCHGroup L s hnil))) =
      [z, g, z⁻¹] := by simp [f]; rfl
  rw [hmap] at he
  simp only [List.prod_cons, List.prod_nil, mul_one] at he
  have hi : (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2) =
      conjugationInput (e.equivFun z.coord) (e.equivFun g.coord) := by
    funext ⟨j, k⟩
    fin_cases j <;> simp [f, conjugationInput]
  change eval (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2)
    (conjugationCoordinatePolynomial e s i) = _ at he
  rw [hi] at he
  simpa only [mul_assoc] using he

theorem conjugationCoordinatePolynomial_zero (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (z : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (conjugationInput (e.equivFun z.coord) 0) (conjugationCoordinatePolynomial e s i) = 0 := by
  simpa using conjugationCoordinatePolynomial_eval e hnil z 1 i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConjugatedLatticeGrids
namespace OAI

section

namespace Erdos3

open Module

theorem denominatorGrid_neg {ι : Type*} (q : ℕ) {x : ι → ℚ}
    (hx : x ∈ denominatorGrid q) : -x ∈ denominatorGrid q := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, ?_⟩
  intro i
  have hi : (q : ℚ) * x i = (z i : ℚ) := hz i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Int.cast_neg, mul_neg, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealGridRationalLift
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_grid_exists_rationalLieInclusion (e : Basis ι ℚ L) (l : ℕ) (hl : 0 < l)
    (x : ℝ ⊗[ℚ] L) (hx : (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    ∃ a : L, e.equivFun a ∈ denominatorGrid l ∧ rationalLieInclusion a = x := by
  obtain ⟨y, hy, heq⟩ := realDenominatorGrid_exists_rational l hl _ hx
  refine ⟨e.equivFun.symm y, ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hy
  · apply (e.baseChange ℝ).equivFun.injective
    funext i
    calc
      _ = (e.equivFun (e.equivFun.symm y) i : ℝ) :=
        rationalLieInclusion_coordinates e (e.equivFun.symm y) i
      _ = (y i : ℝ) := by rw [LinearEquiv.apply_symm_apply]
      _ = _ := congrFun heq i

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_grid_iff (e : Basis ι ℚ L) (l : ℕ) (hl : 0 < l)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l ↔
      ∃ a : NilpotentLieBCHGroup L s hnil,
        e.equivFun a.coord ∈ denominatorGrid l ∧ realificationHom a = g := by
  constructor
  · intro hg
    obtain ⟨a, ha, heq⟩ := real_grid_exists_rationalLieInclusion e l hl g.coord hg
    exact ⟨⟨a⟩, ha, ext heq⟩
  · rintro ⟨a, ha, rfl⟩
    rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
    exact ha

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_grid_mul (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hmul : ∀ a b : NilpotentLieBCHGroup L s hnil,
      e.equivFun a.coord ∈ denominatorGrid l → e.equivFun b.coord ∈ denominatorGrid l →
      e.equivFun (a * b).coord ∈ denominatorGrid m)
    (a b : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (ha : (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l)
    (hb : (e.baseChange ℝ).equivFun b.coord ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (a * b).coord ∈ realDenominatorGrid m := by
  obtain ⟨aq, haq, heqa⟩ := (realification_grid_iff (hnil := hnil) e l hl a).mp ha
  obtain ⟨bq, hbq, heqb⟩ := (realification_grid_iff (hnil := hnil) e l hl b).mp hb
  rw [← heqa, ← heqb, ← map_mul, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  exact hmul aq bq haq hbq

theorem realification_grid_inv (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hinv : ∀ a : NilpotentLieBCHGroup L s hnil,
      e.equivFun a.coord ∈ denominatorGrid l → e.equivFun (a⁻¹).coord ∈ denominatorGrid m)
    (a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (ha : (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (a⁻¹).coord ∈ realDenominatorGrid m := by
  obtain ⟨aq, haq, heqa⟩ := (realification_grid_iff (hnil := hnil) e l hl a).mp ha
  rw [← heqa, ← map_inv, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  exact hinv aq haq

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_block_subspace_defining_matrix
    {ι κ δ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j)
        (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H)) ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ x : ℝ ⊗[ℚ] L,
        (fun i j => (Q i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x = 0 ↔ x ∈ U.baseChange ℝ := by
  classical
  let v' := blockSpanningFamily b c v
  let A : Matrix ι (ι × κ) ℚ := fun i z => b.repr (v' z) i
  have hA : ∀ i z, RationalHeightLE (A i z) H :=
    fun i z => blockSpanningFamily_height b c v hH hv z i
  have hAb : ∀ i z, c i ≠ c z.1 → A i z = 0 := by
    intro i z hz
    change b.repr (blockSpanningFamily b c v z) i = 0
    rw [blockSpanningFamily_repr, if_neg hz]
  obtain ⟨Q, hQ, hQb, hker⟩ := exists_real_block_span_defining_matrix c (fun z : ι × κ => c z.1) A hAb hH hA
  refine ⟨Q, ?_, hQb, ?_⟩
  · simpa only [Fintype.card_prod] using hQ
  · intro x
    have hsp := blockSpanningFamily_span b c U v hspan hU
    rw [← real_span_rational_family U v' hsp, real_span_family_mem_iff_coordinates b v' x,
      real_column_span_mem_iff A]
    change (b.baseChange ℝ).equivFun x ∈ LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) ↔ _
    rw [hker]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalRankCompatibility
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem eq_of_layer_eq {F G : NilpotentLieFiltration L s} (h : F.layer = G.layer) : F = G := by
  cases F
  cases G
  cases h
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem differenceInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    differenceInput a b ∈ denominatorGrid q := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  refine ⟨fun ji => ![-za ji.2, zb ji.2, 0] ji.1, ?_⟩
  rintro ⟨j, i⟩
  have hai : (q : ℚ) * a i = (za i : ℚ) := hza i
  have hbi : (q : ℚ) * b i = (zb i : ℚ) := hzb i
  fin_cases j <;> simp [differenceInput, Pi.smul_apply, smul_eq_mul, hai, hbi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem differenceCoordinate_eval (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a b : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (differenceInput (e.equivFun a.coord) (e.equivFun b.coord))
      (conjugationCoordinatePolynomial e s i) = e.repr (a⁻¹ * b).coord i := by
  let f : Fin 3 → NilpotentLieBCHGroup L s hnil := ![a⁻¹, b, 1]
  have he := bchProductCoordinatePolynomial_eval e s hnil (fun j => (f j).coord) [0, 1, 2] i
  have hp := lieBCHList_group_prod s hnil (fun j => (f j).coord) [0, 1, 2]
  rw [← hp] at he
  have hmap : ([0, 1, 2].map (fun j => (⟨(f j).coord⟩ : NilpotentLieBCHGroup L s hnil))) =
      [a⁻¹, b, 1] := by simp [f]; exact ⟨rfl, rfl⟩
  rw [hmap] at he
  simp only [List.prod_cons, List.prod_nil, mul_one] at he
  have hi : (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2) =
      differenceInput (e.equivFun a.coord) (e.equivFun b.coord) := by
    funext ⟨j, k⟩
    fin_cases j <;> simp [f, differenceInput]
  change eval (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2)
    (conjugationCoordinatePolynomial e s i) = _ at he
  rwa [hi] at he

theorem differenceCoordinate_same (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (differenceInput (e.equivFun a.coord) (e.equivFun a.coord))
      (conjugationCoordinatePolynomial e s i) = 0 := by
  simpa using differenceCoordinate_eval e hnil a a i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def affineRecoveryLogLoss (P : ℝ) (n : ℕ) : ℝ :=
  quarticBogolyubovProgressionConstant * (roundedModelLogBudget P n + 1) ^ 8 +
    (P + 13 * n) + 16 * ((n : ℝ) + 3)

end Erdos3

end

end OAI
end


