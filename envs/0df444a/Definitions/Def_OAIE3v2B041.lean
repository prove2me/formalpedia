-- Prove2me | Definitions.Def_OAIE3v2B041
-- name    : OAIE3v2B041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:00.190265+00:00
-- url     : https://prove2.me/theorems/502107da-eeb0-4287-ab59-e7b249f41a27
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 42 of 311
-- statement:
--   Definitions bundle 42 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B013` of this split.
--
--   Modules: `Estimates/FastCoefficientBlocks.lean`, `Estimates/MinkowskiSecondInduction.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/PrimitiveExtension.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/SquareRationalModel.lean`, `FixedDensity/GeneratorCells.lean`, `Fourier/ExponentialBohrVolume.lean`, `Fourier/QuarticBohrProgression.lean`, `Geometry/CyclicProgressionCoordinates.lean`, `Geometry/MinkowskiSecondBox.lean`, `Geometry/MinkowskiSecondBoxGlue.lean`, `Lattices/ReducedLatticeBasis.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/MinkowskiSecondBoxBasis.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/ShortGeneratingBasisBound.lean`, `Nilpotent/CurrentBracketInductionStep.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

noncomputable def siteEvaluation {ι : Type*} (x : ι → σ → R) :
    VectorPolynomial σ R W →ₗ[R] (ι → W) := LinearMap.pi (fun i => eval (x i))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem realification_comap (P : Submodule ℚ W) (f : V →ₗ[ℚ] W) :
    (P.comap f).baseChange ℝ = (P.baseChange ℝ).comap (f.baseChange ℝ) := by
  have he : P.comap f = LinearMap.ker (P.mkQ.comp f) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [he, realification_ker, LinearMap.baseChange_comp, LinearMap.ker_comp,
    ← realification_ker, Submodule.ker_mkQ]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (P Q : Submodule ℚ E)

noncomputable def realSubquotientProjection : P.baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] (P ⧸ Q.comap P.subtype)) :=
  ((Q.comap P.subtype).mkQ.baseChange ℝ).comp (realificationSubmoduleEquiv P).symm.toLinearMap

theorem realSubquotientProjection_surjective : Function.Surjective (realSubquotientProjection P Q) := by
  have hq : Function.Surjective ((Q.comap P.subtype).mkQ.baseChange ℝ) :=
    LinearMap.lTensor_surjective ℝ (Q.comap P.subtype).mkQ_surjective
  exact hq.comp (realificationSubmoduleEquiv P).symm.surjective

theorem realSubquotientProjection_ker :
    LinearMap.ker (realSubquotientProjection P Q) =
      (Q.baseChange ℝ).comap (P.baseChange ℝ).subtype := by
  ext x
  change (Q.comap P.subtype).mkQ.baseChange ℝ ((realificationSubmoduleEquiv P).symm x) = 0 ↔
    x.val ∈ Q.baseChange ℝ
  rw [realification_mkQ_eq_zero_iff, realification_comap]
  change P.subtype.baseChange ℝ ((realificationSubmoduleEquiv P).symm x) ∈ Q.baseChange ℝ ↔ _
  have he := congrArg Subtype.val ((realificationSubmoduleEquiv P).apply_symm_apply x)
  rw [← realificationSubmoduleEquiv_coe, he]

noncomputable def realSubquotientEquiv :
    (ℝ ⊗[ℚ] (P ⧸ Q.comap P.subtype)) ≃ₗ[ℝ]
      RealSubquotient P Q :=
  (realSubquotientProjection P Q).quotKerEquivOfSurjective (realSubquotientProjection_surjective P Q) |>.symm |>.trans
    (Submodule.quotEquivOfEq _ _ (realSubquotientProjection_ker P Q))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_mem_span (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S x ∈ Submodule.span K (b '' S) := by
  classical
  apply (basis_mem_span_image_iff b S _).mpr
  intro i hi
  simp only [basisCoordinateProjection_repr, hi, ↓reduceIte]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrimitiveExtension
namespace OAI


namespace Erdos3.BohrLattice.Primitive

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem IsPrimitive.ne_zero {z : ι → ℤ} (hz : IsPrimitive z) : z ≠ 0 := by
  rintro rfl
  simp [IsPrimitive] at hz

theorem isPrimitive_of_content_eq_one {z : ι → ℤ} (hz : content z = 1) :
    IsPrimitive z := by
  obtain ⟨u, hu⟩ := exists_bezout_finset Finset.univ z
  have hu' : ∑ i, u i * z i = content z := by
    simpa [content] using hu
  exact ⟨u, hu'.trans hz⟩

theorem divideContent_primitive {z : ι → ℤ} (hz : z ≠ 0) :
    IsPrimitive (divideContent z) := by
  apply isPrimitive_of_content_eq_one
  rw [content]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

theorem divideContent_ne_zero {z : ι → ℤ} (hz : z ≠ 0) :
    divideContent z ≠ 0 := (divideContent_primitive hz).ne_zero

end Erdos3.BohrLattice.Primitive


namespace Erdos3.BohrLattice.PrimitiveExtension

open scoped BigOperators
open Module

noncomputable section

theorem isPrimitive_of_minimal_gauge {n : ℕ} (z : Fin n → ℤ)
    (hz : z ≠ 0) (μ : (Fin n → ℤ) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ z ≤ μ x) :
    Erdos3.BohrLattice.Primitive.IsPrimitive z := by
  let c : ℤ := Erdos3.BohrLattice.Primitive.content z
  have hc0 : 0 ≤ c := by
    have hn := Finset.normalize_gcd (s := Finset.univ) (f := z)
    have habs : |c| = c := by
      rw [Int.abs_eq_normalize]
      exact hn
    rw [← habs]
    exact abs_nonneg c
  have hcne : c ≠ 0 := Erdos3.BohrLattice.Primitive.content_ne_zero hz
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  suffices hc : c = 1 by
    apply Erdos3.BohrLattice.Primitive.isPrimitive_of_content_eq_one
    exact hc
  by_contra hc
  have hc2 : (2 : ℤ) ≤ c := by omega
  let z' : Fin n → ℤ := Erdos3.BohrLattice.Primitive.divideContent z
  have hz' : z' ≠ 0 := Erdos3.BohrLattice.Primitive.divideContent_ne_zero hz
  have hz_eq : z = c • z' := by
    funext i
    exact (Erdos3.BohrLattice.Primitive.content_mul_divideContent z i).symm
  have hscale : μ z = (c : ℝ) * μ z' := by
    rw [hz_eq]
    exact hμhom c hcpos z'
  have hle : μ z ≤ μ z' := hmin z' hz'
  have hz'pos : 0 < μ z' := hμpos z' hz'
  have hc2r : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
  rw [hscale] at hle
  nlinarith

theorem exists_basis_zero_eq_of_isPrimitive {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ) (hz : Erdos3.BohrLattice.Primitive.IsPrimitive z) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b ⟨0, hn⟩ = z := by
  obtain ⟨u, hu⟩ := hz
  let f : (Fin n → ℤ) →ₗ[ℤ] ℤ := dotLinear u
  have hfz : f z = 1 := by
    simpa [f, dotLinear] using hu
  let K : Submodule ℤ (Fin n → ℤ) := LinearMap.ker f
  let kb := K.basisOfPid (Pi.basisFun ℤ (Fin n))
  let k : ℕ := kb.1
  let bK : Basis (Fin k) ℤ K := kb.2
  have hli : ∀ (c : ℤ), ∀ x ∈ K, c • z + x = 0 → c = 0 := by
    intro c x hx hzero
    have hx0 : f x = 0 := by
      exact (LinearMap.mem_ker.mp hx)
    have h : f (c • z + x) = f 0 := congr_arg f hzero
    rw [map_add, map_smul, hfz, hx0, map_zero] at h
    simpa using h
  have hsp : ∀ x : Fin n → ℤ, ∃ c : ℤ, x + c • z ∈ K := by
    intro x
    refine ⟨-f x, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [map_add, map_smul, hfz]
    simp
  let b' : Basis (Fin (k + 1)) ℤ (Fin n → ℤ) :=
    Basis.mkFinCons z bK hli hsp
  have hb'0 : b' 0 = z := by
    simp [b', Basis.coe_mkFinCons]
  have hkn : k + 1 = n := by
    have hc := Fintype.card_congr (b'.indexEquiv (Pi.basisFun ℤ (Fin n)))
    simpa using hc
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := b'.reindex (finCongr hkn)
  refine ⟨b, ?_⟩
  simp only [b, Basis.reindex_apply]
  have hzero : (finCongr hkn).symm ⟨0, hn⟩ = (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hzero, hb'0]

theorem shortest_zspan_vector_primitive_and_extends
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ E)
    (v : Submodule.span ℤ (Set.range b)) (hv : v ≠ 0)
    (μ : Submodule.span ℤ (Set.range b) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ v ≤ μ x) :
    Erdos3.BohrLattice.Primitive.IsPrimitive (zspanCoordEquiv b v) ∧
      ∃ B : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)),
        B ⟨0, hn⟩ = v := by
  let e := zspanCoordEquiv b
  let z : Fin n → ℤ := e v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply e.injective
    simpa [z] using hz0
  let ν : (Fin n → ℤ) → ℝ := fun x => μ (e.symm x)
  have hνpos : ∀ x ≠ 0, 0 < ν x := by
    intro x hx
    apply hμpos
    simpa using e.symm.injective.ne hx
  have hνhom : ∀ (c : ℤ), 0 < c → ∀ x, ν (c • x) = (c : ℝ) * ν x := by
    intro c hc x
    dsimp [ν]
    rw [map_smul]
    exact hμhom c hc (e.symm x)
  have hνmin : ∀ x ≠ 0, ν z ≤ ν x := by
    intro x hx
    dsimp [ν, z]
    rw [e.symm_apply_apply]
    apply hmin
    simpa using e.symm.injective.ne hx
  have hzprim : Erdos3.BohrLattice.Primitive.IsPrimitive z :=
    isPrimitive_of_minimal_gauge z hz ν hνpos hνhom hνmin
  refine ⟨hzprim, ?_⟩
  obtain ⟨B, hB⟩ := exists_basis_zero_eq_of_isPrimitive hn z hzprim
  refine ⟨B.map e.symm, ?_⟩
  rw [Basis.map_apply, hB]
  exact e.symm_apply_apply v

end

end Erdos3.BohrLattice.PrimitiveExtension

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]

def BasisBlockInvariant (b : Basis ι K V) (c : ι → δ) (U : Submodule K V) : Prop :=
  ∀ d x, x ∈ U → basisCoordinateProjection b {i | c i = d} x ∈ U

theorem sum_basisBlockProjection [Fintype ι] [DecidableEq δ]
    (b : Basis ι K V) (c : ι → δ) (x : V) :
    ∑ d ∈ Finset.univ.image c, basisCoordinateProjection b {i | c i = d} x = x := by
  classical
  apply b.repr.injective
  ext i
  have hi : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  simp only [map_sum, Finsupp.finsetSum_apply, basisCoordinateProjection_repr]
  change (∑ d ∈ Finset.univ.image c, if c i = d then b.repr x i else 0) = b.repr x i
  simp [hi]

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V W ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem BasisBlockInvariant.inf (e : Basis ι K V) (c : ι → δ)
    (U Z : Submodule K V) (hU : BasisBlockInvariant e c U) (hZ : BasisBlockInvariant e c Z) :
    BasisBlockInvariant e c (U ⊓ Z) :=
  fun a x hx => ⟨hU a x hx.1, hZ a x hx.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientBlocks
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι δ ε : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_coarser_block (b : Basis ι K V) (c : ι → δ)
    (f : δ → ε) (d : δ) (e : ε) [Decidable (f d = e)] (x : V) :
    basisCoordinateProjection b {i | f (c i) = e}
      (basisCoordinateProjection b {i | c i = d} x) =
      if f d = e then basisCoordinateProjection b {i | c i = d} x else 0 := by
  classical
  apply b.repr.injective
  ext i
  by_cases hi : c i = d <;> by_cases hd : f d = e <;>
    simp_all [basisCoordinateProjection_repr]

theorem BasisBlockInvariant.coarser [Fintype ι]
    (b : Basis ι K V) (c : ι → δ) (U : Submodule K V)
    (hU : BasisBlockInvariant b c U) (f : δ → ε) :
    BasisBlockInvariant b (fun i => f (c i)) U := by
  classical
  intro e x hx
  rw [← sum_basisBlockProjection b c x, map_sum]
  apply U.sum_mem
  intro d _
  rw [basisCoordinateProjection_coarser_block]
  split_ifs
  · exact hU d x hx
  · exact U.zero_mem

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBox
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

theorem exists_shortest_nonzero_of_basis {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ)) :
    ∃ v : Fin (n + 1) → ℝ,
      v ∈ Submodule.span ℤ (Set.range b) ∧ v ≠ 0 ∧
        ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  classical
  let e : Fin (n + 1) := 0
  have hbe_mem : b e ∈ Submodule.span ℤ (Set.range b) :=
    Submodule.subset_span ⟨e, rfl⟩
  have hbe_ne : b e ≠ 0 := b.ne_zero e
  let S : Set (Fin (n + 1) → ℝ) :=
    Metric.closedBall 0 ‖b e‖ ∩ Submodule.span ℤ (Set.range b)
  have hSfin : S.Finite := by
    exact ZSpan.setFinite_inter b Metric.isBounded_closedBall
  let T : Set (Fin (n + 1) → ℝ) := {x ∈ S | x ≠ 0}
  have hTfin : T.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hbeS : b e ∈ S := by
    refine ⟨?_, hbe_mem⟩
    simp
  have hTne : T.Nonempty := ⟨b e, hbeS, hbe_ne⟩
  obtain ⟨v, hvT, hvmin⟩ := Set.exists_min_image T norm hTfin hTne
  refine ⟨v, hvT.1.2, hvT.2, ?_⟩
  intro x hxL hx0
  by_cases hxle : ‖x‖ ≤ ‖b e‖
  · exact hvmin x ⟨⟨by simpa [Metric.mem_closedBall] using hxle, hxL⟩, hx0⟩
  · have hvle : ‖v‖ ≤ ‖b e‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvT.1.1
    exact hvle.trans (le_of_not_ge hxle)

theorem mem_realBox_const_iff_norm_le {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    x ∈ realBox (fun _ ↦ s) ↔ ‖x‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs]
  constructor
  · intro hx i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    constructor <;> intro i
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.1
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.2

theorem deleteProjection_self {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v v = 0 := by
  funext i
  simp [deleteProjection, hvh]

theorem reducedLift_apply_le {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (t a : ℝ)
    (hh : |v h| = ‖v‖) (hvh : v h ≠ 0)
    (ha : |x h / v h + a| ≤ (1 : ℝ) / 2)
    (hx : ‖deleteProjection h v x‖ ≤ t) :
    ‖x + a • v‖ ≤ t + ‖v‖ / 2 := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hx
  rw [pi_norm_le_iff_of_nonneg (add_nonneg ht (by positivity))]
  rw [h.forall_iff_succAbove]
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have heq : x h + a * v h = (x h / v h + a) * v h := by
      field_simp
    rw [heq, abs_mul, hh]
    calc
      |x h / v h + a| * ‖v‖ ≤ ((1 : ℝ) / 2) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg v)
      _ ≤ t + ‖v‖ / 2 := by linarith
  · intro j
    have hproj : |deleteProjection h v x j| ≤ t := by
      simpa only [Real.norm_eq_abs] using
        (abs_apply_le_norm (deleteProjection h v x) j).trans hx
    have hv : |v (h.succAbove j)| ≤ ‖v‖ :=
      abs_apply_le_norm v (h.succAbove j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have hdecomp : x (h.succAbove j) + a * v (h.succAbove j) =
        deleteProjection h v x j +
          (x h / v h + a) * v (h.succAbove j) := by
      rw [deleteProjection]
      ring
    rw [hdecomp]
    calc
      |deleteProjection h v x j + (x h / v h + a) * v (h.succAbove j)| ≤
          |deleteProjection h v x j| +
            |x h / v h + a| * |v (h.succAbove j)| := by
            simpa only [abs_mul] using
              abs_add_le (deleteProjection h v x j)
                ((x h / v h + a) * v (h.succAbove j))
      _ ≤ t + ((1 : ℝ) / 2) * ‖v‖ := by
        exact add_le_add hproj
          (mul_le_mul ha hv (abs_nonneg _) (by norm_num))
      _ = t + ‖v‖ / 2 := by ring

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MinkowskiSecondBoxBasis
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module

theorem projectedTail_det_ne_zero {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    (projectedTail h B).det ≠ 0 := by
  intro hq
  have habs := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h B hB
  rw [hq, abs_zero, mul_zero] at habs
  exact hdet (abs_eq_zero.mp habs)

noncomputable def projectedTailBasis {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (projectedTail h B).col
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (projectedTail_det_ne_zero h B hdet hB))
    (by simp)

@[simp] theorem projectedTailBasis_apply {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) (j : Fin n) :
    projectedTailBasis h B hdet hB j = (projectedTail h B).col j := by
  simp [projectedTailBasis]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBoxGlue
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

theorem deleteProjection_rawTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    deleteProjection h (fun i ↦ B i 0) (rawTailLift B z) =
      Matrix.mulVec (projectedTail h B) (intCastVec z) := by
  funext i
  simp only [deleteProjection, rawTailLift, Matrix.mulVec, dotProduct,
    projectedTail]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero,
    zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exists_abs_apply_eq_norm {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∃ h, |x h| = ‖x‖ := by
  classical
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    Finset.univ_nonempty
  refine ⟨h, le_antisymm (abs_apply_le_norm x h) ?_⟩
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg (x h))]
  intro i
  simpa only [Real.norm_eq_abs] using hh i (Finset.mem_univ i)

theorem realBox_smul_one_eq_const {n : ℕ} (s : ℝ) :
    realBox (s • (fun _ : Fin n ↦ (1 : ℝ))) = realBox (fun _ ↦ s) := by
  congr 1
  funext i
  simp

theorem cube_has_successiveProductCertificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      Nonempty (SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|)) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }⟩
      simp [minkowskiSecondConstant]
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos3.BohrLattice.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MinkowskiSecondInduction
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

noncomputable section

theorem realBox_has_minkowskiSecondCertificate {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Nonempty (BoxCertificate.SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range b)).toAddSubgroup r
      (minkowskiSecondConstant n * |(Matrix.of b).det| *
        (∏ i, r i)⁻¹)) := by
  classical
  open Erdos3.BohrLattice.MinkowskiDiagonalNormalization in
    let b' := normalizedBasis b r hr
    let e := divideCoordinates r hr
    obtain ⟨C⟩ := cube_has_successiveProductCertificate b'
    let point : Fin n → Fin n → ℝ := fun i ↦ e.symm (C.point i)
    refine ⟨{
      scale := C.scale
      point := point
      scale_nonneg := C.scale_nonneg
      point_mem := ?_
      independent := ?_
      mem_scaledBox := ?_
      product_le := ?_ }⟩
    · intro i
      change point i ∈ Submodule.span ℤ (Set.range b)
      apply (divideCoordinates_mem_span_iff b r hr (point i)).mp
      simpa [point, e, b'] using C.point_mem i
    · apply LinearIndependent.of_comp e.toLinearMap
      convert C.independent using 1
      funext i
      simp [point, e]
    · intro i
      change point i ∈ realBox (fun j ↦ C.scale i * r j)
      apply (mem_realBox_mul_iff r hr (C.scale i) (C.scale_nonneg i) (point i)).mpr
      have hi : C.point i ∈ realBox (fun _ ↦ C.scale i) := by
        rw [← realBox_smul_one_eq_const]
        exact C.mem_scaledBox i
      simpa [point, e] using hi
    · simpa [b', abs_det_normalizedBasis, mul_assoc] using C.product_le

end

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section General

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

theorem BasisHomogeneousBrackets.lie_mem_span (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : x ∈ Submodule.span R (b '' {k | w k = i}))
    (hy : y ∈ Submodule.span R (b '' {k | w k = j})) :
    ⁅x, y⁆ ∈ Submodule.span R (b '' {k | w k = i + j}) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    change w a = i at ha
    change w c = j at hc
    apply (basis_mem_span_image_iff b _ _).mpr
    intro k hk
    change w k ≠ i + j at hk
    exact hb a c k (by simpa only [ha, hc] using hk)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left r x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ r h
  | smul_right r x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ r h

end General

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareRationalModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFinWeight (w : ι → ℕ) :
    Fin (Fintype.card (ι ⊕ {i // 2 ≤ w i})) → ℕ :=
  fun i => squareBasisWeight w ((Fintype.equivFin _).symm i)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

namespace Set

lemma carrier_nonempty (B : Set N) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem⟩

lemma card_pos (B : Set N) : 0 < B.carrier.card :=
  Finset.card_pos.mpr B.carrier_nonempty

@[simp] lemma dilate_one (B : Set N) : B.dilate 1 = B := by
  cases B
  simp [dilate]

@[simp] lemma dilate_dilate (B : Set N) (s t : ℝ) :
    (B.dilate s).dilate t = B.dilate (t * s) := by
  cases B
  simp [dilate, abs_mul, mul_assoc]

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

@[simp] lemma card_argumentCodeSpace (B : Set N) (m : ℕ) :
    Fintype.card ((r : ↥B.frequencies) → Fin (m + 1)) =
      (m + 1) ^ B.rank := by
  simp [Set.rank]

@[simp] lemma card_localArgumentCodeSpace (B : Set N) :
    Fintype.card ((r : ↥B.frequencies) → Fin 9) = 9 ^ B.rank := by
  simp [Set.rank]

end CyclicBohr
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ReducedLatticeBasis
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

theorem exists_integral_spanning_product_certificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      ∃ C : SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|),
      span ℤ (Set.range C.point) = span ℤ (Set.range b) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }, ?_⟩
      · simp [minkowskiSecondConstant]
      · simp
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos3.BohrLattice.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq, hcqspan⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      have hspan : span ℤ (Set.range point) = L := by
        have hz : deleteProjectionLinear h v (b' 0) = 0 := by
          rw [hb'0, deleteProjectionLinear_apply, deleteProjection_self h v hvh]
        have ht : ∀ j, deleteProjectionLinear h v (b' j.succ) = qB j := by
          intro j
          ext i
          simp [qB, projectedTail, M, deleteProjection, hb'0]
        have hw : ∀ j, lift j ∈ span ℤ (Set.range b') := by
          intro j
          rw [hb'span]
          exact hliftL j
        have hs : span ℤ (Set.range (fun j => deleteProjectionLinear h v (lift j))) =
            span ℤ (Set.range qB) := by
          simpa only [deleteProjectionLinear_apply, hproj_lift] using hcqspan
        have hhspan := span_fin_cons_of_projected_span b' qB
          (deleteProjectionLinear h v) hz ht lift hw hs
        simpa only [hb'0, hb'span] using hhspan
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }, hspan⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

theorem exists_same_lattice_basis_norm_product_le {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    ∃ c : Basis (Fin n) ℝ (Fin n → ℝ),
      span ℤ (Set.range c) = span ℤ (Set.range b) ∧
      (∏ i, ‖c i‖) ≤ minkowskiSecondConstant n * |(Matrix.of b).det| := by
  obtain ⟨C, hspan⟩ := exists_integral_spanning_product_certificate b
  let c := basisOfLinearIndependentOfCardEqFinrank' C.point C.independent (by simp)
  have hc : ∀ i, c i = C.point i := by intro i; simp [c]
  refine ⟨c, ?_, ?_⟩
  · simpa only [show (c : Fin n → Fin n → ℝ) = C.point from funext hc] using hspan
  · apply le_trans (b := ∏ i, C.scale i) _ C.product_le
    apply Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rw [hc]
    apply (mem_realBox_const_iff_norm_le (C.scale_nonneg i) _).mp
    simpa only [realBox_smul_one_eq_const] using C.mem_scaledBox i

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShortGeneratingBasisBound
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem exists_short_same_lattice_basis {n : ℕ} {A : Type*}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (v : A → Fin n → ℝ) {R : ℝ}
    (hspan : span ℝ (Set.range v) = ⊤)
    (hmem : ∀ a, v a ∈ span ℤ (Set.range b)) (hnorm : ∀ a, ‖v a‖ ≤ R) :
    ∃ c : Basis (Fin n) ℝ (Fin n → ℝ),
      span ℤ (Set.range c) = span ℤ (Set.range b) ∧
      (∏ i, ‖c i‖) ≤ minkowskiSecondConstant n * |(Matrix.of c).det| ∧
      ∀ i, ‖c i‖ ≤ (n.factorial : ℝ) * minkowskiSecondConstant n * R := by
  obtain ⟨c, hc, hp⟩ := exists_same_lattice_basis_norm_product_le b
  rw [← abs_det_eq_of_same_integer_span c b hc] at hp
  refine ⟨c, hc, hp, ?_⟩
  apply basis_norm_le_of_short_spanning_family c (minkowskiSecondConstant_nonneg n) hp v hspan
  · intro a
    rw [hc]
    exact hmem a
  · exact hnorm

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuarticBohrProgression
namespace OAI

section

open scoped BigOperators Matrix Pointwise

namespace Erdos3.BohrProgression

open Erdos3.BohrLattice.BoxCertificate
open Erdos3.BohrLattice.MinkowskiSecondBox

noncomputable section

namespace CyclicCenteredGAP

abbrev Param {N : ℕ} (Q : CyclicCenteredGAP N) :=
  (i : Fin Q.rank) → Fin (2 * Q.radius i + 1)

def coeff {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) : ℤ := (x i : ℤ) - Q.radius i

def eval {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param) : ZMod N :=
  ∑ i, (Q.coeff x i : ZMod N) * Q.step i

noncomputable def carrier {N : ℕ} (Q : CyclicCenteredGAP N) : Finset (ZMod N) :=
  (Finset.univ : Finset Q.Param).image Q.eval

def Proper {N : ℕ} (Q : CyclicCenteredGAP N) : Prop :=
  Function.Injective Q.eval

lemma card_carrier_of_proper {N : ℕ} (Q : CyclicCenteredGAP N)
    (hQ : Q.Proper) :
    Q.carrier.card = ∏ i, (2 * Q.radius i + 1) := by
  rw [carrier, Finset.card_image_of_injective _ hQ, Finset.card_univ]
  simp [Param]

lemma coeff_abs_le {N : ℕ} (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i| ≤ (Q.radius i : ℤ) := by
  change |(x i : ℤ) - Q.radius i| ≤ (Q.radius i : ℤ)
  rw [abs_le]
  have hi := (x i).isLt
  change (x i : ℕ) < 2 * Q.radius i + 1 at hi
  constructor <;> omega

end CyclicCenteredGAP

end

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

lemma zero_proper (N : ℕ) : (zero N).Proper := by
  intro x y _
  funext i
  exact Fin.elim0 i

end CyclicCenteredGAP

end Erdos3.BohrProgression

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Finset
open scoped _root_.Finset

variable {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]

theorem addEnergy'_eq_div_energy (s t : Finset G) :
    addEnergy' s t = (_root_.Finset.addEnergy s t : ℚ≥0) / Fintype.card G ^ 3 := rfl

theorem cast_addEnergy' (s t : Finset G) :
    (addEnergy' s t : ℝ) = (_root_.Finset.addEnergy s t : ℝ) / (Fintype.card G : ℝ) ^ 3 := by
  rw [addEnergy'_eq_div_energy]
  simp

end Finset

end

section

namespace Erdos3.BSG

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem density_mul_le_iff_card_mul_le (s t : Finset G) (c : ℝ) :
    c * (s.dens : ℝ) ≤ t.dens ↔ c * (s.card : ℝ) ≤ t.card := by
  simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
  rw [← mul_div_assoc]
  exact div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))

omit [DecidableEq G] in
theorem density_le_mul_iff_card_le_mul (s t : Finset G) (c : ℝ) :
    (s.dens : ℝ) ≤ c * t.dens ↔ (s.card : ℝ) ≤ c * t.card := by
  simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
  rw [← mul_div_assoc]
  exact div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))

end Erdos3.BSG

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def IsPartitionMeasurable (P : FacePartition Ω) (g : Ω → ℝ) : Prop :=
  ∀ x y, y ∈ P.part x → g y = g x

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CyclicProgressionCoordinates
namespace OAI

section

open scoped BigOperators

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

variable {N : ℕ}

def minParam (Q : CyclicCenteredGAP N) : Q.Param := fun _ => 0

def predParam (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) : Q.Param := fun j =>
  if hji : j = i then
    ⟨(x i : ℕ) - 1, by
      subst j
      have hx := (x i).isLt
      omega⟩
  else x j

@[simp] lemma minParam_apply (Q : CyclicCenteredGAP N) (i : Fin Q.rank) :
    (Q.minParam i : ℕ) = 0 := rfl

end CyclicCenteredGAP

end Erdos3.BohrProgression

end

end OAI
end


