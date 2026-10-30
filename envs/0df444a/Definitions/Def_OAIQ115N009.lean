-- Prove2me | Definitions.Def_OAIQ115N009
-- name    : OAIQ115N009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:31:31.420507+00:00
-- url     : https://prove2.me/theorems/9403aa61-6239-4be7-b2c7-5c3f630802a7
-- title:
--   Definitions bundle OAIQ115N009 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 6 definitions and 33 theorems. The definitions and types are `OAI.NaimarkZFC.atomicEval`, `OAI.NaimarkZFC.fockColumnIndexEmbedding`, `OAI.NaimarkZFC.gnsOrbit`, `OAI.NaimarkZFC.hnnFaithfulEquiv`, `OAI.NaimarkZFC.momentGNSEquiv`, `OAI.NaimarkZFC.starAlgEquivOfFaithfulMoments`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Basic.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Operators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Operators.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean), [`Naimark_Representations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Representations.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N004`, `OAIQ115N005` and `OAIQ115N006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ115N011`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N004
import Definitions.Def_OAIQ115N005
import Definitions.Def_OAIQ115N006

section
-- module Solutions.OAIQ115_Naimark.Naimark_Basic
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed _root_.OAI.NaimarkZFC.vectorNullAlgebra_closed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFunctional_norm_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    ‖vectorFunctional π x‖ ≤ ‖x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro a
  calc
    ‖vectorFunctional π x a‖ = ‖⟪x, π a x⟫_ℂ‖ := rfl
    _ ≤ ‖x‖ * ‖π a x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖π a‖ * ‖x‖) := by gcongr; exact (π a).le_opNorm x
    _ ≤ ‖x‖ * (‖a‖ * ‖x‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = ‖x‖ ^ 2 * ‖a‖ := by ring

theorem isState_vectorFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : H) (hx : ‖x‖ = 1) : IsState (vectorFunctional π x) := by
  constructor
  · apply le_antisymm
    · simpa [hx] using vectorFunctional_norm_le π x
    · calc
        1 = ‖vectorFunctional π x 1‖ := by simp [vectorFunctional_one π hone, hx]
        _ ≤ ‖vectorFunctional π x‖ * ‖(1 : A)‖ := (vectorFunctional π x).le_opNorm 1
        _ ≤ ‖vectorFunctional π x‖ * 1 := by
          gcongr
          exact (IsStarProjection.one A).norm_le _
        _ = ‖vectorFunctional π x‖ := mul_one _
  · intro a
    rw [vectorFunctional_square]
    simp only [← Complex.ofReal_pow, Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact sq_nonneg _

theorem irreducible_vector_state (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : H) (hx : ‖x‖ = 1) : IsState (vectorFunctional π x) :=
  isState_vectorFunctional π (irreducible_map_one π hπ) x hx

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positive_eq_smul_of_gns_irreducible (f g : A →ₚ[ℂ] ℂ)
    (hπ : IsIrreducible f.gnsNonUnitalStarAlgHom) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    ∃ r : ℝ, ∀ a : A, g a = r • f a := by
  let T := dominatedGNS f g C hC hdom
  have hInt (a : A) : T.comp (f.gnsStarAlgHom a) = (g.gnsStarAlgHom a).comp T :=
    dominatedGNS_intertwines f g C hC hdom a
  have hcomm (a : A) : Commute (T.adjoint.comp T) (f.gnsStarAlgHom a) :=
    intertwiner_adjoint_comp_commute f.gnsNonUnitalStarAlgHom g.gnsNonUnitalStarAlgHom T hInt a
  have hself : IsSelfAdjoint (T.adjoint.comp T) := by
    change (T.adjoint.comp T).adjoint = T.adjoint.comp T
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  obtain ⟨r, hr⟩ := irreducible_commutant_selfAdjoint_scalar
    f.gnsNonUnitalStarAlgHom hπ (T.adjoint.comp T) hself hcomm
  refine ⟨r, ?_⟩
  intro a
  have hξ : T (gnsVector f) = gnsVector g := dominatedGNS_apply_vector f g C hC hdom
  have hact : T (f.gnsStarAlgHom a (gnsVector f)) = g.gnsStarAlgHom a (gnsVector g) := by
    simpa only [ContinuousLinearMap.comp_apply, hξ] using
      congrArg (fun R => R (gnsVector f)) (hInt a)
  calc
    g a = ⟪gnsVector g, g.gnsStarAlgHom a (gnsVector g)⟫_ℂ := (gnsVector_coefficient g a).symm
    _ = ⟪T (gnsVector f), T (f.gnsStarAlgHom a (gnsVector f))⟫_ℂ := by rw [hξ, hact]
    _ = ⟪gnsVector f, (T.adjoint.comp T) (f.gnsStarAlgHom a (gnsVector f))⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right T _ _).symm
    _ = r • f a := by
      rw [hr]
      simp only [smul_apply, one_apply_eq_self, inner_smul_right_eq_smul, gnsVector_coefficient]

theorem isPureState_of_gns_irreducible (f : A →L[ℂ] ℂ) (hf : IsState f)
    (hπ : IsIrreducible (positiveOfSquares f hf.2).gnsNonUnitalStarAlgHom) :
    IsPureState f := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨hf, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have dominated (g h : A →L[ℂ] ℂ) (hg : IsState g) (hh : IsState h)
      (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (heq : a • g + b • h = f) : g = f := by
    have hdom (x : A) : (g (star x * x)).re ≤ a⁻¹ * (f (star x * x)).re := by
      have hval := congrArg (fun k : A →L[ℂ] ℂ => (k (star x * x)).re) heq
      simp only [add_apply, smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul] at hval
      have hgpos := (hg.2 x).2
      have hhpos := (hh.2 x).2
      rw [mul_comm a⁻¹, ← div_eq_mul_inv, le_div_iff₀ ha]
      nlinarith
    obtain ⟨r, hr⟩ := positive_eq_smul_of_gns_irreducible
      (positiveOfSquares f hf.2) (positiveOfSquares g hg.2) hπ a⁻¹ (le_of_lt (inv_pos.mpr ha)) hdom
    have hone := hr 1
    simp only [positiveOfSquares_apply, ((isState_iff f).mp hf).1,
      ((isState_iff g).mp hg).1] at hone
    have hrone : r = 1 := by
      have hre := congrArg Complex.re hone
      simpa only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] using hre.symm
    ext x
    simpa only [hrone, one_smul, positiveOfSquares_apply] using hr x
  exact ⟨dominated g h hg hh a b ha hb heq,
    dominated h g hh hg b a hb ha (by rwa [add_comm])⟩

end GNS

section FaithfulMoments

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem faithful_gns_injective (f : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0) :
    Function.Injective f.gnsStarAlgHom := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  rw [← gnsVector_coefficient, map_mul, map_star, map_sub, hab, sub_self]
  simp

def gnsOrbit (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] f.GNS :=
  LinearMap.mkContinuous
    { toFun := fun a => f.gnsStarAlgHom a (gnsVector f)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    ‖gnsVector f‖ fun a => by
      calc
        ‖f.gnsStarAlgHom a (gnsVector f)‖ ≤ ‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖ :=
          (f.gnsStarAlgHom a).le_opNorm _
        _ ≤ ‖a‖ * ‖gnsVector f‖ := by
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le _ _
        _ = ‖gnsVector f‖ * ‖a‖ := mul_comm _ _

@[simp] theorem gnsOrbit_apply (f : A →ₚ[ℂ] ℂ) (a : A) :
    gnsOrbit f a = (f.toPreGNS a : f.GNS) := gns_apply_vector f a

theorem gnsOrbit_dense (f : A →ₚ[ℂ] ℂ) : DenseRange (gnsOrbit f) :=
  gnsVector_cyclic f

@[simp] theorem gnsOrbit_norm (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖gnsOrbit f a‖ = Real.sqrt (f (star a * a)).re := by
  simp only [gnsOrbit_apply, Completion.norm_coe, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ)
    (htr : ∀ r : R, f (i r) = g (j r))

def momentGNSEquiv : f.GNS ≃ₗᵢ[ℂ] g.GNS :=
  (LinearEquiv.refl ℂ R).extendOfIsometry
    ((gnsOrbit f).toLinearMap.comp i.toAlgHom.toLinearMap)
    ((gnsOrbit g).toLinearMap.comp j.toAlgHom.toLinearMap)
    ((gnsOrbit_dense f).comp hi (gnsOrbit f).continuous)
    ((gnsOrbit_dense g).comp hj (gnsOrbit g).continuous)
    (fun r => by
      change ‖gnsOrbit g (j r)‖ = ‖gnsOrbit f (i r)‖
      simp only [gnsOrbit_norm, ← map_mul, ← map_star, htr])

@[simp] theorem momentGNSEquiv_apply (r : R) :
    momentGNSEquiv i j hi hj f g htr (gnsOrbit f (i r)) = gnsOrbit g (j r) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ r

theorem momentGNSEquiv_intertwines (r : R) (x : f.GNS) :
    momentGNSEquiv i j hi hj f g htr (f.gnsStarAlgHom (i r) x) =
      g.gnsStarAlgHom (j r) (momentGNSEquiv i j hi hj f g htr x) := by
  let U := momentGNSEquiv i j hi hj f g htr
  have heq : (fun y : f.GNS => U (f.gnsStarAlgHom (i r) y)) =
      fun y => g.gnsStarAlgHom (j r) (U y) := by
    apply ((gnsOrbit_dense f).comp hi (gnsOrbit f).continuous).equalizer
      (by fun_prop) (by fun_prop)
    funext s
    change U (f.gnsStarAlgHom (i r) (gnsOrbit f (i s))) =
      g.gnsStarAlgHom (j r) (U (gnsOrbit f (i s)))
    have hmul (a b : A) : f.gnsStarAlgHom a (gnsOrbit f b) = gnsOrbit f (a * b) := by
      simp only [gnsOrbit_apply, gns_apply_coe]
    have hmul' (a b : B) : g.gnsStarAlgHom a (gnsOrbit g b) = gnsOrbit g (a * b) := by
      simp only [gnsOrbit_apply, gns_apply_coe]
    rw [hmul, ← map_mul]
    change momentGNSEquiv i j hi hj f g htr (gnsOrbit f (i (r * s))) = _
    rw [momentGNSEquiv_apply, momentGNSEquiv_apply, hmul', map_mul]
  exact congrFun heq x

include hi hj htr in

theorem norm_eq_of_faithful_moments
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) (r : R) : ‖j r‖ = ‖i r‖ := by
  let U := momentGNSEquiv i j hi hj f g htr
  have heq : U.conjStarAlgEquiv (f.gnsStarAlgHom (i r)) = g.gnsStarAlgHom (j r) := by
    ext x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    change momentGNSEquiv i j hi hj f g htr (f.gnsStarAlgHom (i r) (U.symm x)) = _
    rw [momentGNSEquiv_intertwines]
    simp [U]
  calc
    ‖j r‖ = ‖g.gnsStarAlgHom (j r)‖ :=
      (NonUnitalStarAlgHom.norm_map _ (faithful_gns_injective g hg) _).symm
    _ = ‖U.conjStarAlgEquiv (f.gnsStarAlgHom (i r))‖ := congrArg norm heq.symm
    _ = ‖f.gnsStarAlgHom (i r)‖ :=
      NonUnitalStarAlgHom.norm_map
        (U.conjStarAlgEquiv.toStarAlgHom :
          (f.GNS →L[ℂ] f.GNS) →⋆ₐ[ℂ] (g.GNS →L[ℂ] g.GNS))
        U.conjStarAlgEquiv.injective _
    _ = ‖i r‖ := NonUnitalStarAlgHom.norm_map _ (faithful_gns_injective f hf) _

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem starAlgEquivOfDenseNorm_apply
    (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j) (hnorm : ∀ r, ‖j r‖ = ‖i r‖) (r : R) :
    starAlgEquivOfDenseNorm i j hi hj hnorm (i r) = j r :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ r

def starAlgEquivOfFaithfulMoments (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (htr : ∀ r : R, f (i r) = g (j r))
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) : A ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfDenseNorm i j hi hj
    (norm_eq_of_faithful_moments i j hi hj f g htr hf hg)

@[simp] theorem starAlgEquivOfFaithfulMoments_apply (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (htr : ∀ r : R, f (i r) = g (j r))
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) (r : R) :
    starAlgEquivOfFaithfulMoments i j hi hj f g htr hf hg (i r) = j r :=
  starAlgEquivOfDenseNorm_apply ..

theorem starAlgEquivOfFaithfulMoments_preserves (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (htr : ∀ r : R, f (i r) = g (j r))
    (hf : ∀ a : A, f (star a * a) = 0 → a = 0)
    (hg : ∀ b : B, g (star b * b) = 0 → b = 0) (a : A) :
    g (starAlgEquivOfFaithfulMoments i j hi hj f g htr hf hg a) = f a := by
  let U := starAlgEquivOfFaithfulMoments i j hi hj f g htr hf hg
  have h := hi.equalizer (g := fun x : A => positiveCLM g (U x))
    (h := fun x : A => positiveCLM f x) (by fun_prop) (by fun_prop) (by
      funext r
      simp only [Function.comp_apply, U, starAlgEquivOfFaithfulMoments_apply,
        positiveCLM_apply, htr])
  exact congrFun h a

end FaithfulMoments

section MomentEquivalences

open scoped ComplexOrder
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
    (hv : ∀ i, star (v i) = v (!i)) (hw : ∀ i, star (w i) = w (!i))
    (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hrv : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hrw : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (f : B →ₚ[ℂ] ℂ) (g : C →ₚ[ℂ] ℂ)
    (hbase : ∀ a, f (φ a) = g (ψ a))
    (hred : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = g (ψ a*u.eval ψ w))
    (hf : ∀ a : B, f (star a*a) = 0 → a = 0)
    (hg : ∀ a : C, g (star a*a) = 0 → a = 0)
    (hB : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B))
    (hC : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C))

def hnnFaithfulEquiv : B ≃⋆ₐ[ℂ] C :=
  starAlgEquivOfFaithfulMoments
    ((StarAlgHom.fst ℂ B C).comp (StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype)
    ((StarAlgHom.snd ℂ B C).comp (StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype)
    (hnn_pair_fst_dense φ ψ v w hB) (hnn_pair_snd_dense φ ψ v w hC) f g
    (hnn_moments_equal φ ψ v w hv hw K center r hc hrv hrw
      (positiveCLM f) (positiveCLM g) hbase hred) hf hg

theorem hnnFaithfulEquiv_base (a : A) :
    hnnFaithfulEquiv φ ψ v w hv hw K center r hc hrv hrw f g hbase hred hf hg hB hC
      (φ a) = ψ a := by
  let z : StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i))) :=
    ⟨(φ a,ψ a),StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)⟩
  unfold hnnFaithfulEquiv
  exact starAlgEquivOfFaithfulMoments_apply _ _ _ _ _ _ _ _ _ z

theorem hnnFaithfulEquiv_letter (i : Bool) :
    hnnFaithfulEquiv φ ψ v w hv hw K center r hc hrv hrw f g hbase hred hf hg hB hC
      (v i) = w i := by
  let z : StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i))) :=
    ⟨(v i,w i),StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩)⟩
  unfold hnnFaithfulEquiv
  exact starAlgEquivOfFaithfulMoments_apply _ _ _ _ _ _ _ _ _ z

theorem hnnFaithfulEquiv_preserves (b : B) :
    g (hnnFaithfulEquiv φ ψ v w hv hw K center r hc hrv hrw f g hbase hred hf hg hB hC b)
      = f b :=
  starAlgEquivOfFaithfulMoments_preserves _ _ _ _ _ _ _ _ _ b
end MomentEquivalences

section HNNRestriction

open Topology
open scoped ComplexOrder
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

attribute [local instance] hnnGenerated_isClosed

section Trace
variable [PartialOrder C] [StarOrderedRing C]

@[simp] theorem restrictPositive_apply (S : StarSubalgebra ℂ C) [IsClosed (S : Set C)]
    [PartialOrder S] [StarOrderedRing S] (g : C →ₚ[ℂ] ℂ) (z : S) :
    restrictPositive S g z = g z.val := rfl

theorem restrictPositive_faithful (S : StarSubalgebra ℂ C) [IsClosed (S : Set C)]
    [PartialOrder S] [StarOrderedRing S] (g : C →ₚ[ℂ] ℂ)
    (hg : ∀ a : C, g (star a*a) = 0 → a = 0) (z : S)
    (hz : restrictPositive S g (star z*z) = 0) : z = 0 :=
  Subtype.ext (hg z.val hz)
end Trace

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]

theorem exists_hnnRestriction
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
    (hv : ∀ i, star (v i) = v (!i)) (hw : ∀ i, star (w i) = w (!i))
    (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hrv : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hrw : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (f : B →ₚ[ℂ] ℂ) (g : C →ₚ[ℂ] ℂ)
    (hbase : ∀ a, f (φ a) = g (ψ a))
    (hred : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = g (ψ a*u.eval ψ w))
    (hf : ∀ a : B, f (star a*a) = 0 → a = 0)
    (hg : ∀ a : C, g (star a*a) = 0 → a = 0)
    (hB : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) :
    ∃ F : B →⋆ₐ[ℂ] C, Function.Injective F ∧
      (∀ a, F (φ a) = ψ a) ∧ (∀ i, F (v i) = w i) ∧
      (∀ b, g (F b) = f b) ∧ F.range = hnnGenerated ψ w := by
  let S := hnnGenerated ψ w
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let Ψ := hnnGeneratedBase ψ w
  let ω := hnnGeneratedLetter ψ w
  let G := restrictPositive S g
  have hω : ∀ i, star (ω i) = ω (!i) := fun i => Subtype.ext (hw i)
  have hrω : ∀ i a, ω i*Ψ a*ω (!i) = ω i*Ψ (center i a)*ω (!i) + Ψ (r i a) :=
    fun i a => Subtype.ext (hrw i a)
  have hGb : ∀ a, f (φ a) = G (Ψ a) := hbase
  have heval (u : HNNWord A) : (u.eval Ψ ω).val = u.eval ψ w := by
    induction u with
    | single i a => rfl
    | cons i a u ih =>
      change w i*ψ a*(u.eval Ψ ω).val = w i*ψ a*u.eval ψ w
      rw [ih]
  have hGr : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = G (Ψ a*u.eval Ψ ω) := by
    intro u a hu
    change f (φ a*u.eval φ v) = g (ψ a*(u.eval Ψ ω).val)
    rw [heval]
    exact hred u a hu
  have hGf : ∀ a : S, G (star a*a) = 0 → a = 0 := restrictPositive_faithful S g hg
  let e := hnnFaithfulEquiv φ Ψ v ω hv hω K center r hc hrv hrω f G
    hGb hGr hf hGf hB (hnnGenerated_dense ψ w)
  refine ⟨S.subtype.comp e.toStarAlgHom, Subtype.val_injective.comp e.injective, ?_, ?_, ?_, ?_⟩
  · intro a
    exact congrArg Subtype.val (hnnFaithfulEquiv_base φ Ψ v ω hv hω K center r hc hrv hrω
      f G hGb hGr hf hGf hB (hnnGenerated_dense ψ w) a)
  · intro i
    exact congrArg Subtype.val (hnnFaithfulEquiv_letter φ Ψ v ω hv hω K center r hc hrv hrω
      f G hGb hGr hf hGf hB (hnnGenerated_dense ψ w) i)
  · intro b
    exact hnnFaithfulEquiv_preserves φ Ψ v ω hv hω K center r hc hrv hrω
      f G hGb hGr hf hGf hB (hnnGenerated_dense ψ w) b
  · ext z
    constructor
    · rintro ⟨b,rfl⟩
      exact (e b).property
    · intro hz
      exact ⟨e.symm ⟨z,hz⟩,congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)⟩

end HNNRestriction

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} [Fintype ι]

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
universe u v w

variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped CStarAlgebra InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem inequivalent_nullAlgebra_complement_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K) :
    Tendsto (fun e : vectorNullAlgebra π ξ => ρ (1 - (e : A)) η)
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
  let j := NonUnitalStarSubalgebraClass.subtype (vectorNullAlgebra π ξ)
  have ht := approximateUnit_strong (ρ.comp j)
    (CStarAlgebra.increasingApproximateUnit (vectorNullAlgebra π ξ))
    (fun η hη => inequivalent_nullAlgebra_common_kernel π hπ ξ hξ ρ hρ hne η hη) η
  simpa only [map_sub, sub_apply, irreducible_map_one ρ hρ, one_apply_eq_self,
    NonUnitalStarAlgHom.comp_apply, j, NonUnitalStarSubalgebraClass.coe_subtype,
    sub_self] using (tendsto_const_nhds (x := η)).sub ht

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma pureExcisionNet_inequivalent_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K) :
    Tendsto (fun e => ρ (pureExcisionNet π ξ e) η) atTop (𝓝 0) :=
  (inequivalent_nullAlgebra_complement_strong π hπ ξ hξ ρ hρ hne η).comp
    ExcisionIndex.tendsto_coe

open scoped InnerProductSpace ComplexStarModule
open Filter Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology

open scoped ComplexOrder ComplexStarModule

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {V J : Type*}

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockColumnIndexEmbedding (i : I) (t : FockTail L i) :
    ColumnIndex L i t.1.2.1 ↪ FockIndex L where
  toFun c := fockJoin L i ⟨t,c⟩
  inj' c e h := by
    have hh := (fockBlockEquiv L i).injective h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh

theorem fockColumnIndexEmbedding_ne {i : I} (t u : FockTail L i) (hu : u ≠ t)
    (c : ColumnIndex L i u.1.2.1) :
    fockJoin L i ⟨u,c⟩ ∉ Set.range (fockColumnIndexEmbedding L i t) := by
  rintro ⟨e, he⟩
  exact hu (congrArg Sigma.fst ((fockBlockEquiv L i).injective he)).symm

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

def atomicEval (k : I) : atomicAlgebra d →ₗ[ℂ] AtomicHilbertSpace d where
  toFun T := (T : AtomicOperators d) (atomicVacuum d k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint

open Filter Topology
open scoped ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology

open Filter Topology

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule
section
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] in

theorem no_common_irrep_of_dense_decay {ι : Type*} {l : Filter ι} [l.NeBot]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ξ ≠ 0) (hη : η ≠ 0) (S : Set A)
    (hdense : Dense (Submodule.span ℂ S : Set A)) (x y : ι → A)
    (hself : ∀ i, IsSelfAdjoint (x i))
    (hfix : ∀ i, π (x i) ξ = ξ) (hyfix : ∀ i, π (y i) η = η)
    (hdecay : ∀ a ∈ S, Tendsto (fun i => x i*a*y i) l (𝓝 0)) : False := by
  let F : A →L[ℂ] ℂ := (innerSL ℂ ξ).comp (orbitCLM π η)
  have hF : F = 0 := by
    apply ContinuousLinearMap.ext_on hdense
    intro a ha
    have he (i : ι) : F (x i*a*y i) = F a :=
      representation_coefficient_compression π ξ η _ _ _ (hself i) (hfix i) (hyfix i)
    have ht : Tendsto (fun _ : ι => F a) l (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def,he,map_zero] using (F.continuous.tendsto 0).comp (hdecay a ha)
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hc (a : A) : ⟪ξ, π a η⟫_ℂ = 0 := congrArg (fun f : A →L[ℂ] ℂ => f a) hF
  have hz : ⟪ξ,ξ⟫_ℂ = 0 := (irreducible_vector_cyclic π hπ η hη).induction_on (p := fun v => ⟪ξ,v⟫_ℂ = 0) ξ
    (isClosed_eq (innerSL ℂ ξ).continuous continuous_const) hc
  exact hξ (inner_self_eq_zero.mp hz)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [PartialOrder A] [StarOrderedRing A] in

theorem no_common_irrep_of_state_decay (φ : A →⋆ₐ[ℂ] C) (f g : A →L[ℂ] ℂ)
    (S : Set C) (hd : Dense (Submodule.span ℂ S : Set C)) (x y : ι → A)
    (hx : ∀ i, IsSelfAdjoint (x i)) (hxn : ∀ i, ‖x i‖ ≤ 1) (hyn : ∀ i, ‖y i‖ ≤ 1)
    (hxv : ∀ i, f (x i) = 1) (hyv : ∀ i, g (y i) = 1)
    (hdec : ∀ a ∈ S, Tendsto (fun i => φ (x i)*a*φ (y i)) l (𝓝 0))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = f a)
    (hcη : ∀ a, ⟪η,π (φ a) η⟫_ℂ = g a) : False := by
  apply no_common_irrep_of_dense_decay π hπ ξ η
    (norm_ne_zero_iff.mp (hξ.trans_ne one_ne_zero))
    (norm_ne_zero_iff.mp (hη.trans_ne one_ne_zero)) S hd
    (fun i => φ (x i)) (fun i => φ (y i)) (fun i => (hx i).map φ) ?_ ?_ hdec
  · intro i
    exact representation_fix_of_coefficient_one π ξ hξ _
      ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hxn i)) ((hcξ _).trans (hxv i))
  · intro i
    exact representation_fix_of_coefficient_one π η hη _
      ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hyn i)) ((hcη _).trans (hyv i))

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
attribute [-instance] _root_.OAI.NaimarkZFC.KOS.krylovSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem neg_saCayley_sub_one_norm (a : A) (ha : IsSelfAdjoint a) :
    ‖-saCayley a - 1‖ ≤ 2*‖a‖ := by
  have hr : ‖saResolvent a (-Complex.I)‖ ≤ 1 := by
    simpa only [Complex.neg_im,Complex.I_im,abs_neg,abs_one,inv_one] using
      saResolvent_norm_le a ha (-Complex.I) (by simp)
  have hi := (saResolvent_inverse a ha (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hi
  have he : -saCayley a - 1 = -(saResolvent a (-Complex.I) * (a+a)) := by
    rw [saCayley_eq a ha]
    calc
      -(saResolvent a (-Complex.I) * (a - Complex.I • (1:A))) - 1 =
        -(saResolvent a (-Complex.I) * (a - Complex.I • (1:A))) -
          saResolvent a (-Complex.I) * (a + Complex.I • (1:A)) := by rw [hi]
      _ = _ := by noncomm_ring
  rw [he,norm_neg]
  exact (norm_mul_le _ _).trans ((mul_le_mul hr (norm_add_le a a)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring))

theorem irreducible_near_unitary_vector
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hc : ‖ξ-η‖ ≤ 1) :
    ∃ u : unitary A, π u ξ = η ∧ ‖(u:A)-1‖ ≤ 96*‖ξ-η‖ := by
  have hd : 1 ≤ ‖ξ+η‖ := by
    have hh := norm_add_le (ξ+η) (ξ-η)
    have he : (ξ+η)+(ξ-η) = (2:ℂ) • ξ := by module
    rw [he,norm_smul,hξ,Complex.norm_ofNat,mul_one] at hh
    linarith
  have hd' : ‖ξ+η‖ ≤ 2 := (norm_add_le ξ η).trans (by rw [hξ,hη]; norm_num)
  have hi : (⟪ξ+η,Complex.I • (ξ-η)⟫_ℂ).im = 0 := by
    rw [inner_smul_right,inner_add_left,inner_sub_right,inner_sub_right]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
      Complex.sub_re,Complex.add_re,inner_self_eq_norm_sq_to_K]
    have hh := inner_re_symm (𝕜 := ℂ) ξ η
    change (⟪ξ,η⟫_ℂ).re = (⟪η,ξ⟫_ℂ).re at hh
    rw [hh,hξ,hη]; ring
  obtain ⟨T,hT,hTd,hTn⟩ := exists_bounded_selfAdjoint_operator_vector
    (ξ+η) (Complex.I • (ξ-η)) hd hd' hi
  obtain ⟨a,ha,han,haM⟩ := irreducible_selfAdjoint_transitivity π hπ
    (Submodule.span ℂ {ξ+η}) T hT
  have hact : π a (ξ+η) = Complex.I • (ξ-η) :=
    (haM _ (Submodule.subset_span (Set.mem_singleton _))).trans hTd
  have hre : π (a - Complex.I • (1:A)) ξ =
      π (a - (-Complex.I) • (1:A)) (-η) := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,irreducible_map_one π hπ,
      one_apply_eq_self,map_neg,neg_smul,neg_apply]
    have hh : π a ξ + π a η = Complex.I • ξ - Complex.I • η := by
      simpa only [map_add,smul_sub] using hact
    rw [eq_sub_of_add_eq hh]
    abel
  let v : unitary A := ⟨saCayley a,saCayley_unitary a ha⟩
  have hv : π (v:A) ξ = -η := by
    change π (saCayley a) ξ = -η
    rw [saCayley_eq a ha,map_mul,mul_apply_eq_comp,hre,← mul_apply_eq_comp,← map_mul]
    rw [← Algebra.algebraMap_eq_smul_one,(saResolvent_inverse a ha (-Complex.I) (by simp)).2,
      irreducible_map_one π hπ,one_apply_eq_self]
  refine ⟨-v,?_,?_⟩
  · change π (-(v:A)) ξ = η
    rw [map_neg,neg_apply,hv,neg_neg]
  · change ‖-saCayley a-1‖ ≤ 96*‖ξ-η‖
    have hh := neg_saCayley_sub_one_norm a ha
    simp only [norm_smul,Complex.norm_I,one_mul] at hTn
    linarith

end

open UniformSpace
open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem tracial_gns_zero_of_square_zero (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a*b) = τ (b*a)) (a : A) (ha : τ (star a*a) = 0) :
    τ.gnsStarAlgHom a = 0 := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic τ).equalizer ((τ.gnsStarAlgHom a).continuous) (by fun_prop)
  funext b
  change τ.gnsStarAlgHom a (τ.gnsStarAlgHom b (gnsVector τ)) = 0
  rw [← mul_apply_eq_comp,← map_mul]
  apply gns_vector_zero_of_square_zero
  apply norm_eq_zero.mp
  have hh := positiveTrace_sandwich τ htr (star a*a) b (star_mul_self_nonneg a)
  rw [ha,norm_zero,mul_zero] at hh
  apply le_antisymm _ (norm_nonneg _)
  simpa only [star_mul,mul_assoc] using hh

end

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [fintypeι : Fintype ι]

omit fintypeι in
lemma row_frame_coefficient [Fintype ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : ι → A) (v : H) (i j : ι) :
    ⟪π (star (x i)) v,π (star (x j)) v⟫_ℂ =
      vectorFunctional π v (x i*star (x j)) := by
  simp only [vectorFunctional_apply,map_mul,map_star,mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]

lemma row_defect_coefficient (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : ι → A) (v : H) :
    ‖π (rowAverage x 1) v-v‖^2 = (vectorFunctional π v (rowDefectTest x)).re := by
  rw [rowDefectTest,vectorFunctional_square,← Complex.ofReal_pow,Complex.ofReal_re]
  simp only [map_sub,sub_apply,hone,one_apply_eq_self]

lemma row_defect_bound (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : ι → A) (v : H) (r : ℝ) (hr : 0 ≤ r)
    (h : ‖vectorFunctional π v (rowDefectTest x)‖ ≤ r^2) :
    ‖π (rowAverage x 1) v-v‖ ≤ r := by
  have hs := (Complex.re_le_norm (vectorFunctional π v (rowDefectTest x))).trans h
  rw [← row_defect_coefficient π hone x v] at hs
  nlinarith [norm_nonneg (π (rowAverage x 1) v-v)]

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Operators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped BigOperators InnerProductSpace ComplexOrder
open Filter Topology

open scoped InnerProductSpace BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open scoped BigOperators InnerProductSpace

open scoped BigOperators

open scoped InnerProductSpace BigOperators
open Filter Topology

open scoped BigOperators InnerProductSpace
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit partialOrderA starOrderedRingA in
lemma irreducible_vector_lift [PartialOrder A] [StarOrderedRing A]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (η : H) : ∃ v : A, π v ξ=η := by
  let M := Submodule.span ℂ ({ξ}:Set H)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton ξ)
  obtain ⟨v,_,hv⟩ := irreducible_adjoint_transitivity π hπ M (InnerProductSpace.rankOne ℂ η ξ)
  refine ⟨v,?_⟩
  simpa [InnerProductSpace.rankOne_apply,inner_self_eq_norm_sq_to_K,hξ] using
    (hv ξ (Submodule.subset_span (by simp))).1

end KOS

open scoped BigOperators InnerProductSpace ComplexStarModule

end NaimarkZFC

end

end OAI
end


