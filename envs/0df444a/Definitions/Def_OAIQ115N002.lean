-- Prove2me | Definitions.Def_OAIQ115N002
-- name    : OAIQ115N002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:22:19.719802+00:00
-- url     : https://prove2.me/theorems/f2e8c290-06a2-41af-9190-821835c6fe48
-- title:
--   Definitions bundle OAIQ115N002 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 186 declarations of OpenAI's Lean: 45 definitions, 2 inductive types or structures, 23 instances and 116 theorems. The definitions and types are `OAI.NaimarkZFC.CARStage`, `OAI.NaimarkZFC.CStarCompletion.toCompletion`, `OAI.NaimarkZFC.CStarDirectLimit`, `OAI.NaimarkZFC.DependencyClosed`, `OAI.NaimarkZFC.HNNCenteredBlock`, `OAI.NaimarkZFC.HNNWord`, `OAI.NaimarkZFC.HNNWord.Reduced`, `OAI.NaimarkZFC.HNNWord.eval`, `OAI.NaimarkZFC.HNNWord.first`, `OAI.NaimarkZFC.IsometricStarSystem`, `OAI.NaimarkZFC.PeakingPairData.ambientSubalgebraOrder`, `OAI.NaimarkZFC.bridgeScalarPart`, `OAI.NaimarkZFC.bridgeZeroPart`, `OAI.NaimarkZFC.carBond`, `OAI.NaimarkZFC.carStageCStarAux`, `OAI.NaimarkZFC.carStep`, `OAI.NaimarkZFC.closedMapEquiv`, `OAI.NaimarkZFC.cstarDirectLimitInclude`, `OAI.NaimarkZFC.directLimitInclude`, `OAI.NaimarkZFC.directLimitNormTopology`, `OAI.NaimarkZFC.factorCenters`, `OAI.NaimarkZFC.generatedFamily`, `OAI.NaimarkZFC.hnnGenerated`, `OAI.NaimarkZFC.hnnGeneratedBase`, `OAI.NaimarkZFC.hnnGeneratedLetter`, `OAI.NaimarkZFC.hnnReducedSpan`, `OAI.NaimarkZFC.hnnWordSet`, `OAI.NaimarkZFC.hnnWordSpan`, `OAI.NaimarkZFC.jointFirst`, `OAI.NaimarkZFC.jointSecond`, `OAI.NaimarkZFC.jointStarModel`, `OAI.NaimarkZFC.matrixScalarHom`, `OAI.NaimarkZFC.omittedAlgebra`, `OAI.NaimarkZFC.omittedIndices`, `OAI.NaimarkZFC.pairedCenters`, `OAI.NaimarkZFC.pairedDiagonal`, `OAI.NaimarkZFC.pairedFactors`, `OAI.NaimarkZFC.rationalPreimage`, `OAI.NaimarkZFC.restrictPositive`, `OAI.NaimarkZFC.retainedOrdinalAlgebra` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Naimark_Amalgamation`, `Naimark_Basic`, `Naimark_CAR`, `Naimark_Dependencies`, `Naimark_DirectLimit`, `Naimark_Extension`, `Naimark_HNN`, `Naimark_Homogeneity`, `Naimark_Omission`, `Naimark_Peaking`, `Naimark_Recursion`, `Naimark_Representations`, `Naimark_States`.
--
--   **Imports.** It imports the published bundle `Def_Naimark`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N005` and `OAIQ115N006`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark

section
-- module Solutions.OAIQ115_Naimark.Naimark_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section HNNWords

inductive HNNWord (A : Type*)
  | single : Bool → A → HNNWord A
  | cons : Bool → A → HNNWord A → HNNWord A

namespace HNNWord
variable {A B : Type*} [Mul B]
def first : HNNWord A → Bool
  | .single i _ => i
  | .cons i _ _ => i

def eval (φ : A → B) (v : Bool → B) : HNNWord A → B
  | .single i a => v i * φ a
  | .cons i a w => v i * φ a * w.eval φ v

def Reduced (K : Bool → A → Prop) : HNNWord A → Prop
  | .single _ _ => True
  | .cons i a w => (i = w.first ∨ K i a) ∧ w.Reduced K
end HNNWord

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

def hnnWordSet : Set B := Set.range φ ∪
  {z | ∃ (w : HNNWord A) (a : A), w.Reduced K ∧ z = φ a*w.eval φ v}

def hnnWordSpan : Submodule ℂ B := Submodule.span ℂ (hnnWordSet φ v K)

theorem hnnWordSpan_base (a : A) : φ a ∈ hnnWordSpan φ v K :=
  Submodule.subset_span (Or.inl ⟨a,rfl⟩)

theorem hnnWordSpan_word (w : HNNWord A) (a : A) (hw : w.Reduced K) :
    φ a*w.eval φ v ∈ hnnWordSpan φ v K :=
  Submodule.subset_span (Or.inr ⟨w,a,hw,rfl⟩)

theorem hnnWordSpan_mul_base (a : A) {x : B} (hx : x ∈ hnnWordSpan φ v K) :
    φ a*x ∈ hnnWordSpan φ v K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨c,rfl⟩ | ⟨w,c,hw,rfl⟩
    · simpa only [← map_mul] using hnnWordSpan_base φ v K (a*c)
    · simpa only [map_mul,mul_assoc] using hnnWordSpan_word φ v K w (a*c) hw
  | zero => simpa only [mul_zero] using (hnnWordSpan φ v K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (hnnWordSpan φ v K).add_mem ix iy
  | smul c x hx ix => simpa only [mul_smul_comm] using (hnnWordSpan φ v K).smul_mem c ix

variable (center r : Bool → A → A)
  (hc : ∀ i a, K i (center i a))
  (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
include hc hr

theorem hnnWordSpan_left_word (i : Bool) (a : A) (w : HNNWord A)
    (hw : w.Reduced K) : v i*(φ a*w.eval φ v) ∈ hnnWordSpan φ v K := by
  by_cases hij : i = w.first
  · have hh := hnnWordSpan_word φ v K (.cons i a w) 1 ⟨Or.inl hij,hw⟩
    simpa only [map_one,one_mul,HNNWord.eval,mul_assoc] using hh
  · have he : w.first = !i := by
      cases i <;> cases h : w.first <;> simp_all
    have hmain := hnnWordSpan_word φ v K (.cons i (center i a) w) 1
      ⟨Or.inr (hc i a),hw⟩
    simp only [map_one,one_mul,HNNWord.eval] at hmain
    cases w with
    | single j d =>
      change j = !i at he
      subst j
      have hh : v i*(φ a*(v (!i)*φ d)) =
          v i*φ (center i a)*(v (!i)*φ d) + φ (r i a*d) := by
        calc
          _ = (v i*φ a*v (!i))*φ d := by simp only [mul_assoc]
          _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc]
      rw [HNNWord.eval,hh]
      exact (hnnWordSpan φ v K).add_mem hmain (hnnWordSpan_base φ v K _)
    | cons j d tail =>
      change j = !i at he
      subst j
      have hh : v i*(φ a*(v (!i)*φ d*tail.eval φ v)) =
          v i*φ (center i a)*(v (!i)*φ d*tail.eval φ v) +
            φ (r i a*d)*tail.eval φ v := by
        calc
          _ = (v i*φ a*v (!i))*φ d*tail.eval φ v := by simp only [mul_assoc]
          _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc]
      rw [HNNWord.eval,hh]
      exact (hnnWordSpan φ v K).add_mem hmain (hnnWordSpan_word φ v K tail _ hw.2)

theorem hnnWordSpan_mul_letter (i : Bool) {x : B} (hx : x ∈ hnnWordSpan φ v K) :
    v i*x ∈ hnnWordSpan φ v K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | ⟨w,a,hw,rfl⟩
    · simpa only [map_one,one_mul,HNNWord.eval] using
        hnnWordSpan_word φ v K (.single i a) 1 trivial
    · exact hnnWordSpan_left_word φ v K center r hc hr i a w hw
  | zero => simpa only [mul_zero] using (hnnWordSpan φ v K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (hnnWordSpan φ v K).add_mem ix iy
  | smul c x hx ix => simpa only [mul_smul_comm] using (hnnWordSpan φ v K).smul_mem c ix

theorem adjoin_le_hnnWordSpan :
    (Algebra.adjoin ℂ (Set.range φ ∪ Set.range v)).toSubmodule ≤ hnnWordSpan φ v K := by
  intro x hx
  have hinv : ∀ z ∈ Algebra.adjoin ℂ (Set.range φ ∪ Set.range v),
      ∀ y ∈ hnnWordSpan φ v K, z*y ∈ hnnWordSpan φ v K := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a,rfl⟩ | ⟨i,rfl⟩
      · exact fun y hy => hnnWordSpan_mul_base φ v K a hy
      · exact fun y hy => hnnWordSpan_mul_letter φ v K center r hc hr i hy
    | algebraMap c =>
      intro y hy
      simpa only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] using
        (hnnWordSpan φ v K).smul_mem c hy
    | add x y hx hy ix iy =>
      intro z hz
      simpa only [add_mul] using (hnnWordSpan φ v K).add_mem (ix z hz) (iy z hz)
    | mul x y hx hy ix iy =>
      intro z hz
      simpa only [mul_assoc] using ix (y*z) (iy z hz)
  have h1 : (1:B) ∈ hnnWordSpan φ v K := by
    simpa only [map_one] using hnnWordSpan_base φ v K 1
  simpa only [mul_one] using hinv x hx 1 h1

end HNNWords

section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem gns_apply_coe (f : A →ₚ[ℂ] ℂ) (a b : A) :
    f.gnsStarAlgHom a (f.toPreGNS b : f.GNS) = (f.toPreGNS (a * b) : f.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.gnsNonUnitalStarAlgHom,
    ContinuousLinearMap.completion_apply_coe, PositiveLinearMap.leftMulMapPreGNS]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem invariant_orthogonal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H)
    (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M) :
    ∀ a : A, ∀ x ∈ Mᗮ, π a x ∈ Mᗮ := by
  intro a x hx y hy
  have hz := hx (π (star a) y) (hM (star a) y hy)
  rw [map_star] at hz
  exact (ContinuousLinearMap.adjoint_inner_left (π a) x y).symm.trans hz

theorem invariant_starProjection_commute (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M) (a : A) (x : H) :
    M.starProjection (π a x) = π a (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hM a _ (M.starProjection_apply_mem x)
  · rw [← map_sub]
    exact invariant_orthogonal π M hM a _ (M.sub_starProjection_mem_orthogonal x)

variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem cyclic_closed_invariant_top (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a : A => π a ξ)) (M : Submodule ℂ H)
    (hclosed : IsClosed (M : Set H)) (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M)
    (hξ : ξ ∈ M) : M = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  apply closure_minimal (s := Set.range (fun a : A => π a ξ)) _ hclosed (hcyc x)
  rintro y ⟨a, rfl⟩
  exact hinv a ξ hξ

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_denseRange (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (T : H →L[ℂ] H) (hT : T ≠ 0)
    (hcomm : ∀ a : A, Commute T (π a)) : DenseRange T := by
  let M := T.range
  have hinv (a : A) : M.map (π a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
    refine ⟨π a x, ?_⟩
    exact congrArg (fun S : H →L[ℂ] H => S x) (hcomm a).eq
  have hcl (a : A) (x : H) (hx : x ∈ M.topologicalClosure) :
      π a x ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hinv a)
    apply Submodule.topologicalClosure_map (π a) M
    exact ⟨x, hx, rfl⟩
  rcases hπ.2 M.topologicalClosure M.isClosed_topologicalClosure hcl with hz | ht
  · exfalso
    apply hT
    ext x
    have hx : T x ∈ M.topologicalClosure := M.le_topologicalClosure ⟨x, rfl⟩
    rw [hz] at hx
    exact hx
  · intro x
    have hx : x ∈ M.topologicalClosure := by rw [ht]; trivial
    exact hx

theorem commutant_mul_eq_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (S T : H →L[ℂ] H)
    (hcomm : ∀ a : A, Commute T (π a)) (hz : S * T = 0) : S = 0 ∨ T = 0 := by
  by_cases hT : T = 0
  · exact Or.inr hT
  · left
    apply DFunLike.coe_injective
    change (fun x => S x) = (fun _ => 0)
    apply (irreducible_commutant_denseRange π hπ T hT hcomm).equalizer
      S.continuous continuous_const
    funext x
    exact congrArg (fun R : H →L[ℂ] H => R x) hz

end GNS

section FaithfulMoments

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j)
    (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ)
    (htr : ∀ r : R, f (i r) = g (j r))

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

def starAlgEquivOfDenseNorm (i : R →⋆ₐ[ℂ] A) (j : R →⋆ₐ[ℂ] B)
    (hi : DenseRange i) (hj : DenseRange j) (hnorm : ∀ r, ‖j r‖ = ‖i r‖) : A ≃⋆ₐ[ℂ] B := by
  let U : A ≃ₗᵢ[ℂ] B := (LinearEquiv.refl ℂ R).extendOfIsometry
    i.toAlgHom.toLinearMap j.toAlgHom.toLinearMap hi hj hnorm
  have hU (r : R) : U (i r) = j r :=
    LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ r
  have hleft (r : R) (b : A) : U (i r * b) = j r * U b := by
    have h := hi.equalizer (g := fun x : A => U (i r * x))
      (h := fun x : A => j r * U x) (by fun_prop) (by fun_prop) (by
        funext s
        simp only [Function.comp_apply, ← map_mul, hU])
    exact congrFun h b
  have hmul (a b : A) : U (a * b) = U a * U b := by
    have h := hi.equalizer (g := fun x : A => U (x * b))
      (h := fun x : A => U x * U b) (by fun_prop) (by fun_prop) (by
        funext r
        simp only [Function.comp_apply, hU, hleft])
    exact congrFun h a
  have hstar (a : A) : U (star a) = star (U a) := by
    have h := hi.equalizer (g := fun x : A => U (star x))
      (h := fun x : A => star (U x)) (by fun_prop) (by fun_prop) (by
        funext r
        simp only [Function.comp_apply, ← map_star, hU])
    exact congrFun h a
  exact { U.toLinearEquiv with map_mul' := hmul, map_star' := hstar }

end FaithfulMoments

section MomentEquivalences

open scoped ComplexOrder
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem hnn_generators_star (φ : A →⋆ₐ[ℂ] B) (v : Bool → B)
    (hv : ∀ i, star (v i) = v (!i)) :
    star (Set.range φ ∪ Set.range v) ⊆ Set.range φ ∪ Set.range v := by
  intro x hx
  have hh : star x ∈ Set.range φ ∪ Set.range v := Set.mem_star.mp hx
  rcases hh with ⟨a,ha⟩ | ⟨i,hi⟩
  · left
    exact ⟨star a, by rw [map_star,ha,star_star]⟩
  · right
    exact ⟨!i, by rw [← hv,hi,star_star]⟩

theorem hnn_moments_equal
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
    (hv : ∀ i, star (v i) = v (!i)) (hw : ∀ i, star (w i) = w (!i))
    (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hrv : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hrw : ∀ i a, w i*ψ a*w (!i) = w i*ψ (center i a)*w (!i) + ψ (r i a))
    (f : B →L[ℂ] ℂ) (g : C →L[ℂ] ℂ)
    (hbase : ∀ a, f (φ a) = g (ψ a))
    (hred : ∀ (u : HNNWord A) (a : A), u.Reduced K →
      f (φ a*u.eval φ v) = g (ψ a*u.eval ψ w))
    (z : StarAlgebra.adjoin ℂ
      (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))) :
    f (z.val.1) = g (z.val.2) := by
  let η := φ.prod ψ
  let t : Bool → B × C := fun i => (v i,w i)
  have ht : ∀ i, star (t i) = t (!i) := fun i => Prod.ext (hv i) (hw i)
  have hrt : ∀ i a, t i*η a*t (!i) = t i*η (center i a)*t (!i) + η (r i a) :=
    fun i a => Prod.ext (hrv i a) (hrw i a)
  have hz : z.val ∈ Algebra.adjoin ℂ (Set.range η ∪ Set.range t) := by
    have hh := z.property
    change z.val ∈ (StarAlgebra.adjoin ℂ (Set.range η ∪ Set.range t)).toSubalgebra at hh
    rw [StarAlgebra.adjoin_toSubalgebra, Set.union_eq_self_of_subset_right
      (hnn_generators_star η t ht)] at hh
    exact hh
  have hspan := adjoin_le_hnnWordSpan η t K center r hc hrt hz
  have eval_proj (u : HNNWord A) : (u.eval η t).1 = u.eval φ v ∧
      (u.eval η t).2 = u.eval ψ w := by
    induction u with
    | single i a => exact ⟨rfl,rfl⟩
    | cons i a u ih =>
      change v i*φ a*(u.eval η t).1 = _ ∧ w i*ψ a*(u.eval η t).2 = _
      rw [ih.1,ih.2]
      exact ⟨rfl,rfl⟩
  generalize hzv : z.val = x at hspan ⊢
  clear hzv
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | ⟨u,a,hu,rfl⟩
    · exact hbase a
    · change f (φ a*(u.eval η t).1) = g (ψ a*(u.eval η t).2)
      rw [(eval_proj u).1,(eval_proj u).2]
      exact hred u a hu
  | zero => simp only [Prod.fst_zero,Prod.snd_zero,map_zero]
  | add x y hx hy ix iy => simp only [Prod.fst_add,Prod.snd_add,map_add,ix,iy]
  | smul c x hx ix =>
    change f (c • x.1) = g (c • x.2)
    rw [map_smul,map_smul,ix]

theorem hnn_pair_fst_dense (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C)
    (v : Bool → B) (w : Bool → C)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) :
    DenseRange ((StarAlgHom.fst ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := ((StarAlgHom.fst ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype).range) ?_ hx
  rintro y (⟨a,rfl⟩ | ⟨i,rfl⟩)
  · refine ⟨⟨(φ a,ψ a),StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)⟩,rfl⟩
  · refine ⟨⟨(v i,w i),StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩)⟩,rfl⟩

theorem hnn_pair_snd_dense (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C)
    (v : Bool → B) (w : Bool → C)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    DenseRange ((StarAlgHom.snd ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := ((StarAlgHom.snd ℂ B C).comp
      (StarAlgebra.adjoin ℂ
        (Set.range (φ.prod ψ) ∪ Set.range (fun i => (v i,w i)))).subtype).range) ?_ hx
  rintro y (⟨a,rfl⟩ | ⟨i,rfl⟩)
  · refine ⟨⟨(φ a,ψ a),StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)⟩,rfl⟩
  · refine ⟨⟨(v i,w i),StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩)⟩,rfl⟩

end MomentEquivalences

section HNNRestriction

open Topology
open scoped ComplexOrder
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

def hnnGenerated (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) : StarSubalgebra ℂ C :=
  (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w)).topologicalClosure

theorem hnnGenerated_isClosed (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) :
    IsClosed (hnnGenerated ψ w : Set C) := isClosed_closure
attribute [local instance] hnnGenerated_isClosed

def hnnGeneratedBase (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) : A →⋆ₐ[ℂ] hnnGenerated ψ w :=
  ψ.codRestrict _ (fun a => subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩)))

def hnnGeneratedLetter (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (i : Bool) : hnnGenerated ψ w :=
  ⟨w i,subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩))⟩

theorem hnnGenerated_dense (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) :
    Dense (StarAlgebra.adjoin ℂ
      (Set.range (hnnGeneratedBase ψ w) ∪ Set.range (hnnGeneratedLetter ψ w)) :
        Set (hnnGenerated ψ w)) := by
  let R := StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w)
  let T := StarAlgebra.adjoin ℂ
    (Set.range (hnnGeneratedBase ψ w) ∪ Set.range (hnnGeneratedLetter ψ w))
  have hm : T.map (hnnGenerated ψ w).subtype = R := by
    rw [StarAlgHom.map_adjoin]
    apply congrArg (StarAlgebra.adjoin ℂ)
    ext x
    constructor
    · rintro ⟨y,(⟨a,rfl⟩ | ⟨i,rfl⟩),rfl⟩
      · exact Or.inl ⟨a,rfl⟩
      · exact Or.inr ⟨i,rfl⟩
    · rintro (⟨a,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨hnnGeneratedBase ψ w a,Or.inl ⟨a,rfl⟩,rfl⟩
      · exact ⟨hnnGeneratedLetter ψ w i,Or.inr ⟨i,rfl⟩,rfl⟩
  have hd : DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure R)) := by
    exact (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  apply hd.mono
  rintro x ⟨y,rfl⟩
  have hy : y.val ∈ T.map (hnnGenerated ψ w).subtype := by
    rw [hm]
    exact y.property
  obtain ⟨z,hz,hzy⟩ := hy
  have he : z = Set.inclusion (StarSubalgebra.le_topologicalClosure R) y :=
    Subtype.ext hzy
  exact he ▸ hz

section Trace
variable [PartialOrder C] [StarOrderedRing C]

def restrictPositive (S : StarSubalgebra ℂ C) [IsClosed (S : Set C)]
    [PartialOrder S] [StarOrderedRing S] (g : C →ₚ[ℂ] ℂ) : S →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (g.toLinearMap.comp S.subtype.toAlgHom.toLinearMap)
    (fun x hx => g.map_nonneg (by
      let π : S →⋆ₙ+* C :=
        { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl,
          map_mul' := fun _ _ => rfl, map_star' := fun _ => rfl }
      have h := π.map_le_map_of_map_star hx
      exact h))

end Trace

end HNNRestriction

section WordSpans

open Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

def hnnReducedSpan : Submodule ℂ B :=
  Submodule.span ℂ {z | ∃ (w : HNNWord A) (a : A), w.Reduced K ∧ z = φ a*w.eval φ v}

theorem hnnWordSpan_center_mem (E : B →L[ℂ] A) (hbase : ∀ a, E (φ a) = a)
    (hred : ∀ (w : HNNWord A) (a : A), w.Reduced K → E (φ a*w.eval φ v) = 0)
    {x : B} (hx : x ∈ hnnWordSpan φ v K) : x-φ (E x) ∈ hnnReducedSpan φ v K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a,rfl⟩ | ⟨w,a,hw,rfl⟩
    · simpa only [hbase,sub_self] using (hnnReducedSpan φ v K).zero_mem
    · rw [hred w a hw,map_zero,sub_zero]
      exact Submodule.subset_span ⟨w,a,hw,rfl⟩
  | zero => simpa only [map_zero,sub_self] using (hnnReducedSpan φ v K).zero_mem
  | add x y hx hy ix iy =>
    simpa only [map_add,add_sub_add_comm] using (hnnReducedSpan φ v K).add_mem ix iy
  | smul c x hx ix =>
    simpa only [map_smul,smul_sub] using (hnnReducedSpan φ v K).smul_mem c ix

theorem hnnWordSpan_dense (hv : ∀ i, star (v i) = v (!i))
    (center r : Bool → A → A) (hc : ∀ i a, K i (center i a))
    (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) :
    Dense (hnnWordSpan φ v K : Set B) := by
  apply hd.mono
  intro z hz
  apply adjoin_le_hnnWordSpan φ v K center r hc hr
  change z ∈ (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v)).toSubalgebra at hz
  have hs : star (Set.range φ ∪ Set.range v) ⊆ Set.range φ ∪ Set.range v := by
    intro x hx
    have hh : star x ∈ Set.range φ ∪ Set.range v := Set.mem_star.mp hx
    rcases hh with ⟨a,ha⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨star a,by rw [map_star,ha,star_star]⟩
    · exact Or.inr ⟨!i,by rw [← hv,hi,star_star]⟩
  rwa [StarAlgebra.adjoin_toSubalgebra,Set.union_eq_self_of_subset_right hs] at hz

end WordSpans

open Topology
variable {A B C D : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra C] [CStarAlgebra D]

theorem HNNWord.eval_hom (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C)
    (v : Bool → B) (w : Bool → C) (F : B →⋆ₐ[ℂ] C)
    (hbase : ∀ a, F (φ a) = ψ a) (hletter : ∀ i, F (v i) = w i) (u : HNNWord A) :
    F (u.eval φ v) = u.eval ψ w := by
  induction u with
  | single i a => simp only [HNNWord.eval,map_mul,hbase,hletter]
  | cons i a u ih => simp only [HNNWord.eval,map_mul,hbase,hletter,ih]

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointSubspace (S : StarSubalgebra ℂ A) : Submodule ℝ A :=
  (S.toSubalgebra.toSubmodule.restrictScalars ℝ) ⊓ selfAdjoint.submodule ℝ A

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

open scoped CStarAlgebra

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
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

theorem inner_realPart_operator (T : H →L[ℂ] H) (x y : H) :
    2 * (⟪y, (realPart T : H →L[ℂ] H) x⟫_ℂ).re =
      (⟪y, T x⟫_ℂ).re + (⟪T y, x⟫_ℂ).re := by
  simp only [realPart_apply_coe, smul_apply, add_apply, ← Complex.coe_smul,
    inner_smul_right, inner_add_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

variable {ι : Type*} [Fintype ι]

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

theorem sa_spectrum_sub_ne_zero (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) (t : ℂ) (ht : t ∈ spectrum ℂ a) : t - z ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  exact hz (he ▸ ha.im_eq_zero_of_mem_spectrum ht)

theorem saResolvent_continuousOn (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousOn (fun t : ℂ => (t - z)⁻¹) (spectrum ℂ a) :=
  (continuous_id.sub continuous_const).continuousOn.inv₀ (sa_spectrum_sub_ne_zero a ha z hz)

theorem resolvent_sum_real (t : ℝ) :
    ((t : ℂ) - Complex.I)⁻¹ + ((t : ℂ) - (-Complex.I))⁻¹ =
      (2 * t / (1 + t ^ 2) : ℝ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      zero_sub, sub_zero, neg_zero, neg_neg] <;> ring

def rationalPreimage (t : ℝ) : ℝ := t / (1 + Real.sqrt (1 - t ^ 2))

theorem rationalPreimage_continuous : Continuous rationalPreimage := by
  change Continuous (fun t : ℝ => t / (1 + Real.sqrt (1 - t ^ 2)))
  exact continuous_id.div
    (continuous_const.add ((continuous_const.sub (continuous_id.pow 2)).sqrt))
    (fun t => ne_of_gt (show 0 < 1 + Real.sqrt (1 - t ^ 2) by positivity))

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def symmetricCompression (P T : H →L[ℂ] H) : H →L[ℂ] H := T * P + P * T - P * T * P

theorem symmetricCompression_selfAdjoint (P T : H →L[ℂ] H)
    (hP : IsSelfAdjoint P) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (symmetricCompression P T) := by
  change star (symmetricCompression P T) = symmetricCompression P T
  simp only [symmetricCompression, star_sub, star_add, star_mul, hP.star_eq, hT.star_eq]
  noncomm_ring

omit [CompleteSpace H] in
theorem symmetricCompression_mul_projection (P T : H →L[ℂ] H)
    (hP : IsIdempotentElem P) : symmetricCompression P T * P = T * P := by
  have hPP : P * P = P := hP
  simp only [symmetricCompression, add_mul, sub_mul, mul_assoc, hPP]
  abel

theorem symmetricCompression_norm_le (P T : H →L[ℂ] H)
    (hP : IsSelfAdjoint P) (hT : IsSelfAdjoint T) (hn : ‖P‖ ≤ 1) :
    ‖symmetricCompression P T‖ ≤ 3 * ‖T * P‖ := by
  have h : ‖P * T‖ = ‖T * P‖ := by
    rw [← norm_star (P * T)]
    simp only [star_mul, hP.star_eq, hT.star_eq]
  have h' : ‖P * T * P‖ ≤ ‖T * P‖ := by
    calc
      _ ≤ ‖P * T‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖P * T‖ * 1 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = ‖T * P‖ := by rw [mul_one, h]
  calc
    ‖symmetricCompression P T‖ ≤ ‖T * P + P * T‖ + ‖P * T * P‖ := norm_sub_le _ _
    _ ≤ (‖T * P‖ + ‖P * T‖) + ‖P * T * P‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 3 * ‖T * P‖ := by linarith

omit [CompleteSpace H] in

theorem norm_mul_starProjection_le_sum {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ M) (T : H →L[ℂ] H) :
    ‖T * M.starProjection‖ ≤ ∑ i, ‖T (b i : H)‖ := by
  classical
  rw [b.starProjection_eq_sum_rankOne, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
    InnerProductSpace.norm_rankOne]
  have hb : ‖(b i : H)‖ = 1 := b.orthonormal.1 i
  rw [hb, mul_one]

omit [CompleteSpace H] in

theorem symmetricCompression_apply_of_mem {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    (T : H →L[ℂ] H) {x : H} (hx : x ∈ M) :
    symmetricCompression M.starProjection T x = T x := by
  have hp := symmetricCompression_mul_projection M.starProjection T M.isIdempotentElem_starProjection
  have hh := congrArg (fun S : H →L[ℂ] H => S x) hp
  simpa only [mul_apply_eq_comp, M.starProjection_eq_self_iff.mpr hx] using hh

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

def saCayley (a : A) : A :=
  cfc (fun t : ℂ => (t - (-Complex.I))⁻¹ * (t - Complex.I)) a

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

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_contraction_square_le {y : A} (hy : 0 ≤ y) (hn : ‖y‖ ≤ 1) :
    y * y ≤ y := by
  have h1 : y ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg y hy).mp hn
  have hpos := ((Commute.one_right y).sub_right (Commute.refl y)).mul_nonneg
    hy (sub_nonneg.mpr h1)
  simpa only [mul_sub, mul_one, sub_nonneg] using hpos

theorem cross_excision_bound {x y z : A} (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1)
    (hy : 0 ≤ y) (hyn : ‖y‖ ≤ 1) (hyz : y ≤ z) (a : A) (c : ℂ) :
    ‖x * a * y‖ ^ 2 ≤ ‖c‖ + ‖x * (a * z * star a - c • (1 : A)) * x‖ := by
  have hxs := IsSelfAdjoint.of_nonneg hx
  have hys := IsSelfAdjoint.of_nonneg hy
  have hsq := (positive_contraction_square_le hy hyn).trans hyz
  have hle := star_right_conjugate_le_conjugate hsq (x * a)
  have hid : x * a * (y * y) * star (x * a) =
      (x * a * y) * star (x * a * y) := by
    simp only [star_mul, hxs.star_eq, hys.star_eq]
    noncomm_ring
  rw [hid] at hle
  calc
    ‖x * a * y‖ ^ 2 = ‖(x * a * y) * star (x * a * y)‖ := by
      rw [CStarRing.norm_self_mul_star, pow_two]
    _ ≤ ‖x * a * z * star (x * a)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (mul_star_self_nonneg _) hle
    _ = ‖c • (x * x) + x * (a * z * star a - c • (1 : A)) * x‖ := by
      congr 1
      simp only [star_mul, hxs.star_eq, mul_sub, sub_mul, mul_smul_comm,
        smul_mul_assoc, mul_one]
      noncomm_ring
    _ ≤ ‖c • (x * x)‖ + ‖x * (a * z * star a - c • (1 : A)) * x‖ := norm_add_le _ _
    _ ≤ ‖c‖ + ‖x * (a * z * star a - c • (1 : A)) * x‖ := by
      gcongr
      rw [norm_smul]
      calc
        _ ≤ ‖c‖ * (‖x‖ * ‖x‖) := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖c‖ * (1 * 1) := by gcongr
        _ = ‖c‖ := by ring

theorem cross_excision_tendsto
    {ι κ : Type*} [Preorder ι] [Preorder κ]
    [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
    (x : ι → A) (y : κ → A) (f : A → ℂ)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hy : ∀ j, 0 ≤ y j) (hyn : ∀ j, ‖y j‖ ≤ 1)
    (hym : Antitone y)
    (hexc : ∀ b : A, Tendsto (fun i => x i * (b - f b • (1 : A)) * x i) atTop (𝓝 0))
    (a : A) (hcoef : Tendsto (fun j => f (a * y j * star a)) atTop (𝓝 0)) :
    Tendsto (fun ij : ι × κ => x ij.1 * a * y ij.2) atTop (𝓝 0) := by
  let : IsDirectedOrder (ι × κ) := ⟨by
    intro p q
    obtain ⟨i, hi, hi'⟩ := exists_ge_ge p.1 q.1
    obtain ⟨j, hj, hj'⟩ := exists_ge_ge p.2 q.2
    exact ⟨(i,j), ⟨hi,hj⟩, ⟨hi',hj'⟩⟩⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  have hc : ∀ᶠ j in atTop, ‖f (a * y j * star a)‖ < ε ^ 2 / 2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hcoef) _ hδ
  obtain ⟨j, hj⟩ := hc.exists
  have he : ∀ᶠ i in atTop,
      ‖x i * (a * y j * star a - f (a * y j * star a) • (1 : A)) * x i‖ < ε ^ 2 / 2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp (hexc (a * y j * star a))) _ hδ
  rw [eventually_atTop] at he
  obtain ⟨i, hi⟩ := he
  rw [eventually_atTop]
  refine ⟨(i,j), fun ij hij => ?_⟩
  simp only [dist_zero_right, norm_norm]
  have hb := cross_excision_bound (hx ij.1) (hxn ij.1) (hy ij.2) (hyn ij.2)
    (hym hij.2) a (f (a * y j * star a))
  have hh := hi ij.1 hij.1
  nlinarith [norm_nonneg (x ij.1 * a * y ij.2)]

open Filter Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem strong_zero_of_nondegenerate
    {ι : Type*} {l : Filter ι} (T : ι → (H →L[ℂ] H))
    (hT : ∀ i, ‖T i‖ ≤ 1) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hker : ∀ ξ : H, (∀ b : B, ρ b ξ = 0) → ξ = 0)
    (hr : ∀ b : B, ∀ ξ : H, Tendsto (fun i => T i (ρ b ξ)) l (𝓝 0))
    (ξ : H) : Tendsto (fun i => T i ξ) l (𝓝 0) := by
  let M : Submodule ℂ H :=
    { carrier := {x | Tendsto (fun i => T i x) l (𝓝 0)}
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
        (tendsto_const_nhds (x := (0 : H)))
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_ofPred_eq, map_add, add_zero] using hx.add hy
      smul_mem' := by
        intro z x hx
        simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hx.const_smul z }
  have hEq : Equicontinuous (fun i x => T i x) :=
    (LipschitzWith.uniformEquicontinuous _ 1
      (fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hT i))).equicontinuous
  have hclosed : IsClosed (M : Set H) :=
    hEq.isClosed_setOfPred_tendsto (l := l) continuous_const
  have hbot : Mᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply hker x
    intro b
    have hh := (M.mem_orthogonal x).mp hx (ρ (star b) (ρ b x)) (hr _ _)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hh
    exact inner_self_eq_zero.mp hh
  let : IsClosed (M : Set H) := hclosed
  have htop : M = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
  exact show ξ ∈ M from htop ▸ Submodule.mem_top

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι}

theorem excision_null_mul_tendsto
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (x : ι → A)
    (hx : ∀ i, 0 ≤ x i)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * x i)
      l (𝓝 0)) (b : A) (hb : π (star b) ξ = 0) :
    Tendsto (fun i => x i * b) l (𝓝 0) := by
  have hc : ⟪ξ, π (b * star b) ξ⟫_ℂ = 0 := by
    rw [map_mul, mul_apply_eq_comp, hb, map_zero, inner_zero_right]
  have hsq (i : ι) : ‖x i * b‖ ^ 2 = ‖x i * (b * star b) * x i‖ := by
    rw [pow_two, ← CStarRing.norm_self_mul_star, star_mul,
      (IsSelfAdjoint.of_nonneg (hx i)).star_eq]
    congr 1
    noncomm_ring
  have ht : Tendsto (fun i => ‖x i * b‖ ^ 2) l (𝓝 0) := by
    simpa only [hsq, hc, zero_smul, sub_zero, norm_zero] using (hexc (b * star b)).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveTrace_sandwich (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x a : A) (hx : 0 ≤ x) :
    ‖τ (star a * x * a)‖ ≤ ‖a‖ ^ 2 * ‖τ x‖ := by
  let s := CFC.sqrt x
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)
  have hss : s*s = x := CFC.sqrt_mul_sqrt_self x hx
  have hc : τ (star a*x*a) = τ (s*(a*star a)*s) := by
    rw [← hss]
    calc
      _ = τ ((s*s*a)*star a) := by
        simpa only [mul_assoc] using htr (star a) (s*s*a)
      _ = τ (s*(a*star a)*s) := by
        rw [show s*s*a*star a = s*(s*a*star a) by noncomm_ring,
          htr s (s*a*star a)]
        congr 1
        noncomm_ring
  have hb : s*(a*star a)*s ≤ ‖a‖ ^ 2 • x := by
    have hh := CStarAlgebra.star_left_conjugate_le_norm_smul (a := s) (b := a*star a)
    simpa only [hs.star_eq, hss, CStarRing.norm_self_mul_star, pow_two, mul_assoc] using hh
  have hp : 0 ≤ star a*x*a := star_left_conjugate_nonneg hx a
  have hτx := τ.map_nonneg hx
  rw [← Complex.re_eq_norm.mpr (τ.map_nonneg hp), hc,
    ← Complex.re_eq_norm.mpr hτx]
  have hh := (τ.monotone hb).1
  have hm : τ (‖a‖ ^ 2 • x) = (‖a‖ ^ 2 : ℝ) • τ x := by
    rw [← Complex.coe_smul, map_smul]
    rfl
  change (τ (s*(a*star a)*s)).re ≤ (τ (‖a‖ ^ 2 • x)).re at hh
  rw [hm] at hh
  simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hh

open Filter Topology
open scoped ComplexOrder

theorem positive_dini
    {ι X : Type*} [Preorder ι] [TopologicalSpace X] [CompactSpace X]
    (g : ι → C(X, ℂ)) (hg : ∀ i, 0 ≤ g i) (hm : Antitone g)
    (ht : ∀ t : X, Tendsto (fun i => g i t) atTop (𝓝 0)) :
    Tendsto g atTop (𝓝 0) := by
  let F : ι → C(X, ℝ) := fun i => ⟨fun t => ‖g i t‖, (g i).continuous.norm⟩
  have hF : Antitone F := by
    intro i j hij t
    exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hg j t) (hm hij t)
  have htt : ∀ t : X, Tendsto (fun i => F i t) atTop (𝓝 ((0 : C(X, ℝ)) t)) := by
    intro t
    simpa only [F, ContinuousMap.coe_mk, norm_zero, ContinuousMap.zero_apply] using (ht t).norm
  have hn := (ContinuousMap.tendsto_of_antitone_of_pointwise hF htt).norm
  have hFn (i : ι) : ‖F i‖ = ‖g i‖ := by
    simp only [ContinuousMap.norm_eq_iSup_norm, F, ContinuousMap.coe_mk, norm_norm]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [hFn, norm_zero] using hn

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {p : ℕ → A}
  {f : A →L[ℂ] ℂ}
  (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ)
  (hτ : IsState τ)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}

theorem trace_sandwich_tendsto (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x : ι → A) (hx : ∀ i, 0 ≤ x i)
    (ht : Tendsto (fun i => τ (x i)) l (𝓝 0)) (a : A) :
    Tendsto (fun i => τ (star a * x i * a)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => positiveTrace_sandwich τ htr (x i) a (hx i))
  simpa only [norm_zero,mul_zero] using ht.norm.const_mul (‖a‖^2)

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_exists_unit_fixed {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (hne : P ≠ 0) : ∃ η : H, ‖η‖ = 1 ∧ P η = η := by
  obtain ⟨v, hv⟩ : ∃ v : H, P v ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (ContinuousLinearMap.ext hh)
  let η : H := ‖P v‖⁻¹ • P v
  refine ⟨η, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · change P (‖P v‖⁻¹ • P v) = ‖P v‖⁻¹ • P v
    rw [ContinuousLinearMap.map_smul_of_tower, ← mul_apply_eq_comp, hP.isIdempotentElem.eq]

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem vector_sandwich_tendsto
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (x : ι → A) (a : A)
    (ht : Tendsto (fun i => ρ (x i) (ρ a ξ)) l (𝓝 0)) :
    Tendsto (fun i => ⟪ξ, ρ (star a*x i*a) ξ⟫_ℂ) l (𝓝 0) := by
  have he (i : ι) : ⟪ξ, ρ (star a*x i*a) ξ⟫_ℂ =
      ⟪ρ a ξ, ρ (x i) (ρ a ξ)⟫_ℂ := by
    rw [map_mul,map_mul,map_star, mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp_rw [he]
  simpa only [inner_zero_right] using tendsto_const_nhds.inner ht

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
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

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped CStarAlgebra
section
universe u v
variable {A : Type u} {C : Type v} [CStarAlgebra A] [CStarAlgebra C]

theorem faithfulStarHom_spectrum (π : A →⋆ₐ[ℂ] C) (hπ : Function.Injective π) (a : A) :
    spectrum ℂ (π a) = spectrum ℂ a := by
  let : IsClosed (π.range : Set C) :=
    (NonUnitalStarAlgHom.isometry π hπ).isClosedEmbedding.isClosed_range
  calc
    spectrum ℂ (π a) = spectrum ℂ ((StarAlgEquiv.ofInjective π hπ) a) :=
      (StarSubalgebra.spectrum_eq π.range (a := (StarAlgEquiv.ofInjective π hπ) a)).symm
    _ = spectrum ℂ a := AlgEquiv.spectrum_eq (StarAlgEquiv.ofInjective π hπ) a

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C]

theorem faithfulStarHom_nonneg_iff (π : A →⋆ₐ[ℂ] C) (hπ : Function.Injective π) (a : A) :
    0 ≤ π a ↔ 0 ≤ a := by
  refine ⟨fun hp => ?_, map_nonneg π⟩
  have hpsa : IsSelfAdjoint (π a) := IsSelfAdjoint.of_nonneg hp
  have hsa : IsSelfAdjoint a := by
    apply hπ
    rw [map_star]
    exact hpsa.star_eq
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a hsa).mpr
  intro x hx
  apply spectrum_nonneg_of_nonneg hp
  apply hpsa.coe_mem_spectrum_complex.mp
  rw [faithfulStarHom_spectrum π hπ]
  exact hsa.coe_mem_spectrum_complex.mpr hx

end

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
-- module Solutions.OAIQ115_Naimark.Naimark_DirectLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open UniformSpace Topology
namespace NaimarkZFC
section DirectLimit
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)]

class IsometricStarSystem : Prop where
  isometry : ∀ i j h, Isometry (f i j h)

variable [IsometricStarSystem A f]

instance directLimitNorm : Norm (DirectLimit A f) where
  norm := Quotient.lift (fun x : Sigma A => ‖x.2‖) (by
    intro x y h
    obtain ⟨k,hx,hy,he⟩ := h
    have hf (i j) (h : i ≤ j) (a : A i) : ‖f i j h a‖ = ‖a‖ :=
      (IsometricStarSystem.isometry (A := A) (f := f) i j h).norm_map_of_map_zero
        (map_zero _) a
    rw [← hf x.1 k hx, ← hf y.1 k hy, he])

omit [Nonempty I] in
@[simp] theorem directLimit_norm_mk (i : I) (a : A i) :
    ‖(⟦⟨i,a⟩⟧ : DirectLimit A f)‖ = ‖a‖ := rfl

theorem directLimitNormCore : NormedSpace.Core ℂ (DirectLimit A f) where
  norm_nonneg := DirectLimit.induction f (fun i a => norm_nonneg a)
  norm_smul z := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.smul_def,directLimit_norm_mk,directLimit_norm_mk,norm_smul])
  norm_triangle := DirectLimit.induction₂ f (fun i a b => by
    rw [DirectLimit.add_def,directLimit_norm_mk,directLimit_norm_mk,directLimit_norm_mk]
    exact norm_add_le a b)
  norm_eq_zero_iff := DirectLimit.induction f (fun i a => by
    rw [directLimit_norm_mk,norm_eq_zero]
    constructor
    · intro h
      rw [h,DirectLimit.zero_def i]
    · intro h
      have hh := Quotient.eq.mp h
      obtain ⟨k,ha,hb,he⟩ := hh
      have hz : f i k ha a = 0 := by simpa using he
      exact (IsometricStarSystem.isometry (A := A) (f := f) i k ha).injective
        (hz.trans (map_zero _).symm))

instance directLimitNormedAddCommGroup : NormedAddCommGroup (DirectLimit A f) :=
  NormedAddCommGroup.ofCore (directLimitNormCore A f)

instance directLimitNormedRing : NormedRing (DirectLimit A f) where
  __ : Ring (DirectLimit A f) := inferInstance
  __ : NormedAddCommGroup (DirectLimit A f) := directLimitNormedAddCommGroup A f
  norm_mul_le := DirectLimit.induction₂ f (fun i a b => by
    rw [DirectLimit.mul_def,directLimit_norm_mk,directLimit_norm_mk,directLimit_norm_mk]
    exact norm_mul_le a b)

instance directLimitNormedAlgebra : NormedAlgebra ℂ (DirectLimit A f) where
  norm_smul_le z := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.smul_def,directLimit_norm_mk,directLimit_norm_mk]
    exact norm_smul_le z a)

instance directLimitNormedStarGroup : NormedStarGroup (DirectLimit A f) where
  norm_star_le := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.star_def,directLimit_norm_mk,directLimit_norm_mk,norm_star])

instance directLimitCStarRing : CStarRing (DirectLimit A f) where
  norm_mul_self_le := DirectLimit.induction f (fun i a => by
    rw [DirectLimit.star_def,DirectLimit.mul_def,directLimit_norm_mk,directLimit_norm_mk]
    exact CStarRing.norm_mul_self_le a)

def directLimitInclude (i : I) : A i →⋆ₐ[ℂ] DirectLimit A f where
  toFun a := ⟦⟨i,a⟩⟧
  map_zero' := (DirectLimit.zero_def i).symm
  map_one' := (DirectLimit.one_def i).symm
  map_add' a b := (DirectLimit.add_def i a b).symm
  map_mul' a b := (DirectLimit.mul_def i a b).symm
  map_star' a := (DirectLimit.star_def i a).symm
  commutes' z := (DirectLimit.algebraMap_def i z).symm

omit [IsometricStarSystem A f] in
@[simp] theorem directLimitInclude_compatible (i j : I) (h : i ≤ j) (a : A i) :
    directLimitInclude A f j (f i j h a) = directLimitInclude A f i a :=
  DirectLimit.mk_apply i j a h

end DirectLimit

namespace CStarCompletion
variable (A : Type*) [NormedRing A] [StarRing A] [NormedStarGroup A]

instance instStarCompletion_solutions : Star (Completion A) where
  star := Completion.map (star : A → A)

@[simp] theorem star_coe (a : A) : star (a : Completion A) = (star a : A) :=
  Completion.map_coe star_isometry.uniformContinuous a

instance instContinuousStarCompletion_solutions : ContinuousStar (Completion A) where
  continuous_star := Completion.continuous_map

instance instStarRingCompletion_solutions : StarRing (Completion A) where
  star_involutive x := by
    induction x using Completion.induction_on
    · exact isClosed_eq (by fun_prop) continuous_id
    · rename_i a
      simp only [star_coe,star_star]
  star_mul x y := by
    induction x, y using Completion.induction_on₂
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rename_i a b
      simp only [← Completion.coe_mul,star_coe,star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rename_i a b
      simp only [← Completion.coe_add,star_coe,star_add]

instance instNormedStarGroupCompletion_solutions : NormedStarGroup (Completion A) where
  norm_star_le x := by
    induction x using Completion.induction_on
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · rename_i a
      simp only [star_coe,Completion.norm_coe,norm_star,le_refl]

instance instCStarRingCompletion_solutions [CStarRing A] : CStarRing (Completion A) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · rename_i a
      rw [star_coe,← Completion.coe_mul,Completion.norm_coe,Completion.norm_coe]
      exact CStarRing.norm_mul_self_le a

instance instStarModuleComplexCompletion_solutions [NormedAlgebra ℂ A] [StarModule ℂ A] : StarModule ℂ (Completion A) where
  star_smul z x := by
    induction x using Completion.induction_on
    · exact isClosed_eq (continuous_star.comp (continuous_const_smul z))
        ((continuous_const_smul (star z)).comp continuous_star)
    · rename_i a
      simp only [← Completion.coe_smul,star_coe,star_smul]

instance instNormedAlgebraComplexCompletion_solutions [NormedAlgebra ℂ A] : NormedAlgebra ℂ (Completion A) where
  norm_smul_le := norm_smul_le

instance instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions [CStarRing A] [NormedAlgebra ℂ A] [StarModule ℂ A] :
    CStarAlgebra (Completion A) where
  __ : NormedAlgebra ℂ (Completion A) := inferInstance
  __ : StarModule ℂ (Completion A) := inferInstance

def toCompletion [NormedAlgebra ℂ A] [StarModule ℂ A] : A →⋆ₐ[ℂ] Completion A where
  toFun := (↑)
  map_zero' := Completion.coe_zero
  map_one' := Completion.coe_one A
  map_add' := Completion.coe_add
  map_mul' := Completion.coe_mul
  map_star' a := (star_coe A a).symm
  commutes' z := by simp only [Algebra.algebraMap_eq_smul_one,Completion.coe_smul,Completion.coe_one]

theorem include_isometry [NormedAlgebra ℂ A] [StarModule ℂ A] : Isometry (toCompletion A) :=
  Completion.coe_isometry

theorem include_dense [NormedAlgebra ℂ A] [StarModule ℂ A] : DenseRange (toCompletion A) :=
  Completion.denseRange_coe

end CStarCompletion

section Completion
universe u v w
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]

abbrev CStarDirectLimit := Completion (DirectLimit A f)

def cstarDirectLimitInclude (i : I) : A i →⋆ₐ[ℂ] CStarDirectLimit A f :=
  (CStarCompletion.toCompletion (DirectLimit A f)).comp (directLimitInclude A f i)

@[simp] theorem cstarDirectLimitInclude_compatible (i j : I) (h : i ≤ j) (a : A i) :
    cstarDirectLimitInclude A f j (f i j h a) = cstarDirectLimitInclude A f i a := by
  change (directLimitInclude A f j (f i j h a) : Completion (DirectLimit A f)) = _
  rw [directLimitInclude_compatible]
  rfl

end Completion
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

section
variable {C : Type*} [CStarAlgebra C]

theorem two_end_norm_bound (P d w d' : C) (hP : IsStarProjection P)
    (hw : (1-P)*w*(1-P) = 0) :
    ‖d*w*d'‖ ≤ ‖d*P‖*‖w‖*‖d'‖ + ‖d‖*‖w‖*‖P*d'‖ := by
  have hdecomp : w = P*w+(1-P)*w*P := by
    have hh : w - (P*w+(1-P)*w*P) = (1-P)*w*(1-P) := by noncomm_ring
    rw [hw] at hh
    exact sub_eq_zero.mp hh
  calc
    ‖d*w*d'‖ = ‖d*(P*w)*d'+d*((1-P)*w*P)*d'‖ := by
      conv_lhs => rw [hdecomp]
      rw [mul_add, add_mul]
    _ ≤ ‖d*(P*w)*d'‖+‖d*((1-P)*w*P)*d'‖ := norm_add_le _ _
    _ = ‖(d*P)*w*d'‖+‖(d*(1-P))*w*(P*d')‖ := by simp only [mul_assoc]
    _ ≤ ‖d*P‖*‖w‖*‖d'‖ + ‖d*(1-P)‖*‖w‖*‖P*d'‖ :=
      add_le_add norm_mul₃_le norm_mul₃_le
    _ ≤ ‖d*P‖*‖w‖*‖d'‖ + ‖d‖*‖w‖*‖P*d'‖ := by
      gcongr
      calc
        ‖d*(1-P)‖ ≤ ‖d‖*‖1-P‖ := norm_mul_le _ _
        _ ≤ ‖d‖*1 := mul_le_mul_of_nonneg_left (hP.one_sub.norm_le _) (norm_nonneg _)
        _ = ‖d‖ := mul_one _

end

open Filter Topology
open scoped ComplexOrder

section
variable {C : Type*} [CStarAlgebra C] {ι : Type*} {l : Filter ι}

theorem two_end_tendsto (P w : C) (hP : IsStarProjection P)
    (hw : (1-P)*w*(1-P) = 0) (d e : ι → C) (L R : ℝ)
    (hd : ∀ i, ‖d i‖ ≤ L) (he : ∀ i, ‖e i‖ ≤ R)
    (hlt : Tendsto (fun i => d i*P) l (𝓝 0))
    (hrt : Tendsto (fun i => P*e i) l (𝓝 0)) :
    Tendsto (fun i => d i*w*e i) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (g := fun i => ‖d i*P‖*‖w‖*R+L*‖w‖*‖P*e i‖)
  · intro i
    apply (two_end_norm_bound P (d i) w (e i) hP hw).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (he i) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _))
        (norm_nonneg _))
  · simpa only [norm_zero,zero_mul,mul_zero,zero_add] using
      ((hlt.norm.mul_const ‖w‖).mul_const R).add (hrt.norm.const_mul (L*‖w‖))
end

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
section
variable {F B γ : Type*}
  [CStarAlgebra F]
  [CStarAlgebra B]
  {l : Filter γ}
  (φ : F →⋆ₐ[ℂ] B)
  (b e : Bool → B)
  (P : B)
  (hP : IsStarProjection P)
  (hel : ∀ i, e i*b i = b i)
  (her : ∀ i, b i*e (!i) = b i)
  (hen : ∀ i, ‖e i‖ ≤ 1)
  (K : F → Prop)
include hel her hen hP

omit hel her hen hP

def bridgeZeroPart (f : Bool → F →L[ℂ] ℂ) (tag : Option Bool) (i : Bool) (a : F) : F :=
  if tag = some i then a-f i a • 1 else a

def bridgeScalarPart (f : Bool → F →L[ℂ] ℂ) (tag : Option Bool) (i : Bool) (a : F) : ℂ :=
  if tag = some i then f i a else 0

theorem bridge_four_terms (a c : F) (a' c' : F) (α β : ℂ)
    (ha : a = a'+α • 1) (hc : c = c'+β • 1) (x y w : B) :
    x*φ a*w*φ c*y = (x*φ a'*w*φ c'*y + α • (x*w*φ c'*y)) +
      (β • (x*φ a'*w*y) + (α*β) • (x*w*y)) := by
  rw [ha,hc]
  simp only [map_add,map_smul,map_one,mul_add,add_mul,mul_smul_comm,
    smul_mul_assoc,mul_one,smul_add,smul_smul,mul_comm β α]

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder
theorem top_fst {ι κ : Type*} [Preorder ι] [Preorder κ] :
    Tendsto (Prod.fst : ι × κ → ι) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_fst

theorem top_snd {ι κ : Type*} [Preorder ι] [Preorder κ] :
    Tendsto (Prod.snd : ι × κ → κ) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_snd

theorem top_pair {ι κ μ : Type*} [Preorder ι] [Preorder κ]
    {l : Filter μ} {f : μ → ι} {g : μ → κ}
    (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun k => (f k,g k)) l atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMk hg

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule
section
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem representation_fix_of_coefficient_one
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (x : A) (hx : ‖x‖ ≤ 1) (hcoef : ⟪ξ, π x ξ⟫_ℂ = 1) : π x ξ = ξ := by
  have hbound : ‖π x ξ‖ ≤ 1 := by
    calc
      ‖π x ξ‖ ≤ ‖π x‖*‖ξ‖ := (π x).le_opNorm ξ
      _ ≤ ‖x‖*‖ξ‖ := mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π x)
        (norm_nonneg ξ)
      _ ≤ 1 := by simpa only [hξ,mul_one] using hx
  have hd := norm_sub_sq (𝕜 := ℂ) ξ (π x ξ)
  rw [hξ,hcoef] at hd
  have hz : ‖ξ-π x ξ‖ = 0 := by
    simp only [RCLike.re_to_complex,Complex.one_re,one_pow] at hd
    nlinarith [norm_nonneg (ξ-π x ξ),norm_nonneg (π x ξ)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem representation_coefficient_compression
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (x y a : A)
    (hx : IsSelfAdjoint x) (hfix : π x ξ = ξ) (hyfix : π y η = η) :
    ⟪ξ, π (x*a*y) η⟫_ℂ = ⟪ξ, π a η⟫_ℂ := by
  rw [map_mul,map_mul,mul_apply_eq_comp,mul_apply_eq_comp,hyfix,
    ← ContinuousLinearMap.adjoint_inner_left]
  have hs : (π x).adjoint = π x := by
    change star (π x) = π x
    rw [← map_star,hx.star_eq]
  rw [hs,hfix]

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

section
variable {A C D : Type*} [Ring A] [Ring C] [Ring D]
  (φ : A →+* C) (δ : Bool → D →+* A) (v : Bool → C)

theorem hnn_reverse_conjugacy (hleft : v false*v true = 1)
    (hconj : ∀ d, v true*φ (δ false d)*v false = φ (δ true d))
    (i : Bool) (d : D) : v i*φ (δ (!i) d)*v (!i) = φ (δ i d) := by
  cases i
  · change v false*φ (δ true d)*v true = φ (δ false d)
    rw [← hconj d]
    calc
      _ = (v false*v true)*φ (δ false d)*(v false*v true) := by simp only [mul_assoc]
      _ = _ := by rw [hleft,one_mul,mul_one]
  · exact hconj d

theorem hnn_turn_split (E : Bool → A → D)
    (hconj : ∀ i d, v i*φ (δ (!i) d)*v (!i) = φ (δ i d)) (i : Bool) (a : A) :
    v i*φ a*v (!i) = v i*φ (a-δ (!i) (E (!i) a))*v (!i) + φ (δ i (E (!i) a)) := by
  rw [map_sub,mul_sub,sub_mul,hconj,sub_add_cancel]
end

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

omit [PartialOrder A] [StarOrderedRing A] [l.NeBot] in

theorem map_cross_decay (φ : A →⋆ₐ[ℂ] C) (x y : ι → A) (a : A)
    (ht : Tendsto (fun i => x i*a*y i) l (𝓝 0)) :
    Tendsto (fun i => φ (x i)*φ a*φ (y i)) l (𝓝 0) := by
  simpa only [Function.comp_def,map_zero,map_mul] using ((map_continuous φ).tendsto 0).comp ht

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
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)
  (hKL : ∀ i a, K i a → L i (φ a))
  (F : B →L[ℂ] A) (E : C →L[ℂ] B)
  (hcenter : ∀ b, F b = 0 → ∀ i a c, L i (φ a*b*φ c))
  (hred : ∀ (w : HNNWord B) (b : B), w.Reduced L → E (ψ b*w.eval ψ v) = 0)
  (hleft : ∀ b z, E (ψ b*z) = b*E z) (hright : ∀ z b, E (z*ψ b) = E z*b)

def HNNCenteredBlock (i : Bool) (x : C) : Prop :=
  if i then x ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C)
  else ∃ b : B, F b = 0 ∧ ψ b = x

end

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

section
variable {I R : Type*} [Ring R] [Algebra ℂ R]

variable {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring C] [Algebra ℂ C] (V : I → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (φ : ∀ i, V i →ₐ[ℂ] B) (ψ : ∀ i, V i →ₐ[ℂ] C)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)

def pairedDiagonal : NonUnitalSubalgebra ℂ (B × C) :=
  (b.prod c).range.toNonUnitalSubalgebra

def pairedFactors : I → NonUnitalSubalgebra ℂ (B × C) :=
  fun i => ((φ i).prod (ψ i)).range.toNonUnitalSubalgebra

def pairedCenters : I → Submodule ℂ (B × C) :=
  fun i => (LinearMap.ker (E i)).map ((φ i).prod (ψ i)).toLinearMap

end

section
variable {I R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

variable {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring C] [Algebra ℂ C] (V : I → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (φ : ∀ i, V i →ₐ[ℂ] B) (ψ : ∀ i, V i →ₐ[ℂ] C)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)

def factorCenters : I → Submodule ℂ B :=
  fun i => (LinearMap.ker (E i)).map (φ i).toLinearMap

end

open Topology
open scoped ComplexOrder
section
variable {I A B C : Type*} [Ring A] [Algebra ℂ A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (V : I → Type*) [∀ i, Ring (V i)] [∀ i, StarRing (V i)] [∀ i, Algebra ℂ (V i)]
  (φ : ∀ i, V i →⋆ₐ[ℂ] B) (ψ : ∀ i, V i →⋆ₐ[ℂ] C)

def jointStarModel : StarSubalgebra ℂ (B × C) :=
  StarAlgebra.adjoin ℂ (⋃ i, Set.range ((φ i).prod (ψ i)))

def jointFirst : jointStarModel V φ ψ →⋆ₐ[ℂ] B :=
  (StarAlgHom.fst ℂ B C).comp (jointStarModel V φ ψ).subtype

def jointSecond : jointStarModel V φ ψ →⋆ₐ[ℂ] C :=
  (StarAlgHom.snd ℂ B C).comp (jointStarModel V φ ψ).subtype

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem jointFirst_dense
    (hd : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set B)) :
    DenseRange (jointFirst V φ ψ) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := (jointFirst V φ ψ).range) ?_ hx
  intro y hy
  obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hy
  refine ⟨⟨((φ i).prod (ψ i)) a,StarAlgebra.subset_adjoin ℂ _ ?_⟩,rfl⟩
  exact Set.mem_iUnion.mpr ⟨i,a,rfl⟩

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem jointSecond_dense
    (hd : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (ψ i)) : Set C)) :
    DenseRange (jointSecond V φ ψ) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := (jointSecond V φ ψ).range) ?_ hx
  intro y hy
  obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hy
  refine ⟨⟨((φ i).prod (ψ i)) a,StarAlgebra.subset_adjoin ℂ _ ?_⟩,rfl⟩
  exact Set.mem_iUnion.mpr ⟨i,a,rfl⟩

end

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open UniformSpace
open scoped ComplexOrder
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]
  (τ : ∀ i, A i →L[ℂ] ℂ) (hτ : ∀ i, IsState (τ i))
  (hcompat : ∀ i j h a, τ j (f i j h a) = τ i a)

local instance directLimitNormTopology : TopologicalSpace (DirectLimit A f) :=
  (inferInstance : UniformSpace (DirectLimit A f)).toTopologicalSpace

end

open scoped CStarAlgebra ComplexOrder

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
noncomputable instance hnnGeneratedCStar {A C : Type*}
    [CStarAlgebra A] [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] C) (w : Bool → C) :
    CStarAlgebra (hnnGenerated φ w) := by
  letI : IsClosed (hnnGenerated φ w : Set C) := hnnGenerated_isClosed φ w
  exact StarSubalgebra.cstarAlgebra (hnnGenerated φ w)

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

def CARStage : ℕ → Type
  | 0 => ℂ
  | n+1 => CStarMatrix Bool Bool (CARStage n)

@[instance_reducible] def carStageCStarAux : ∀ n, CStarAlgebra (CARStage n) :=
  Nat.rec (inferInstanceAs (CStarAlgebra ℂ)) (fun n ih => by
    letI : CStarAlgebra (CARStage n) := ih
    letI : PartialOrder (CARStage n) := CStarAlgebra.spectralOrder _
    letI : StarOrderedRing (CARStage n) := CStarAlgebra.spectralOrderedRing _
    exact inferInstanceAs (CStarAlgebra (CStarMatrix Bool Bool (CARStage n))))

instance carStageCStar (n : ℕ) : CStarAlgebra (CARStage n) := carStageCStarAux n

instance carStagePartialOrder (n : ℕ) : PartialOrder (CARStage n) :=
  CStarAlgebra.spectralOrder _
instance carStageStarOrder (n : ℕ) : StarOrderedRing (CARStage n) :=
  CStarAlgebra.spectralOrderedRing _

def matrixScalarHom (A : Type*) [CStarAlgebra A] : A →⋆ₐ[ℂ] CStarMatrix Bool Bool A where
  toFun a := CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => a))
  map_zero' := by change Matrix.diagonal (fun _ : Bool => (0:A)) = 0; simp
  map_one' := by change Matrix.diagonal (fun _ : Bool => (1:A)) = 1; simp
  map_add' a b := by
    change Matrix.diagonal (fun _ : Bool => a+b) =
      Matrix.diagonal (fun _ : Bool => a) + Matrix.diagonal (fun _ : Bool => b)
    exact (Matrix.diagonal_add _ _).symm
  map_mul' a b := by
    change Matrix.diagonal (fun _ : Bool => a*b) = _
    exact (Matrix.diagonal_mul_diagonal _ _).symm
  commutes' z := by
    change Matrix.diagonal (fun _ : Bool => algebraMap ℂ A z) = _
    exact (Matrix.algebraMap_eq_diagonal z).symm
  map_star' a := by
    change Matrix.diagonal (fun _ : Bool => star a) =
      (Matrix.diagonal (fun _ : Bool => a)).conjTranspose
    exact (Matrix.diagonal_conjTranspose _).symm

@[simp] theorem matrixScalarHom_entry (A : Type*) [CStarAlgebra A] (a : A) (i : Bool) :
    (matrixScalarHom A a) i i = a := by simp [matrixScalarHom]

theorem matrixScalarHom_injective (A : Type*) [CStarAlgebra A] :
    Function.Injective (matrixScalarHom A) := by
  intro a b h
  simpa only [matrixScalarHom_entry] using
    congrArg (fun x : CStarMatrix Bool Bool A => x false false) h

theorem matrixScalarHom_isometry (A : Type*) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    Isometry (matrixScalarHom A) :=
  NonUnitalStarAlgHom.isometry _ (matrixScalarHom_injective A)

def carStep (n : ℕ) : CARStage n →⋆ₐ[ℂ] CARStage (n+1) := matrixScalarHom (CARStage n)

def carBond (n m : ℕ) (h : n ≤ m) : CARStage n →⋆ₐ[ℂ] CARStage m :=
  Nat.leRec (StarAlgHom.id ℂ (CARStage n)) (fun {k} _ g => (carStep k).comp g) h

@[simp] theorem carBond_self (n : ℕ) : carBond n n le_rfl = StarAlgHom.id _ _ := by
  simp only [carBond,Nat.leRec_self]

@[simp] theorem carBond_succ (n m : ℕ) (h : n ≤ m) :
    carBond n (m+1) (Nat.le.step h) = (carStep m).comp (carBond n m h) := by
  simp only [carBond,Nat.leRec_succ _ _ h]

theorem carBond_comp (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    (carBond m k hmk).comp (carBond n m hnm) = carBond n k (hnm.trans hmk) := by
  induction hmk with
  | refl => simp
  | @step k hmk ih =>
    rw [carBond_succ m k hmk,carBond_succ n k (hnm.trans hmk),StarAlgHom.comp_assoc,ih]

instance carDirected : DirectedSystem CARStage (fun n m h => carBond n m h) where
  map_self n a := by rw [carBond_self]; rfl
  map_map k m n hnm hmk a := by
    exact congrArg (fun g : CARStage n →⋆ₐ[ℂ] CARStage k => g a) (carBond_comp n m k hnm hmk)

theorem carBond_isometry (n m : ℕ) (h : n ≤ m) : Isometry (carBond n m h) := by
  induction h with
  | refl => rw [carBond_self]; exact isometry_id
  | @step m h ih =>
    rw [carBond_succ n m h]
    exact (matrixScalarHom_isometry (CARStage m)).comp ih

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
variable {A ι : Type*} [CStarAlgebra A]

def generatedFamily (base : Set A) (v : ι → A) (S : Set ι) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ (base ∪ v '' S)).topologicalClosure

theorem generatedFamily_mono (base : Set A) (v : ι → A) :
    Monotone (generatedFamily base v) := by
  intro S T h
  exact StarSubalgebra.topologicalClosure_mono
    (StarAlgebra.adjoin_mono (Set.union_subset_union_right base (Set.image_mono h)))

theorem generatedFamily_isClosed (base : Set A) (v : ι → A) (S : Set ι) :
    IsClosed (generatedFamily base v S : Set A) := isClosed_closure

theorem generatedFamily_contains_base (base : Set A) (v : ι → A) (S : Set ι) :
    base ⊆ generatedFamily base v S :=
  fun _ h => subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl h))

theorem generatedFamily_contains (base : Set A) (v : ι → A) {S : Set ι} {j : ι}
    (hj : j ∈ S) : v j ∈ generatedFamily base v S :=
  subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨j,hj,rfl⟩))

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

section
variable {ι : Type*}

def DependencyClosed (I : ι → Set ι) (S : Set ι) : Prop := ∀ j ∈ S, I j ⊆ S

end

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra InnerProductSpace

open Filter Topology
open scoped CStarAlgebra

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open Filter Topology
open scoped InnerProductSpace

open Topology
section
variable {A ι κ : Type*} [CStarAlgebra A]

theorem generatedFamily_iUnion_directed [Nonempty κ]
    (base : Set A) (v : ι → A) (N : κ → Set ι) (hN : Directed (· ⊆ ·) N) :
    (generatedFamily base v (⋃ k, N k) : Set A) =
      closure (⋃ k, (generatedFamily base v (N k) : Set A)) := by
  let C : StarSubalgebra ℂ A := (⨆ k, generatedFamily base v (N k)).topologicalClosure
  have hd : Directed (· ≤ ·) (fun k => generatedFamily base v (N k)) :=
    fun i j => by
      obtain ⟨k,hik,hjk⟩ := hN i j
      exact ⟨k,generatedFamily_mono base v hik,generatedFamily_mono base v hjk⟩
  have hcoe : (C : Set A) = closure (⋃ k, (generatedFamily base v (N k) : Set A)) := by
    change closure (((⨆ k, generatedFamily base v (N k)) : StarSubalgebra ℂ A) : Set A) = _
    rw [StarSubalgebra.coe_iSup_of_directed hd]
  apply Set.Subset.antisymm
  · rw [← hcoe]
    change generatedFamily base v (⋃ k, N k) ≤ C
    apply StarSubalgebra.topologicalClosure_minimal _
      (show IsClosed (C : Set A) from isClosed_closure)
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | ⟨j,hj,rfl⟩
    · let k : κ := Classical.arbitrary κ
      exact subset_closure ((le_iSup (fun k => generatedFamily base v (N k)) k)
        (generatedFamily_contains_base base v (N k) hx))
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hj
      exact subset_closure ((le_iSup (fun k => generatedFamily base v (N k)) k)
        (generatedFamily_contains base v hk))
  · apply closure_minimal _ (generatedFamily_isClosed base v _)
    exact Set.iUnion_subset fun k => generatedFamily_mono base v (Set.subset_iUnion N k)

universe u

theorem dense_iUnion_starSubalgebra_inclusions
    (S : StarSubalgebra ℂ A) (T : κ → StarSubalgebra ℂ A) (hT : ∀ k, T k ≤ S)
    (he : (S : Set A) = closure (⋃ k, (T k : Set A))) :
    Dense (⋃ k, Set.range (StarSubalgebra.inclusion (hT k))) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx : (x:A) ∈ closure (⋃ k, (T k : Set A)) := by rw [← he]; exact x.property
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hy
  refine ⟨⟨y,hT k hk⟩,Set.mem_iUnion.mpr ⟨k,⟨y,hk⟩,rfl⟩,?_⟩
  exact hxy

end

open Topology
section
attribute [local instance] generatedFamily_isClosed
universe u
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (base : Set A) (v : Ordinal.{u} → A) (S : Set Ordinal.{u})

omit [PartialOrder A] [StarOrderedRing A] in
theorem starSubalgebra_inclusion_comp (X Y Z : StarSubalgebra ℂ A)
    (h : X ≤ Y) (h' : Y ≤ Z) :
    (StarSubalgebra.inclusion h').comp (StarSubalgebra.inclusion h) =
      StarSubalgebra.inclusion (h.trans h') := rfl

def retainedOrdinalAlgebra (j : Ordinal.{u}) : StarSubalgebra ℂ A :=
  generatedFamily base v (S ∪ Set.Iio j)

instance retainedOrdinalAlgebra_isClosed (j : Ordinal.{u}) :
    IsClosed (retainedOrdinalAlgebra base v S j : Set A) := generatedFamily_isClosed _ _ _

noncomputable instance retainedOrdinalAlgebra_cstar (j : Ordinal.{u}) :
    CStarAlgebra (retainedOrdinalAlgebra base v S j) :=
  StarSubalgebra.cstarAlgebra _

local instance retainedOrdinalAlgebra_order (j : Ordinal.{u}) :
    PartialOrder (retainedOrdinalAlgebra base v S j) :=
  CStarAlgebra.spectralOrder _
local instance retainedOrdinalAlgebra_starOrder (j : Ordinal.{u}) :
    StarOrderedRing (retainedOrdinalAlgebra base v S j) :=
  CStarAlgebra.spectralOrderedRing _

def retainedOrdinalInclusion {i j : Ordinal.{u}} (h : i ≤ j) :
    retainedOrdinalAlgebra base v S i →⋆ₐ[ℂ] retainedOrdinalAlgebra base v S j :=
  StarSubalgebra.inclusion (generatedFamily_mono base v (Set.union_subset_union_right S
    (fun _ hx => lt_of_lt_of_le hx h)))

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_injective {i j : Ordinal.{u}} (h : i ≤ j) :
    Function.Injective (retainedOrdinalInclusion base v S h) := by
  exact StarSubalgebra.inclusion_injective _

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_comp {i j k : Ordinal.{u}} (h : i ≤ j) (h' : j ≤ k) :
    (retainedOrdinalInclusion base v S h').comp (retainedOrdinalInclusion base v S h) =
      retainedOrdinalInclusion base v S (h.trans h') :=
  starSubalgebra_inclusion_comp _ _ _ _ _

omit [PartialOrder A] [StarOrderedRing A] in

theorem retainedOrdinalSucc_eq_of_mem (j : Ordinal.{u}) (hj : j ∈ S) :
    retainedOrdinalAlgebra base v S (j+1) = retainedOrdinalAlgebra base v S j := by
  apply congrArg (generatedFamily base v)
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show x < j+1 from hx)) with hx | rfl
      · exact Or.inr hx
      · exact Or.inl hj
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (show x < j+1 from (show x < j from hx).trans_le le_self_add)

end

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Homogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Filter Topology
open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open Topology
section
variable {A C D ι : Type*} [CStarAlgebra A] [CStarAlgebra C] [CStarAlgebra D]

def starPair (a : A) : Bool → A
  | false => a
  | true => star a

@[simp] lemma starPair_false (a : A) : starPair a false = a := rfl
@[simp] lemma starPair_true (a : A) : starPair a true = star a := rfl

lemma map_hnnGenerated (φ : C →⋆ₐ[ℂ] D) (w : Bool → D) (ψ : D →⋆ₐ[ℂ] A)
    (hψ : Function.Injective ψ) :
    (hnnGenerated φ w).map ψ = hnnGenerated (ψ.comp φ) (fun i => ψ (w i)) := by
  have hcont := (NonUnitalStarAlgHom.isometry ψ hψ).continuous
  have hclosed := (NonUnitalStarAlgHom.isometry ψ hψ).isClosedEmbedding.isClosedMap
  rw [hnnGenerated,← StarSubalgebra.topologicalClosure_map _ ψ hclosed hcont,
    StarAlgHom.map_adjoin,hnnGenerated]
  congr 2
  rw [Set.image_union,← Set.range_comp,← Set.range_comp]
  rfl

lemma hnnGenerated_self (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (a : A) : hnnGenerated S.subtype (starPair a) =
      (StarAlgebra.adjoin ℂ ((S : Set A) ∪ {a})).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal _ isClosed_closure
    apply StarAlgebra.adjoin_le
    rintro x (⟨s,rfl⟩ | ⟨i,rfl⟩)
    · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl s.property))
    · cases i
      · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton a)))
      · exact star_mem (subset_closure (StarAlgebra.subset_adjoin ℂ _
          (Or.inr (Set.mem_singleton a))))
  · apply StarSubalgebra.topologicalClosure_minimal _ (hnnGenerated_isClosed _ _)
    apply StarAlgebra.adjoin_le
    rintro x (hx | hx)
    · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨⟨x,hx⟩,rfl⟩))
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨false,rfl⟩))

lemma generatedFamily_insert (base : Set A) (v : ι → A) (S : Set ι) (j : ι) :
    generatedFamily base v (insert j S) =
      (StarAlgebra.adjoin ℂ ((generatedFamily base v S : Set A) ∪ {v j})).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal _ isClosed_closure
    apply StarAlgebra.adjoin_le
    rintro x (hx | ⟨k,hk,rfl⟩)
    · exact subset_closure (StarAlgebra.subset_adjoin ℂ _
        (Or.inl (generatedFamily_contains_base base v S hx)))
    · rcases hk with rfl | hk
      · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton _)))
      · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl (generatedFamily_contains base v hk)))
  · apply StarSubalgebra.topologicalClosure_minimal _ (generatedFamily_isClosed _ _ _)
    apply StarAlgebra.adjoin_le
    rintro x (hx | hx)
    · exact generatedFamily_mono base v (Set.subset_insert j S) hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact generatedFamily_contains base v (Set.mem_insert j S)

attribute [local instance] generatedFamily_isClosed

lemma hnnGenerated_eq_insert (base : Set A) (v : ι → A) (S : Set ι) (j : ι) :
    hnnGenerated (generatedFamily base v S).subtype (starPair (v j)) =
      generatedFamily base v (insert j S) := by
  rw [hnnGenerated_self,generatedFamily_insert]

end

open Topology

lemma StarAlgHom.equivClosedRange {B A : Type*} [CStarAlgebra B] [CStarAlgebra A]
    (φ : B →⋆ₐ[ℂ] A) (hφ : Function.Injective φ) (S : StarSubalgebra ℂ A)
    (hS : φ.range = S) :
    ∃ e : B ≃⋆ₐ[ℂ] S, ∀ b, (e b : A) = φ b := by
  let f : B →⋆ₐ[ℂ] S := φ.codRestrict S (fun b => by rw [← hS]; exact ⟨b,rfl⟩)
  have hfi : Function.Injective f := fun x y h => hφ (congrArg Subtype.val h)
  have hfs : Function.Surjective f := by
    intro y
    have hy : (y:A) ∈ φ.range := by rw [hS]; exact y.property
    obtain ⟨b,hb⟩ := hy
    exact ⟨b,Subtype.ext hb⟩
  exact ⟨StarAlgEquiv.ofBijective f ⟨hfi,hfs⟩,fun _ => rfl⟩

lemma StarAlgHom.range_comp_eq_map {A B C : Type*} [CStarAlgebra A]
    [CStarAlgebra B] [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) :
    (ψ.comp φ).range = φ.range.map ψ := by
  ext c
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨φ a,⟨a,rfl⟩,rfl⟩
  · rintro ⟨b,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
local instance ambientSubalgebraOrder {A : Type} [CStarAlgebra A]
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : PartialOrder S :=
  CStarAlgebra.spectralOrder S
local instance ambientSubalgebraStarOrder {A : Type} [CStarAlgebra A]
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S :=
  CStarAlgebra.spectralOrderedRing S

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
section
universe u
variable {A : Type} [CStarAlgebra A]

def omittedIndices (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) : Set Ordinal.{u} :=
  Set.Iio j ∪ (S ∩ Set.Iio β)

lemma omittedIndices_mono (j : Ordinal.{u}) (S : Set Ordinal.{u}) :
    Monotone (omittedIndices j S) := by
  intro β γ h k hk
  rcases hk with hk | ⟨hk,hk'⟩
  · exact Or.inl hk
  · exact Or.inr ⟨hk,hk'.trans_le h⟩

lemma omittedIndices_succ (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hk : k ∈ S) : omittedIndices j S (k+1) = insert k (omittedIndices j S k) := by
  ext x
  constructor
  · rintro (hx | ⟨hx,hx'⟩)
    · exact Or.inr (Or.inl hx)
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show x < k+1 from hx')) with hd | rfl
      · exact Or.inr (Or.inr ⟨hx,hd⟩)
      · exact Or.inl rfl
  · rintro (rfl | (hx | ⟨hx,hx'⟩))
    · exact Or.inr ⟨hk,show x < x+1 from Order.lt_succ x⟩
    · exact Or.inl hx
    · exact Or.inr ⟨hx,show x < k+1 from (show x < k from hx').trans_le le_self_add⟩

lemma omittedIndices_succ_of_not_mem (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hk : k ∉ S) : omittedIndices j S (k+1) = omittedIndices j S k := by
  apply Set.Subset.antisymm
  · rintro x (hx | ⟨hx,hx'⟩)
    · exact Or.inl hx
    · right
      refine ⟨hx,show x < k from lt_of_le_of_ne (Order.lt_add_one_iff.mp (show x < k+1 from hx')) ?_⟩
      intro he; exact hk (he ▸ hx)
  · exact omittedIndices_mono j S le_self_add

lemma omittedIndices_succ_of_lt (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hk : k < j) : omittedIndices j S (k+1) = omittedIndices j S k := by
  apply Set.Subset.antisymm
  · rintro x (hx | ⟨hx,hx'⟩)
    · exact Or.inl hx
    · exact Or.inl (lt_of_le_of_lt (Order.lt_add_one_iff.mp (show x < k+1 from hx')) hk)
  · exact omittedIndices_mono j S le_self_add

lemma omittedIndices_subset_Iio (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u})
    (hj : j ≤ k) : omittedIndices j S k ⊆ Set.Iio k := by
  rintro x (hx | ⟨_,hx⟩)
  · exact hx.trans_le hj
  · exact hx

lemma omittedIndices_insert_eq (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    insert j (omittedIndices j S β) = omittedIndices (j+1) S β := by
  ext k
  constructor
  · rintro (rfl | (hk | hk))
    · exact Or.inl (show k < k+1 from Order.lt_succ k)
    · exact Or.inl (show k < j+1 from (show k < j from hk).trans_le le_self_add)
    · exact Or.inr hk
  · rintro (hk | hk)
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show k < j+1 from hk)) with hk | rfl
      · exact Or.inr (Or.inl hk)
      · exact Or.inl rfl
    · exact Or.inr (Or.inr hk)

lemma omittedIndices_iUnion (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) :
    (⋃ k : {k : Ordinal.{u} // k < β}, omittedIndices j S k.val) = omittedIndices j S β := by
  have h0 : (0 : Ordinal.{u}) < β := hβ.ne_bot.bot_lt
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    exact omittedIndices_mono j S k.property.le hk
  · rintro (hx | ⟨hx,hx'⟩)
    · exact Set.mem_iUnion.mpr ⟨⟨0,h0⟩,Or.inl hx⟩
    · exact Set.mem_iUnion.mpr ⟨⟨Order.succ x,hβ.succ_lt hx'⟩,
        Or.inr ⟨hx,Order.lt_succ x⟩⟩

def omittedAlgebra (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) : StarSubalgebra ℂ A :=
  generatedFamily base v (omittedIndices j S β)

instance omittedAlgebra_isClosed (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    IsClosed (omittedAlgebra base v j S β : Set A) := generatedFamily_isClosed _ _ _

noncomputable instance omittedAlgebra_cstar (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    CStarAlgebra (omittedAlgebra base v j S β) := StarSubalgebra.cstarAlgebra _

lemma omittedAlgebra_mono (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) : Monotone (omittedAlgebra base v j S) :=
  (generatedFamily_mono base v).comp (omittedIndices_mono j S)

lemma omittedAlgebra_hnnGenerated (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    hnnGenerated (omittedAlgebra base v j S β).subtype (starPair (v j)) =
      omittedAlgebra base v (j+1) S β := by
  rw [hnnGenerated_self]
  exact (generatedFamily_insert base v (omittedIndices j S β) j).symm.trans
    (congrArg (generatedFamily base v) (omittedIndices_insert_eq j S β))

lemma omittedAlgebra_continuous (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) (hβ : Order.IsSuccLimit β) :
    (omittedAlgebra base v j S β : Set A) =
      closure (⋃ k : {k : Ordinal.{u} // k < β}, (omittedAlgebra base v j S k.val : Set A)) := by
  let K := {k : Ordinal.{u} // k < β}
  let : Nonempty K := ⟨⟨0,hβ.ne_bot.bot_lt⟩⟩
  have hd : Directed (· ⊆ ·) (fun k : K => omittedIndices j S k.val) := by
    intro k l
    exact ⟨⟨max k.val l.val,max_lt k.property l.property⟩,
      omittedIndices_mono j S (le_max_left _ _),omittedIndices_mono j S (le_max_right _ _)⟩
  change (generatedFamily base v (omittedIndices j S β) : Set A) = _
  rw [← omittedIndices_iUnion j S β hβ]
  exact generatedFamily_iUnion_directed base v _ hd

end

open Topology
section
universe u
variable {A : Type} [CStarAlgebra A]

lemma hnnGenerated_eq_of_mem (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (z : A) (hz : z ∈ S) : hnnGenerated S.subtype (starPair z) = S := by
  rw [hnnGenerated_self]
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal _ (inferInstance : IsClosed (S : Set A))
    apply StarAlgebra.adjoin_le
    rintro x (hx | hx)
    · exact hx
    · exact Set.mem_singleton_iff.mp hx ▸ hz
  · intro x hx
    exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl hx))

lemma omittedAlgebra_base_mono (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (β : Ordinal.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) :
    omittedAlgebra base v i S β ≤ omittedAlgebra base v j S β := by
  apply generatedFamily_mono
  apply Set.union_subset_union_left
  exact fun _ hx => (show _ < i from hx).trans_le hij

lemma omittedAlgebra_le_chronological (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) (hj : j ≤ β) :
    omittedAlgebra base v j S β ≤ generatedFamily base v (Set.Iio β) :=
  generatedFamily_mono base v (omittedIndices_subset_Iio j S β hj)

lemma omittedAlgebra_contains_initial (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) :
    generatedFamily base v (Set.Iio j) ≤ omittedAlgebra base v j S β :=
  generatedFamily_mono base v Set.subset_union_left

lemma omittedAlgebra_succ_of_not_mem (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hk : k ∉ S) :
    omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k :=
  congrArg (generatedFamily base v) (omittedIndices_succ_of_not_mem j S k hk)

lemma omittedAlgebra_succ_of_lt (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hk : k < j) :
    omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k :=
  congrArg (generatedFamily base v) (omittedIndices_succ_of_lt j S k hk)

lemma omittedAlgebra_succ (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hk : k ∈ S) :
    omittedAlgebra base v j S (k+1) =
      hnnGenerated (omittedAlgebra base v j S k).subtype (starPair (v k)) := by
  rw [hnnGenerated_self]
  exact (congrArg (generatedFamily base v) (omittedIndices_succ j S k hk)).trans
    (generatedFamily_insert base v (omittedIndices j S k) k)

lemma omittedAlgebra_succ_of_one (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (k : Ordinal.{u}) (hv : v k = 1) :
    omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k := by
  classical
  by_cases hk : k ∈ S
  · rw [omittedAlgebra_succ base v j S k hk]
    exact hnnGenerated_eq_of_mem _ _ (hv ▸ (omittedAlgebra base v j S k).one_mem)
  · exact omittedAlgebra_succ_of_not_mem base v j S k hk

end

open Topology
section
variable {A : Type*} [CStarAlgebra A]

lemma dense_subalgebra_inclusion_ranges {I : Type*}
    (S : I → StarSubalgebra ℂ A) (V : StarSubalgebra ℂ A) (hSV : ∀ i, S i ≤ V)
    (hcont : (V : Set A) = closure (⋃ i, (S i : Set A))) :
    Dense (⋃ i, Set.range (StarSubalgebra.inclusion (hSV i))) := by
  have he : (⋃ i, Set.range (StarSubalgebra.inclusion (hSV i))) =
      (Subtype.val : V → A) ⁻¹' (⋃ i, (S i : Set A)) := by
    ext a
    simp only [Set.mem_iUnion,Set.mem_range,Set.mem_preimage]
    constructor
    · rintro ⟨i,b,rfl⟩
      exact ⟨i,b.property⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,⟨a,hi⟩,rfl⟩
  rw [he]
  intro a
  have hsub : (⋃ i, (S i : Set A)) ⊆ (V : Set A) := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact hSV i hi
  rw [closure_subtype]
  have himg : (Subtype.val : V → A) '' ((Subtype.val : V → A) ⁻¹' (⋃ i, (S i : Set A))) =
      ⋃ i, (S i : Set A) := by
    exact Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x,hsub hx⟩,rfl⟩)
  rw [himg]
  rw [← hcont]
  exact a.property

end

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma subalgebra_inclusion_ranges_directed [PartialOrder A] [StarOrderedRing A] (S : Ordinal.{u} → StarSubalgebra ℂ A)
    (hmono : Monotone S) (β : Ordinal.{u}) :
    Directed (· ⊆ ·) (fun k : Set.Iio β =>
      Set.range (StarSubalgebra.inclusion (hmono k.property.le))) := by
  intro k l
  let m : Set.Iio β := ⟨max k.val l.val,max_lt (show k.val < β from k.property) (show l.val < β from l.property)⟩
  refine ⟨m,?_,?_⟩
  · rintro a ⟨b,rfl⟩
    exact ⟨⟨b,hmono (le_max_left k.val l.val) b.property⟩,rfl⟩
  · rintro a ⟨b,rfl⟩
    exact ⟨⟨b,hmono (le_max_right k.val l.val) b.property⟩,rfl⟩

end PeakingPairData

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (base : Set A)
  (v : Ordinal.{u} → A)
  (active S : Set Ordinal.{u})
  (δ j : Ordinal.{u})
  (hj : j < δ)
  (hja : j ∈ active)
  (hjS : j ∉ S)
  (hinactive : ∀ k < δ, k ∉ active → v k = 1)

lemma ordinal_invariant (F : Ordinal.{u} → Prop) (δ : Ordinal.{u})
    (h0 : F 0) (hs : ∀ k < δ, F k → F (k+1))
    (hl : ∀ β ≤ δ, Order.IsSuccLimit β → (∀ k < β, F k) → F β)
    (β : Ordinal.{u}) (hβ : β ≤ δ) : F β := by
  induction β using Ordinal.limitRecOn with
  | zero => exact h0
  | add_one k ih =>
    have hk : k < δ := (Order.lt_succ k).trans_le hβ
    exact hs k hk (ih hk.le)
  | limit β hlim ih => exact hl β hβ hlim (fun k hk => ih k hk (hk.le.trans hβ))

end

end PeakingPairData

open Topology

open Topology

section
open Topology
universe u
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma omittedAlgebra_all_before (base : Set A) (v : Ordinal.{u} → A)
    (δ k : Ordinal.{u}) (hk : k ≤ δ) :
    omittedAlgebra base v 0 (Set.Iio δ) k = generatedFamily base v (Set.Iio k) := by
  apply congrArg (generatedFamily base v)
  ext x
  simp only [omittedIndices,Set.mem_union,Set.mem_Iio,not_lt_zero,false_or,Set.mem_inter_iff]
  exact ⟨And.right,fun hx => ⟨hx.trans_le hk,hx⟩⟩

lemma omittedAlgebra_endpoint_eq_retained (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hS : S ⊆ Set.Iio δ) :
    omittedAlgebra base v j S δ = retainedOrdinalAlgebra base v S j := by
  apply congrArg (generatedFamily base v)
  ext x
  constructor
  · rintro (hx | ⟨hx,_⟩)
    · exact Or.inr hx
    · exact Or.inl hx
  · rintro (hx | hx)
    · exact Or.inr ⟨hx,hS hx⟩
    · exact Or.inl hx

lemma retainedOrdinal_succ_generated (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (j : Ordinal.{u}) :
    retainedOrdinalAlgebra base v S (j+1) =
      hnnGenerated (retainedOrdinalAlgebra base v S j).subtype (starPair (v j)) := by
  change generatedFamily base v (S ∪ Set.Iio (j+1)) =
    hnnGenerated (generatedFamily base v (S ∪ Set.Iio j)).subtype (starPair (v j))
  rw [hnnGenerated_eq_insert]
  apply congrArg (generatedFamily base v)
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inr (Or.inl hx)
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show x < j+1 from hx)) with hx | rfl
      · exact Or.inr (Or.inr hx)
      · exact Or.inl rfl
  · rintro (rfl | (hx | hx))
    · exact Or.inr (show x < x+1 from Order.lt_succ x)
    · exact Or.inl hx
    · exact Or.inr (show x < j+1 from (show x < j from hx).trans_le le_self_add)

lemma retainedOrdinal_succ_of_one (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (j : Ordinal.{u}) (hv : v j = 1) :
    retainedOrdinalAlgebra base v S (j+1) = retainedOrdinalAlgebra base v S j := by
  rw [retainedOrdinal_succ_generated]
  exact hnnGenerated_eq_of_mem _ _ (hv ▸ (retainedOrdinalAlgebra base v S j).one_mem)

end

open Topology

section
universe u
variable {A : Type} [CStarAlgebra A]

lemma generatedFamily_Iio_mono (base : Set A) (v : Ordinal.{u} → A) :
    Monotone (fun k : Ordinal.{u} => generatedFamily base v (Set.Iio k)) :=
  fun _ _ h => generatedFamily_mono base v (fun _ hk => hk.trans_le h)

end

open Topology

open Topology

open Topology

open Topology

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open Topology
section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

def closedMapEquiv (S : StarSubalgebra ℂ A) (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) : S ≃⋆ₐ[ℂ] S.map φ :=
  StarAlgEquiv.ofBijective
    ((φ.comp S.subtype).codRestrict (S.map φ) (fun a => ⟨a,a.property,rfl⟩))
    ⟨fun a b h => Subtype.ext (hφ (congrArg Subtype.val h)), by
      rintro ⟨b,a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩⟩

end

open Topology

open Topology

open Topology

open Topology

open CategoryTheory

open CategoryTheory

open CategoryTheory Topology

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory Cardinal Classical

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct

open Cardinal Ordinal

open CategoryTheory Topology

open CategoryTheory Cardinal

universe u v w

end NaimarkZFC

end

end OAI
end


