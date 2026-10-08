-- Prove2me | Definitions.Def_CharacterCriterion
-- name    : CharacterCriterion
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.722708+00:00
-- url     : https://prove2.me/theorems/115659f3-81f2-4e78-9ee9-dc12205a4624
-- statement:
--   For a complex unital C*-algebra A and any ultrafilter ω on ℕ, the norm ultrapower Aω is the algebra of bounded A-valued sequences modulo those whose norms converge to zero along ω. The construction establishes that this is a C*-algebra with ‖[x]‖ = limω ‖xₙ‖; replacing terms of norm at least c by zero preserves the class whenever c exceeds this limit. Constant sequences give the diagonal map A → Aω, and CentralAlgebra(A,ω) is its closed commutant, also a C*-algebra. HasNoCharacters(A) is the defined proposition that every complex-linear, multiplicative, involution-preserving map A → ℂ, without a unit-preservation requirement, is zero. Supporting constructions extend involutions to completions and form C*-inductive limits by completing algebraic direct limits of sequences of unital *-homomorphisms assumed to preserve norms. Tensor-product constructions introduce submultiplicative *-invariant seminorms satisfying p(x*x) = p(x)² and p(a ⊗ b) ≤ ‖a‖‖b‖, and obtain such seminorms from pairs of commuting representations. The defined minimal tensor product is the completion for the supremum, including zero, of operator seminorms arising from representations on separate complex Hilbert spaces and their Hilbert-space tensor product. For arbitrary nonnegative integers p,q, the dimension-drop algebra I(p,q) consists of continuous functions f: [0,1] → Mₚq(ℂ) with f(0) in Mₚ(ℂ) ⊗ 1q and f(1) in 1p ⊗ Mq(ℂ); it is closed and hence a C*-algebra. Matrix block sums, tensor embeddings, index rearrangements, and unitary paths between permutation matrices construct connecting maps by conjugating diagonal blocks evaluating f at t/2, (t+1)/2, and 1/2. General connecting data from I(p,q) to I(P,Q) assume multiplicities L,U>0 and M,a,b,c,d≥0 satisfying qL=aQ, U+M=bQ, pU=Pc, L+M=Pd, pa+pqb=P, and qc+pqd=Q. These equations ensure the endpoint conditions, while the two nonconstant evaluation paths cover [0,1], making the connecting maps injective and norm-preserving. A prime-drop presentation additionally assumes stage parameters pₙ=2^(eₙ+1) and endpoint copy bounds a+(pₙ+1)b≥2 and c+pₙd≥2. The explicit presentation starts with p₀=2 and pₙ₊₁=pₙ⁷, so pₙ=2^(7ⁿ). At a stage p≥2, put k=(p−1)(p⁴+p²+1); its three evaluation multiplicities are pk+1, (p+1)k+1, and p(p+1)k²−1, with a=c=1 and b=d=k. The algebra named JiangSu.Algebra is defined as the completed inductive limit of these I(pₙ,pₙ+1) stages and connecting maps.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CharacterCriterion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CharacterCriterion.lean; bytes 16..135077
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
protected theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

/-!
# Character criterion for Jiang–Su absorption

The main statement is Theorem 1.1 of the Kirchberg–Rørdam character-criterion paper.
The constructions below specify the norm central-sequence algebra and Jiang–Su absorption.
-/

namespace OAI

noncomputable section

section

open scoped TensorProduct InnerProductSpace BigOperators
open Set Module

universe uQuot
namespace KirchbergRordam.QuotientNormSupport

@[instance_reducible]
noncomputable def normedRing {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
    [IsClosed (I : Set R)] : NormedRing (R ⧸ I) := by
  classical
  have h_QuotientNormSupport_distance_eq  {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
      [IsClosed (I : Set R)] (x y : R ⧸ I) :
      dist x y = ‖-x + y‖ := dist_eq_norm_neg_add x y
  have h_QuotientNormSupport_multiplication_bound  {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
      [IsClosed (I : Set R)] (x y : R ⧸ I) :
      ‖x * y‖ ≤ ‖x‖ * ‖y‖ := le_of_forall_pos_le_add fun ε hε =>
    let neighborhood : ∃ radii : ℝ × ℝ, (0 < radii.1 ∧ 0 < radii.2) ∧
      ∀ point : ℝ × ℝ, (dist point.1 ‖x‖ < radii.1 ∧ dist point.2 ‖y‖ < radii.2) →
        dist (point.1 * point.2) (‖x‖ * ‖y‖) < ε :=
      ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
        Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    neighborhood.elim fun radii radii_spec =>
      (Submodule.Quotient.norm_mk_lt x radii_spec.1.1).elim fun representative_x x_spec =>
        (Submodule.Quotient.norm_mk_lt y radii_spec.1.2).elim fun representative_y y_spec =>
          let lower_x : ‖x‖ ≤ ‖representative_x‖ :=
            Eq.mp (congrArg (fun value : R ⧸ I => ‖value‖ ≤ ‖representative_x‖) x_spec.1)
              (Submodule.Quotient.norm_mk_le I representative_x)
          let lower_y : ‖y‖ ≤ ‖representative_y‖ :=
            Eq.mp (congrArg (fun value : R ⧸ I => ‖value‖ ≤ ‖representative_y‖) y_spec.1)
              (Submodule.Quotient.norm_mk_le I representative_y)
          let distance_x : dist ‖representative_x‖ ‖x‖ < radii.1 :=
            Eq.mpr (congrArg (fun distance : ℝ => distance < radii.1)
              (Real.dist_eq ‖representative_x‖ ‖x‖))
                (abs_sub_lt_iff.mpr ⟨sub_lt_iff_lt_add'.mpr x_spec.2,
                  (sub_nonpos.mpr lower_x).trans_lt radii_spec.1.1⟩)
          let distance_y : dist ‖representative_y‖ ‖y‖ < radii.2 :=
            Eq.mpr (congrArg (fun distance : ℝ => distance < radii.2)
              (Real.dist_eq ‖representative_y‖ ‖y‖))
                (abs_sub_lt_iff.mpr ⟨sub_lt_iff_lt_add'.mpr y_spec.2,
                  (sub_nonpos.mpr lower_y).trans_lt radii_spec.1.2⟩)
          let product_distance :=
            radii_spec.2 (‖representative_x‖, ‖representative_y‖) ⟨distance_x, distance_y⟩
          let product_bound : ‖x * y‖ ≤ ‖representative_x‖ * ‖representative_y‖ :=
            Eq.mp (congrArg₂ (fun left right : R ⧸ I =>
              ‖left * right‖ ≤ ‖representative_x‖ * ‖representative_y‖) x_spec.1 y_spec.1)
                ((Submodule.Quotient.norm_mk_le I (representative_x * representative_y)).trans
                  (norm_mul_le representative_x representative_y))
          product_bound.trans (sub_lt_iff_lt_add'.mp (abs_sub_lt_iff.mp
            (Eq.mp (congrArg (fun distance : ℝ => distance < ε)
              (Real.dist_eq (‖representative_x‖ * ‖representative_y‖) (‖x‖ * ‖y‖)))
                product_distance)).1).le
  exact {
    toNorm := inferInstance
    toRing := inferInstance
    toMetricSpace := inferInstance
    dist_eq := h_QuotientNormSupport_distance_eq I
    norm_mul_le := h_QuotientNormSupport_multiplication_bound I
  }

end KirchbergRordam.QuotientNormSupport

end

open scoped TensorProduct CStarAlgebra InnerProductSpace Matrix Kronecker ComplexOrder
open UniformSpace Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam.NormUltrapower

variable {A : Type*} [CStarAlgebra A]

abbrev BoundedSeq (A : Type*) [CStarAlgebra A] := ℕ →ᵇ A

def normLimit (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : ℝ := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  exact
    (h_NormUltrapower_exists_norm_limit ω x).choose

def nullIdeal (ω : Ultrafilter ℕ) : Ideal (OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_add_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x + y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x+y))
      ((h_NormUltrapower_tendsto_norm ω x).add (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_add_le (x n) (y n))
  have h_NormUltrapower_normLimit_mul_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x * y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x * OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x*y))
      ((h_NormUltrapower_tendsto_norm ω x).mul (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_mul_le (x n) (y n))
  have h_NormUltrapower_normLimit_nonneg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.1
  have h_NormUltrapower_normLimit_zero  (ω : Ultrafilter ℕ) : OAI.KirchbergRordam.NormUltrapower.normLimit ω (0 : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) = 0 := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω 0)
    simp
  exact {
    carrier := {x | OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0}
    zero_mem' := h_NormUltrapower_normLimit_zero ω
    add_mem' := by
      intro x y hx hy
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0 at hx
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω y = 0 at hy
      apply le_antisymm _ (h_NormUltrapower_normLimit_nonneg ω (x+y))
      simpa only [hx, hy, add_zero] using h_NormUltrapower_normLimit_add_le ω x y
    smul_mem' := by
      intro x y hy
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω y = 0 at hy
      apply le_antisymm _ (h_NormUltrapower_normLimit_nonneg ω (x*y))
      simpa only [hy, mul_zero] using h_NormUltrapower_normLimit_mul_le ω x y
  }

instance nullIdeal_twoSided (ω : Ultrafilter ℕ) : (OAI.KirchbergRordam.NormUltrapower.nullIdeal (A := A) ω).IsTwoSided := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_mul_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x * y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x * OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x*y))
      ((h_NormUltrapower_tendsto_norm ω x).mul (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_mul_le (x n) (y n))
  have h_NormUltrapower_normLimit_nonneg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.1
  exact {
    mul_mem_of_left := by
      intro x y hx
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω (x*y) = 0
      apply le_antisymm _ (h_NormUltrapower_normLimit_nonneg ω (x*y))
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0 at hx
      simpa only [hx, zero_mul] using h_NormUltrapower_normLimit_mul_le ω x y
  }

instance nullIdeal_closed (ω : Ultrafilter ℕ) : IsClosed (OAI.KirchbergRordam.NormUltrapower.nullIdeal (A := A) ω : Set (OAI.KirchbergRordam.NormUltrapower.BoundedSeq A)) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_normLimit_le  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : OAI.KirchbergRordam.NormUltrapower.normLimit ω x ≤ ‖x‖ :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.2
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_add_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x + y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x+y))
      ((h_NormUltrapower_tendsto_norm ω x).add (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_add_le (x n) (y n))
  have h_NormUltrapower_normLimit_sub_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω x - OAI.KirchbergRordam.NormUltrapower.normLimit ω y ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω (x-y) := by
    have h := h_NormUltrapower_normLimit_add_le ω (x-y) y
    rw [sub_add_cancel] at h
    linarith
  have h_NormUltrapower_normLimit_lipschitz  (ω : Ultrafilter ℕ) :
      LipschitzWith 1 (OAI.KirchbergRordam.NormUltrapower.normLimit ω : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_le, dist_eq_norm]
    constructor
    · have h := (h_NormUltrapower_normLimit_sub_le ω y x).trans (h_NormUltrapower_normLimit_le ω (y-x))
      rw [norm_sub_rev] at h
      linarith
    · exact (h_NormUltrapower_normLimit_sub_le ω x y).trans (h_NormUltrapower_normLimit_le ω (x-y))
  exact
    isClosed_eq (h_NormUltrapower_normLimit_lipschitz ω).continuous continuous_const

abbrev Algebra (A : Type*) [CStarAlgebra A] (ω : Ultrafilter ℕ) :=
  OAI.KirchbergRordam.NormUltrapower.BoundedSeq A ⧸ OAI.KirchbergRordam.NormUltrapower.nullIdeal (A := A) ω

noncomputable instance quotientNormedRing {R : Type uQuot} [NormedRing R] (I : Ideal R)
    [I.IsTwoSided] [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  KirchbergRordam.QuotientNormSupport.normedRing I

instance quotientNormedAlgebra (ω : Ultrafilter ℕ) : NormedAlgebra ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where
  norm_smul_le := norm_smul_le

instance quotientStar (ω : Ultrafilter ℕ) : Star (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_star  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (star x) = OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω (star x))
    simp [h_NormUltrapower_tendsto_norm]
  exact {
    star := Quotient.map' star fun x y h => by
      rw [Submodule.quotientRel_def] at h ⊢
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω (star x - star y) = 0
      rw [← star_sub, h_NormUltrapower_normLimit_star]
      exact h
  }

instance quotientStarRing (ω : Ultrafilter ℕ) : StarRing (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where
  star_involutive := by
    rintro ⟨x⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (star x)) = Ideal.Quotient.mk _ x
    rw [star_star]
  star_mul := by
    rintro ⟨x⟩ ⟨y⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (x*y)) = Ideal.Quotient.mk _ (star y * star x)
    rw [star_mul]
  star_add := by
    rintro ⟨x⟩ ⟨y⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (x+y)) = Ideal.Quotient.mk _ (star x + star y)
    rw [star_add]

instance quotientStarModule (ω : Ultrafilter ℕ) : StarModule ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where
  star_smul := by
    intro z
    rintro ⟨x⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (z • x)) = Ideal.Quotient.mk _ (star z • star x)
    rw [star_smul]

def cutRepresentative (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A :=
  ofNormedAddCommGroupDiscrete (fun n => if ‖x n‖ < c then x n else 0) c (by
    intro n
    split_ifs with h
    · exact h.le
    · simpa only [norm_zero] using hc)

instance quotientCStarRing (ω : Ultrafilter ℕ) : CStarRing (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_star_mul  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (star x * x) = OAI.KirchbergRordam.NormUltrapower.normLimit ω x * OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω (star x * x))
    simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply,
      CStarRing.norm_star_mul_self] using (h_NormUltrapower_tendsto_norm ω x).mul (h_NormUltrapower_tendsto_norm ω x)
  have h_NormUltrapower_normLimit_neg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (-x) = OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω (-x))
    simp [h_NormUltrapower_tendsto_norm]
  have h_NormUltrapower_normLimit_add_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x + y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x+y))
      ((h_NormUltrapower_tendsto_norm ω x).add (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_add_le (x n) (y n))
  have h_NormUltrapower_normLimit_sub_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω x - OAI.KirchbergRordam.NormUltrapower.normLimit ω y ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω (x-y) := by
    have h := h_NormUltrapower_normLimit_add_le ω (x-y) y
    rw [sub_add_cancel] at h
    linarith
  have h_NormUltrapower_normLimit_eq_of_sub_mem  (ω : Ultrafilter ℕ) {x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A}
      (h : x-y ∈ OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) : OAI.KirchbergRordam.NormUltrapower.normLimit ω x = OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    change OAI.KirchbergRordam.NormUltrapower.normLimit ω (x-y) = 0 at h
    apply le_antisymm
    · have h' := h_NormUltrapower_normLimit_sub_le ω x y
      linarith
    · have h' := h_NormUltrapower_normLimit_sub_le ω y x
      rw [← neg_sub x y, h_NormUltrapower_normLimit_neg, h] at h'
      linarith
  have h_NormUltrapower_normLimit_le  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : OAI.KirchbergRordam.NormUltrapower.normLimit ω x ≤ ‖x‖ :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.2
  have h_NormUltrapower_normLimit_le_quotient  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω x ≤ ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ := by
    apply QuotientAddGroup.le_norm_iff.mpr
    intro y hy
    have h : y-x ∈ OAI.KirchbergRordam.NormUltrapower.nullIdeal ω := (Ideal.Quotient.eq).mp hy
    rw [← h_NormUltrapower_normLimit_eq_of_sub_mem ω h]
    exact h_NormUltrapower_normLimit_le ω y
  have h_NormUltrapower_mem_nullIdeal  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      x ∈ OAI.KirchbergRordam.NormUltrapower.nullIdeal ω ↔ Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 0) := by
    change OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0 ↔ _
    constructor
    · intro h
      simpa only [h] using h_NormUltrapower_tendsto_norm ω x
    · exact fun h => tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω x) h
  have h_NormUltrapower_cutRepresentative_mk_eq  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A)
      (c : ℝ) (hc : 0 ≤ c) (hlim : OAI.KirchbergRordam.NormUltrapower.normLimit ω x < c) :
      Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x =
        Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (OAI.KirchbergRordam.NormUltrapower.cutRepresentative x c hc) := by
    rw [Ideal.Quotient.eq, h_NormUltrapower_mem_nullIdeal]
    have he : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c :=
      (h_NormUltrapower_tendsto_norm ω x).eventually (eventually_lt_nhds hlim)
    have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0) := tendsto_const_nhds
    apply hz.congr'
    filter_upwards [he] with n hn
    change (0 : ℝ) = ‖x n - (if ‖x n‖ < c then x n else 0)‖
    rw [ite_eq_left hn, sub_self, norm_zero]
  have h_NormUltrapower_cutRepresentative_norm_le  (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) :
      ‖OAI.KirchbergRordam.NormUltrapower.cutRepresentative x c hc‖ ≤ c := by
    apply (BoundedContinuousFunction.norm_le hc).mpr
    intro n
    change ‖if ‖x n‖ < c then x n else 0‖ ≤ c
    split_ifs with h
    · exact h.le
    · simpa only [norm_zero] using hc
  have h_NormUltrapower_normLimit_nonneg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.1
  have h_NormUltrapower_quotient_norm_le_normLimit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hpos : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε := add_nonneg (h_NormUltrapower_normLimit_nonneg ω x) hε.le
    rw [h_NormUltrapower_cutRepresentative_mk_eq ω x (OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε) hpos (lt_add_of_pos_right _ hε)]
    have hb := Submodule.Quotient.norm_mk_le (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω)
      (OAI.KirchbergRordam.NormUltrapower.cutRepresentative x (OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε) hpos)
    exact hb.trans (h_NormUltrapower_cutRepresentative_norm_le x (OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε) hpos)
  have h_NormUltrapower_norm_mk_eq  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ = OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    le_antisymm (h_NormUltrapower_quotient_norm_le_normLimit ω x) (h_NormUltrapower_normLimit_le_quotient ω x)
  exact {
    norm_mul_self_le := by
      rintro ⟨x⟩
      change ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ * ‖Ideal.Quotient.mk _ x‖ ≤
        ‖Ideal.Quotient.mk _ (star x * x)‖
      rw [h_NormUltrapower_norm_mk_eq, h_NormUltrapower_norm_mk_eq, h_NormUltrapower_normLimit_star_mul]
  }

instance quotientCStarAlgebra (ω : Ultrafilter ℕ) : CStarAlgebra (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where

def quotientMap (ω : Ultrafilter ℕ) : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A →⋆ₐ[ℂ] OAI.KirchbergRordam.NormUltrapower.Algebra A ω where
  __ := Ideal.Quotient.mkₐ ℂ (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω)
  map_star' _ := rfl

def constantSeq : A →⋆ₐ[ℂ] OAI.KirchbergRordam.NormUltrapower.BoundedSeq A where
  toFun := BoundedContinuousFunction.const ℕ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def diagonal (ω : Ultrafilter ℕ) : A →⋆ₐ[ℂ] OAI.KirchbergRordam.NormUltrapower.Algebra A ω :=
  (OAI.KirchbergRordam.NormUltrapower.quotientMap ω).comp OAI.KirchbergRordam.NormUltrapower.constantSeq

def centralSubalgebra (ω : Ultrafilter ℕ) : StarSubalgebra ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) :=
  StarSubalgebra.centralizer ℂ (Set.range (OAI.KirchbergRordam.NormUltrapower.diagonal (A := A) ω))

instance centralSubalgebra_closed (ω : Ultrafilter ℕ) :
    IsClosed (OAI.KirchbergRordam.NormUltrapower.centralSubalgebra (A := A) ω : Set (OAI.KirchbergRordam.NormUltrapower.Algebra A ω)) :=
  Set.isClosed_centralizer _

abbrev CentralAlgebra (A : Type*) [CStarAlgebra A] (ω : Ultrafilter ℕ) :=
  OAI.KirchbergRordam.NormUltrapower.centralSubalgebra (A := A) ω

instance centralSubringClass (ω : Ultrafilter ℕ) :
    SubringClass (StarSubalgebra ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω)) (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) :=
  StarSubalgebra.subringClass (R := ℂ) (A := OAI.KirchbergRordam.NormUltrapower.Algebra A ω)

instance centralCStarAlgebra (ω : Ultrafilter ℕ) : CStarAlgebra (OAI.KirchbergRordam.NormUltrapower.CentralAlgebra A ω) :=
  StarSubalgebra.cstarAlgebra _

end KirchbergRordam.NormUltrapower

namespace KirchbergRordam
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionStar : Star (Completion R) := ⟨Completion.map (star : R → R)⟩

instance completionContinuousStar : ContinuousStar (Completion R) where
  continuous_star := Completion.continuous_map

instance completionStarRing : StarRing (Completion R) := by
  classical
  have h_StarCompletion_star_coe  (x : R) : star (x : Completion R) = (star x : R) :=
    Completion.map_coe star_isometry.uniformContinuous x
  exact {
    star_involutive x := by
      induction x using Completion.induction_on with
      | hp => exact isClosed_eq (continuous_star.comp continuous_star) continuous_id
      | ih x => simp only [h_StarCompletion_star_coe, star_star]
    star_mul x y := by
      induction x, y using Completion.induction_on₂ with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih x y => simp only [← Completion.coe_mul, h_StarCompletion_star_coe, star_mul]
    star_add x y := by
      induction x, y using Completion.induction_on₂ with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih x y => simp only [← Completion.coe_add, h_StarCompletion_star_coe, star_add]
  }

variable [NormedAlgebra ℂ R] [StarModule ℂ R]

instance completionNormedAlgebra : NormedAlgebra ℂ (Completion R) where
  norm_smul_le := norm_smul_le

instance completionStarModule : StarModule ℂ (Completion R) := by
  classical
  have h_StarCompletion_star_coe  (x : R) : star (x : Completion R) = (star x : R) :=
    Completion.map_coe star_isometry.uniformContinuous x
  exact {
    star_smul z x := by
      induction x using Completion.induction_on with
      | hp =>
        exact isClosed_eq
          (continuous_star.comp (continuous_const_smul z))
          ((continuous_const_smul (star z)).comp continuous_star)
      | ih x =>
        rw [← Completion.coe_smul, h_StarCompletion_star_coe, star_smul, Completion.coe_smul, h_StarCompletion_star_coe]
  }

end StarCompletion

end KirchbergRordam

namespace KirchbergRordam.CStarInductiveLimit
universe u

structure System where
  obj : ℕ → Type u
  [cstar : ∀ n, CStarAlgebra (obj n)]
  map : ∀ i j, i ≤ j → obj i →⋆ₐ[ℂ] obj j
  map_self : ∀ i x, map i i le_rfl x = x
  map_map : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
    map j k hjk (map i j hij x) = map i k (hij.trans hjk) x
  norm_map : ∀ i j (h : i ≤ j) x, ‖map i j h x‖ = ‖x‖

attribute [instance] System.cstar

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : DirectedSystem S.obj (S.map · · ·) where
  map_self := fun {_} x => S.map_self _ x
  map_map := fun {_ _ _} hij hjk x => S.map_map _ _ _ hij hjk x

def Raw (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) := DirectLimit S.obj S.map

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : Ring (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (Ring (DirectLimit S.obj S.map))

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : Algebra ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (Algebra ℂ (DirectLimit S.obj S.map))

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : StarRing (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (StarRing (DirectLimit S.obj S.map))

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : StarModule ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (StarModule ℂ (DirectLimit S.obj S.map))

def rawOf (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) : S.obj n →⋆ₐ[ℂ] OAI.KirchbergRordam.CStarInductiveLimit.Raw S where
  __ := DirectLimit.Algebra.of S.obj S.map n
  map_star' _ := rfl

def normLift (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : OAI.KirchbergRordam.CStarInductiveLimit.Raw S → ℝ :=
  DirectLimit.lift S.map (fun _ x => ‖x‖) (fun i j h x => (S.norm_map i j h x).symm)

def ringNorm (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : RingNorm (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  exact {
    toFun := OAI.KirchbergRordam.CStarInductiveLimit.normLift S
    map_zero' := by
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (0 : DirectLimit S.obj S.map) = 0
      rw [DirectLimit.zero_def (f := S.map) 0]
      exact norm_zero
    add_le' := by
      intro x y
      refine DirectLimit.induction₂ S.map ?_ x y
      intro n x y
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x + OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y) ≤
        OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) + OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y)
      rw [← map_add, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk]
      exact norm_add_le x y
    neg' := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (-OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x)
      rw [← map_neg, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk, norm_neg]
    mul_le' := by
      intro x y
      refine DirectLimit.induction₂ S.map ?_ x y
      intro n x y
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x * OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y) ≤
        OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) * OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y)
      rw [← map_mul, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk]
      exact norm_mul_le x y
    eq_zero_of_map_eq_zero' := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x hx
      change ‖x‖ = 0 at hx
      rw [norm_eq_zero] at hx
      change OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x = 0
      rw [hx, map_zero]
  }

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : NormedRing (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := (OAI.KirchbergRordam.CStarInductiveLimit.ringNorm S).toNormedRing

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : NormedAlgebra ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  have h_CStarInductiveLimit_norm_rawOf  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ = ‖x‖ := rfl
  exact {
    norm_smul_le z := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change ‖z • OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ ≤ ‖z‖ * ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖
      rw [← map_smul, h_CStarInductiveLimit_norm_rawOf, h_CStarInductiveLimit_norm_rawOf]
      exact norm_smul_le z x
  }

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : NormedStarGroup (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  have h_CStarInductiveLimit_norm_rawOf  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ = ‖x‖ := rfl
  exact {
    norm_star_le := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change ‖star (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x)‖ ≤ ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖
      rw [← map_star, h_CStarInductiveLimit_norm_rawOf, h_CStarInductiveLimit_norm_rawOf, norm_star]
  }

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : CStarRing (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  have h_CStarInductiveLimit_norm_rawOf  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ = ‖x‖ := rfl
  exact {
    norm_mul_self_le := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ * ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ ≤ ‖star (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) * OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖
      rw [← map_star, ← map_mul, h_CStarInductiveLimit_norm_rawOf, h_CStarInductiveLimit_norm_rawOf]
      exact CStarRing.norm_mul_self_le x
  }

abbrev Algebra (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) := UniformSpace.Completion (OAI.KirchbergRordam.CStarInductiveLimit.Raw S)

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : CStarRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S) := by
  classical
  have h_StarCompletion_star_coe (x : Raw S) : star (x : Completion (Raw S)) = ((star x : Raw S) : Completion (Raw S)) := Completion.map_coe star_isometry.uniformContinuous x
  exact {
    norm_mul_self_le x := by
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih x =>
        rw [(h_StarCompletion_star_coe), ← UniformSpace.Completion.coe_mul]
        simpa only [UniformSpace.Completion.norm_coe] using CStarRing.norm_mul_self_le x
  }

instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : CStarAlgebra (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S) :=
  { (inferInstance : NormedRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : NormedAlgebra ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : CompleteSpace (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : StarRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : StarModule ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : CStarRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)) with }

structure Chain where
  obj : ℕ → Type u
  [cstar : ∀ n, CStarAlgebra (obj n)]
  step : ∀ n, obj n →⋆ₐ[ℂ] obj (n+1)
  norm_step : ∀ n x, ‖step n x‖ = ‖x‖

attribute [instance] Chain.cstar

def Chain.map (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j : ℕ) (h : i ≤ j) : S.obj i →⋆ₐ[ℂ] S.obj j :=
  Nat.leRecOn (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n) h
    (fun {n} φ => (S.step n).comp φ) (StarAlgHom.id ℂ _)

def Chain.system (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) : OAI.KirchbergRordam.CStarInductiveLimit.System.{u} := by
  classical
  have h_CStarInductiveLimit_Chain_map_self  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i : ℕ) :
      S.map i i le_rfl = StarAlgHom.id ℂ _ := by simp [Chain.map, Nat.leRecOn_self]
  have h_CStarInductiveLimit_Chain_map_succ  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j : ℕ) (h : i ≤ j) :
      S.map i (j+1) (h.trans (Nat.le_succ j)) = (S.step j).comp (S.map i j h) := by
    exact Nat.leRecOn_succ (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n)
      (next := fun {n} φ => (S.step n).comp φ) h (StarAlgHom.id ℂ (S.obj i))
  have h_CStarInductiveLimit_Chain_map_map  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
      (x : S.obj i) : S.map j k hjk (S.map i j hij x) = S.map i k (hij.trans hjk) x := by
    induction k, hjk using Nat.le_induction with
    | base => simp [h_CStarInductiveLimit_Chain_map_self]
    | succ k hjk ih =>
      rw [(h_CStarInductiveLimit_Chain_map_succ S j k hjk), (h_CStarInductiveLimit_Chain_map_succ S i k (LE.le.trans hij hjk))]
      exact congrArg (S.step k) ih
  have h_CStarInductiveLimit_Chain_norm_map  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
      ‖S.map i j h x‖ = ‖x‖ := by
    induction j, h using Nat.le_induction with
    | base => simp [h_CStarInductiveLimit_Chain_map_self]
    | succ j h ih =>
      rw [(h_CStarInductiveLimit_Chain_map_succ S i j h)]
      exact (S.norm_step j (S.map i j h x)).trans ih
  exact {
    obj := S.obj
    map := S.map
    map_self i x := by simp [h_CStarInductiveLimit_Chain_map_self]
    map_map := (h_CStarInductiveLimit_Chain_map_map S)
    norm_map := (h_CStarInductiveLimit_Chain_norm_map S)
  }

end KirchbergRordam.CStarInductiveLimit

namespace KirchbergRordam.MaxTensor
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]

structure CrossSeminorm extends Seminorm ℂ (A ⊗[ℂ] B) where
  mul_le : ∀ x y, toSeminorm (x * y) ≤ toSeminorm x * toSeminorm y
  star_eq : ∀ x, toSeminorm (star x) = toSeminorm x
  cstar_eq : ∀ x, toSeminorm (star x * x) = toSeminorm x * toSeminorm x
  tmul_le : ∀ a b, toSeminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖

instance : Inhabited (OAI.KirchbergRordam.MaxTensor.CrossSeminorm A B) := ⟨{
  toSeminorm := 0
  mul_le := by simp
  star_eq := by simp
  cstar_eq := by simp
  tmul_le := by intro a b; simp only [zero_apply]; positivity }⟩

variable {A B}

def Raw (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] := A ⊗[ℂ] B

instance : Ring (OAI.KirchbergRordam.MaxTensor.Raw A B) := inferInstanceAs (Ring (A ⊗[ℂ] B))

instance : Algebra ℂ (OAI.KirchbergRordam.MaxTensor.Raw A B) := inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))

instance : StarRing (OAI.KirchbergRordam.MaxTensor.Raw A B) := inferInstanceAs (StarRing (A ⊗[ℂ] B))

def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] OAI.KirchbergRordam.MaxTensor.Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)

variable {C : Type*} [CStarAlgebra C]

def liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : OAI.KirchbergRordam.MaxTensor.Raw A B →⋆ₐ[ℂ] C where
  toAlgHom := _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h
  map_star' x := by
    change _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h (star x) =
      star (_root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h x)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [star_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change φ (star a) * ψ (star b) = star (φ a * ψ b)
      rw [star_mul, ← map_star, ← map_star]
      exact h (star a) (star b)

def representationSeminorm (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : OAI.KirchbergRordam.MaxTensor.CrossSeminorm A B := by
  classical
  have h_MaxTensor_liftRaw_tmul  (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
      (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
      OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (a ⊗ₜ[ℂ] b) = φ a * ψ b := rfl
  exact {
    toSeminorm := (normSeminorm ℂ C).comp (OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h).toLinearMap
    mul_le x y := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x * OAI.KirchbergRordam.MaxTensor.rawEquiv y)‖ ≤
        ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖ * ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv y)‖
      rw [map_mul]
      exact norm_mul_le _ _
    star_eq x := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (star (OAI.KirchbergRordam.MaxTensor.rawEquiv x))‖ = ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖
      rw [map_star, norm_star]
    cstar_eq x := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (star (OAI.KirchbergRordam.MaxTensor.rawEquiv x) * OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖ =
        ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖ * ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖
      rw [map_mul, map_star, CStarRing.norm_star_mul_self]
    tmul_le a b := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (a ⊗ₜ[ℂ] b)‖ ≤ ‖a‖ * ‖b‖
      rw [h_MaxTensor_liftRaw_tmul]
      exact (norm_mul_le _ _).trans (mul_le_mul
        (NonUnitalStarAlgHom.norm_apply_le φ a) (NonUnitalStarAlgHom.norm_apply_le ψ b)
        (norm_nonneg _) (norm_nonneg _))
  }

end KirchbergRordam.MaxTensor

namespace KirchbergRordam.Spatial
open Set Module NormedSpace
open scoped TensorProduct InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Hilbert (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] := Completion (H ⊗[ℂ] K)

def map (T : H →L[ℂ] H) (S : K →L[ℂ] K) : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K :=
  (TensorProduct.mapL T S).completion

variable [CompleteSpace H] [CompleteSpace K]

def left : (H →L[ℂ] H) →⋆ₐ[ℂ] (OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K) := by
  classical
  have h_Spatial_ext  {T S : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K}
      (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq T.continuous S.continuous
    | ih x => exact h x
  have h_Spatial_map_add_left__simp_1_1 (a b : H ⊗[ℂ] K) : (a : Completion (H ⊗[ℂ] K)) + (b : Completion (H ⊗[ℂ] K)) = ((a + b : H ⊗[ℂ] K) : Completion (H ⊗[ℂ] K)) := (Completion.coe_add a b).symm
  have h_Spatial_map_coe  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T S (x : OAI.KirchbergRordam.Spatial.Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
    simp [OAI.KirchbergRordam.Spatial.map]
  have h_Spatial_map_add_left  (T U : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T + U) S = OAI.KirchbergRordam.Spatial.map T S + OAI.KirchbergRordam.Spatial.map U S := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_add_left, (@h_Spatial_map_add_left__simp_1_1)]
  have h_Spatial_map_mul  (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T * U) (S * V) = OAI.KirchbergRordam.Spatial.map T S * OAI.KirchbergRordam.Spatial.map U V := by
    apply h_Spatial_ext
    intro x
    simp only [mul_apply_eq_comp, h_Spatial_map_coe, TensorProduct.mapL_mul]
  have h_Spatial_map_one  : OAI.KirchbergRordam.Spatial.map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
      show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]
  have h_Spatial_map_smul_left  (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (z • T) S = z • OAI.KirchbergRordam.Spatial.map T S := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_smul_left, ← Completion.coe_smul]
  have h_Spatial_map_inner_algebraic  (T : H →L[ℂ] H) (S : K →L[ℂ] K)
      (x y : H ⊗[ℂ] K) :
      ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
        ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
      | tmul c d =>
        simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h_Spatial_map_inner  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : OAI.KirchbergRordam.Spatial.Hilbert H K) :
      ⟪OAI.KirchbergRordam.Spatial.map (star T) (star S) x, y⟫_ℂ = ⟪x, OAI.KirchbergRordam.Spatial.map T S y⟫_ℂ := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simpa [h_Spatial_map_coe] using h_Spatial_map_inner_algebraic T S x y
  have h_Spatial_map_star  (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (star T) (star S) = star (OAI.KirchbergRordam.Spatial.map T S) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [h_Spatial_map_inner, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  exact {
    toFun T := OAI.KirchbergRordam.Spatial.map T 1
    map_zero' := by apply h_Spatial_ext; intro x; simp [OAI.KirchbergRordam.Spatial.map]
    map_one' := h_Spatial_map_one
    map_add' T U := h_Spatial_map_add_left T U 1
    map_mul' T U := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_mul T U (1 : K →L[ℂ] K) 1
    commutes' z := by
      change OAI.KirchbergRordam.Spatial.map (z • 1) 1 = z • 1
      rw [h_Spatial_map_smul_left, h_Spatial_map_one]
    map_star' T := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_star T (1 : K →L[ℂ] K)
  }

def right : (K →L[ℂ] K) →⋆ₐ[ℂ] (OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K) := by
  classical
  have h_Spatial_ext  {T S : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K}
      (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq T.continuous S.continuous
    | ih x => exact h x
  have h_Spatial_map_add_right__simp_1_1 (a b : H ⊗[ℂ] K) : (a : Completion (H ⊗[ℂ] K)) + (b : Completion (H ⊗[ℂ] K)) = ((a + b : H ⊗[ℂ] K) : Completion (H ⊗[ℂ] K)) := (Completion.coe_add a b).symm
  have h_Spatial_map_coe  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T S (x : OAI.KirchbergRordam.Spatial.Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
    simp [OAI.KirchbergRordam.Spatial.map]
  have h_Spatial_map_add_right  (T : H →L[ℂ] H) (S U : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T (S + U) = OAI.KirchbergRordam.Spatial.map T S + OAI.KirchbergRordam.Spatial.map T U := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_add_right, (@h_Spatial_map_add_right__simp_1_1)]
  have h_Spatial_map_mul  (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T * U) (S * V) = OAI.KirchbergRordam.Spatial.map T S * OAI.KirchbergRordam.Spatial.map U V := by
    apply h_Spatial_ext
    intro x
    simp only [mul_apply_eq_comp, h_Spatial_map_coe, TensorProduct.mapL_mul]
  have h_Spatial_map_one  : OAI.KirchbergRordam.Spatial.map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
      show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]
  have h_Spatial_map_smul_right  (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T (z • S) = z • OAI.KirchbergRordam.Spatial.map T S := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_smul_right, ← Completion.coe_smul]
  have h_Spatial_map_inner_algebraic  (T : H →L[ℂ] H) (S : K →L[ℂ] K)
      (x y : H ⊗[ℂ] K) :
      ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
        ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
      | tmul c d =>
        simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h_Spatial_map_inner  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : OAI.KirchbergRordam.Spatial.Hilbert H K) :
      ⟪OAI.KirchbergRordam.Spatial.map (star T) (star S) x, y⟫_ℂ = ⟪x, OAI.KirchbergRordam.Spatial.map T S y⟫_ℂ := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simpa [h_Spatial_map_coe] using h_Spatial_map_inner_algebraic T S x y
  have h_Spatial_map_star  (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (star T) (star S) = star (OAI.KirchbergRordam.Spatial.map T S) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [h_Spatial_map_inner, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  exact {
    toFun S := OAI.KirchbergRordam.Spatial.map 1 S
    map_zero' := by apply h_Spatial_ext; intro x; simp [OAI.KirchbergRordam.Spatial.map]
    map_one' := h_Spatial_map_one
    map_add' T U := h_Spatial_map_add_right 1 T U
    map_mul' T U := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_mul (1 : H →L[ℂ] H) 1 T U
    commutes' z := by
      change OAI.KirchbergRordam.Spatial.map 1 (z • 1) = z • 1
      rw [h_Spatial_map_smul_right, h_Spatial_map_one]
    map_star' S := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_star (1 : H →L[ℂ] H) S
  }

end KirchbergRordam.Spatial

namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

structure RepresentationPair where
  H : Type u
  K : Type u
  normH : NormedAddCommGroup H
  innerH : InnerProductSpace ℂ H
  completeH : CompleteSpace H
  normK : NormedAddCommGroup K
  innerK : InnerProductSpace ℂ K
  completeK : CompleteSpace K
  leftRep : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  rightRep : B →⋆ₐ[ℂ] (K →L[ℂ] K)

attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK
variable {A B}
def RepresentationPair.left (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) :
    A →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  Spatial.left.comp ρ.leftRep

def RepresentationPair.right (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) :
    B →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  Spatial.right.comp ρ.rightRep

def RepresentationPair.crossSeminorm (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) :
    MaxTensor.CrossSeminorm A B := by
  classical
  have h_Spatial_ext {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K]  {T S : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K}
      (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq T.continuous S.continuous
    | ih x => exact h x
  have h_Spatial_map_coe {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K]  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T S (x : OAI.KirchbergRordam.Spatial.Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
    simp [OAI.KirchbergRordam.Spatial.map]
  have h_Spatial_map_mul {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K]  (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T * U) (S * V) = OAI.KirchbergRordam.Spatial.map T S * OAI.KirchbergRordam.Spatial.map U V := by
    apply h_Spatial_ext
    intro x
    simp only [mul_apply_eq_comp, h_Spatial_map_coe, TensorProduct.mapL_mul]
  have h_Spatial_left_right_commute {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K] [inst6 : CompleteSpace H] [inst7 : CompleteSpace K]  (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      Commute (OAI.KirchbergRordam.Spatial.left (K := K) T) (OAI.KirchbergRordam.Spatial.right (H := H) S) := by
    change OAI.KirchbergRordam.Spatial.map T 1 * OAI.KirchbergRordam.Spatial.map 1 S = OAI.KirchbergRordam.Spatial.map 1 S * OAI.KirchbergRordam.Spatial.map T 1
    rw [← h_Spatial_map_mul, ← h_Spatial_map_mul]
    simp
  have h_MinTensor_RepresentationPair_commute  (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) (a : A) (b : B) :
      Commute (ρ.left a) (ρ.right b) :=
    (@h_Spatial_left_right_commute) _ _
  exact
    MaxTensor.representationSeminorm (A := A) (B := B)
        (C := (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K))
        ρ.left ρ.right (h_MinTensor_RepresentationPair_commute ρ)

def spatialIndex : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B) → MaxTensor.CrossSeminorm A B
  | none => default
  | some ρ => ρ.crossSeminorm

def seminorm : Seminorm ℂ (A ⊗[ℂ] B) :=
  ⨆ ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B), (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm

end KirchbergRordam.MinTensor
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
open Set Module NormedSpace
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
local instance instRingTensorProductComplex_analysis : Ring (A ⊗[ℂ] B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)

end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

def Raw : Type u := A ⊗[ℂ] B

variable {A B}
instance : Ring (OAI.KirchbergRordam.MinTensor.Raw A B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)

instance : Algebra ℂ (OAI.KirchbergRordam.MinTensor.Raw A B) := _root_.Algebra.TensorProduct.instAlgebra

instance instStarRingRaw : StarRing (OAI.KirchbergRordam.MinTensor.Raw A B) :=
  inferInstanceAs (StarRing (MaxTensor.Raw A B))

def rawRingSeminorm : RingSeminorm (OAI.KirchbergRordam.MinTensor.Raw A B) := by
  classical
  have h_MaxTensor_bounded_at {A : Type u} {B : Type u} [inst2 : CStarAlgebra A] [inst3 : CStarAlgebra B]  (x : A ⊗[ℂ] B) :
      ∃ C : ℝ, ∀ p : OAI.KirchbergRordam.MaxTensor.CrossSeminorm A B, p.toSeminorm x ≤ C := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact ⟨‖a‖ * ‖b‖, fun p => p.tmul_le a b⟩
    | add x y hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, fun p => (map_add_le_add p.toSeminorm x y).trans
          (add_le_add (hC p) (hD p))⟩
  have h_MinTensor_bounded  : BddAbove (Set.range (fun ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B) =>
      (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm)) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    obtain ⟨C,hC⟩ := (@h_MaxTensor_bounded_at) x
    exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
  have h_MinTensor_seminorm_apply  (x : A ⊗[ℂ] B) :
      OAI.KirchbergRordam.MinTensor.seminorm x=⨆ ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B), (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm x :=
    Seminorm.iSup_apply h_MinTensor_bounded
  have h_MinTensor_le_seminorm  (ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B)) (x : A ⊗[ℂ] B) :
      (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm x ≤ OAI.KirchbergRordam.MinTensor.seminorm x := by
    rw [h_MinTensor_seminorm_apply]
    apply le_ciSup _ ρ
    obtain ⟨C,hC⟩ := (@h_MaxTensor_bounded_at) x
    exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
  have h_MinTensor_seminorm_le  {x : A ⊗[ℂ] B} {C : ℝ}
      (h : ∀ ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B), (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm x ≤ C) :
      OAI.KirchbergRordam.MinTensor.seminorm x ≤ C := by
    rw [h_MinTensor_seminorm_apply]
    exact ciSup_le h
  have h_MinTensor_seminorm_mul_le  (x y : A ⊗[ℂ] B) :
      @LE.le ℝ Real.instLE
        (OAI.KirchbergRordam.MinTensor.seminorm (@Mul.mul (A ⊗[ℂ] B)
          (_root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)).toMul x y))
        (@Mul.mul ℝ Real.instMul (OAI.KirchbergRordam.MinTensor.seminorm x) (OAI.KirchbergRordam.MinTensor.seminorm y)) := by
    apply h_MinTensor_seminorm_le
    intro ρ
    exact ((OAI.KirchbergRordam.MinTensor.spatialIndex ρ).mul_le x y).trans (mul_le_mul (h_MinTensor_le_seminorm ρ x)
      (h_MinTensor_le_seminorm ρ y) (apply_nonneg _ _) (apply_nonneg _ _))
  exact {
    __ := (OAI.KirchbergRordam.MinTensor.seminorm (A := A) (B := B)).toAddGroupSeminorm
    mul_le' := h_MinTensor_seminorm_mul_le
  }

instance : SeminormedRing (OAI.KirchbergRordam.MinTensor.Raw A B) := OAI.KirchbergRordam.MinTensor.rawRingSeminorm.toSeminormedRing

abbrev Algebra (A B : Type u) [CStarAlgebra A] [CStarAlgebra B] :=
  UniformSpace.Completion (OAI.KirchbergRordam.MinTensor.Raw A B)

end KirchbergRordam.MinTensor

namespace KirchbergRordam.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ

def leftMatrixAlgebra : Matrix ι ι ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix κ κ ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix κ κ ℂ) (1 : Matrix κ κ ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix κ κ ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

def rightMatrixAlgebra : Matrix κ κ ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := (1 : Matrix ι ι ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix ι ι ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

def leftMatrix : OAI.KirchbergRordam.MatrixTensor.Mat ι →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixTensor.Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (OAI.KirchbergRordam.MatrixTensor.leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

def rightMatrix : OAI.KirchbergRordam.MatrixTensor.Mat κ →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixTensor.Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (OAI.KirchbergRordam.MatrixTensor.rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

end KirchbergRordam.MatrixTensor

namespace KirchbergRordam.PrimeDimensionDrop
open MatrixTensor
open scoped Matrix Kronecker ComplexOrder CStarAlgebra

abbrev Fiber (p q : ℕ) := OAI.KirchbergRordam.MatrixTensor.Mat (Fin p × Fin q)

def eval (p q : ℕ) (t : unitInterval) :
    C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) →⋆ₐ[ℂ] OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def subalgebra (p q : ℕ) : StarSubalgebra ℂ C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) :=
  (OAI.KirchbergRordam.MatrixTensor.leftMatrix (ι := Fin p) (κ := Fin q)).range.comap (OAI.KirchbergRordam.PrimeDimensionDrop.eval p q 0) ⊓
    (OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι := Fin p) (κ := Fin q)).range.comap (OAI.KirchbergRordam.PrimeDimensionDrop.eval p q 1)

instance (p q : ℕ) : FiniteDimensional ℂ (OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ))

instance (p q : ℕ) : IsClosed (OAI.KirchbergRordam.PrimeDimensionDrop.subalgebra p q : Set C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)) := by
  change IsClosed ((fun f : C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) => f 0) ⁻¹'
    ((OAI.KirchbergRordam.MatrixTensor.leftMatrix (ι := Fin p) (κ := Fin q)).range : Set (OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)) ∩
    (fun f : C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) => f 1) ⁻¹'
    ((OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι := Fin p) (κ := Fin q)).range : Set (OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)))
  exact ((OAI.KirchbergRordam.MatrixTensor.leftMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))).inter
    ((OAI.KirchbergRordam.MatrixTensor.rightMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (1 : unitInterval)))

abbrev Algebra (p q : ℕ) := OAI.KirchbergRordam.PrimeDimensionDrop.subalgebra p q

instance (p q : ℕ) : SubringClass
    (StarSubalgebra ℂ C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)) C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q))

instance (p q : ℕ) : CStarAlgebra (OAI.KirchbergRordam.PrimeDimensionDrop.Algebra p q) := StarSubalgebra.cstarAlgebra (OAI.KirchbergRordam.PrimeDimensionDrop.subalgebra p q)

end KirchbergRordam.PrimeDimensionDrop

namespace KirchbergRordam.UnitaryPaths

variable {A : Type*} [CStarAlgebra A]

def phase (t : unitInterval) : ℂ := Complex.exp (((t:ℝ) * Real.pi) * Complex.I)

def involutionValue (U : A) (t : unitInterval) : A :=
  ((1 + OAI.KirchbergRordam.UnitaryPaths.phase t) / 2) • (1:A) + ((1 - OAI.KirchbergRordam.UnitaryPaths.phase t) / 2) • U

def involutionPath (U : unitary A) (hs : star (U:A) = U) : Path 1 U := by
  classical
  have h_UnitaryPaths_phase_continuous  : Continuous OAI.KirchbergRordam.UnitaryPaths.phase := by unfold OAI.KirchbergRordam.UnitaryPaths.phase; fun_prop
  have h_UnitaryPaths_involutionValue_continuous  (U : A) : Continuous (OAI.KirchbergRordam.UnitaryPaths.involutionValue U) := by
    unfold OAI.KirchbergRordam.UnitaryPaths.involutionValue
    fun_prop
  have h_UnitaryPaths_phase_unitary  (t : unitInterval) : star (OAI.KirchbergRordam.UnitaryPaths.phase t) * OAI.KirchbergRordam.UnitaryPaths.phase t = 1 := by
    have hn : ‖OAI.KirchbergRordam.UnitaryPaths.phase t‖ = 1 := by
      simpa [OAI.KirchbergRordam.UnitaryPaths.phase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I ((t:ℝ) * Real.pi)
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have h_UnitaryPaths_involutionValue_unitary  (U : A) (hs : star U = U) (hm : U * U = 1)
      (t : unitInterval) : OAI.KirchbergRordam.UnitaryPaths.involutionValue U t ∈ unitary A := by
    have hz := h_UnitaryPaths_phase_unitary t
    have h1 : (star ((1:ℂ)+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
        (star ((1:ℂ)-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)=1 := by
      simp only [star_add,star_sub,star_one]
      calc
        _ = (1+star (OAI.KirchbergRordam.UnitaryPaths.phase t)*OAI.KirchbergRordam.UnitaryPaths.phase t)/2 := by ring
        _ = 1 := by rw [hz]; norm_num
    have h2 : (star ((1:ℂ)+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
        (star ((1:ℂ)-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)=0 := by
      simp only [star_add,star_sub,star_one]
      calc
        _ = (1-star (OAI.KirchbergRordam.UnitaryPaths.phase t)*OAI.KirchbergRordam.UnitaryPaths.phase t)/2 := by ring
        _ = 0 := by rw [hz]; norm_num
    have h : star (OAI.KirchbergRordam.UnitaryPaths.involutionValue U t) * OAI.KirchbergRordam.UnitaryPaths.involutionValue U t = 1 := by
      simp only [OAI.KirchbergRordam.UnitaryPaths.involutionValue, star_add, star_smul, star_one, hs, star_div₀,
        star_ofNat, star_sub, smul_add, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, smul_smul, one_mul, mul_one, hm]
      calc
        _ = (((1+star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
              ((1-star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)) • (1:A) +
            (((1+star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
              ((1-star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)) • U := by
                rw [add_smul, add_smul]; module
        _ = 1 := by
          simp only [star_add, star_sub, star_one] at h1 h2
          rw [h1, h2, one_smul, zero_smul, add_zero]
    refine ⟨h, ?_⟩
    have hc : Commute (OAI.KirchbergRordam.UnitaryPaths.involutionValue U t) (star (OAI.KirchbergRordam.UnitaryPaths.involutionValue U t)) := by
      unfold OAI.KirchbergRordam.UnitaryPaths.involutionValue
      simp only [star_add, star_smul, star_one, hs]
      exact ((Commute.one_left _).smul_left _).add_left
        ((((Commute.one_right U).smul_right _).add_right
          ((Commute.refl U).smul_right _)).smul_left _)
    exact hc.eq.trans h
  have h_UnitaryPaths_phase_one  : OAI.KirchbergRordam.UnitaryPaths.phase 1 = -1 := by simp [OAI.KirchbergRordam.UnitaryPaths.phase, Complex.exp_pi_mul_I]
  have h_UnitaryPaths_phase_zero  : OAI.KirchbergRordam.UnitaryPaths.phase 0 = 1 := by simp [OAI.KirchbergRordam.UnitaryPaths.phase]
  exact {
    toFun t := ⟨OAI.KirchbergRordam.UnitaryPaths.involutionValue (U:A) t,
      h_UnitaryPaths_involutionValue_unitary (U:A) hs (by simpa only [hs] using Unitary.coe_star_mul_self U) t⟩
    continuous_toFun := (h_UnitaryPaths_involutionValue_continuous _).subtype_mk _
    source' := by apply Subtype.ext; simp [h_UnitaryPaths_phase_zero, OAI.KirchbergRordam.UnitaryPaths.involutionValue]
    target' := by apply Subtype.ext; simp [h_UnitaryPaths_phase_one, OAI.KirchbergRordam.UnitaryPaths.involutionValue]
  }

end KirchbergRordam.UnitaryPaths

namespace KirchbergRordam.MatrixPermutationPath
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ

def perm (σ : Equiv.Perm ι) : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) :=
  ⟨CStarMatrix.ofMatrix (σ⁻¹.permMatrix ℂ), by
    constructor
    · change (σ⁻¹.permMatrix ℂ)ᴴ * σ⁻¹.permMatrix ℂ = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp
    · change σ⁻¹.permMatrix ℂ * (σ⁻¹.permMatrix ℂ)ᴴ = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp⟩

def path (σ τ : Equiv.Perm ι) : Path (OAI.KirchbergRordam.MatrixPermutationPath.perm σ) (OAI.KirchbergRordam.MatrixPermutationPath.perm τ) := by
  classical
  have h_MatrixPermutationPath_perm_mul  (σ τ : Equiv.Perm ι) : OAI.KirchbergRordam.MatrixPermutationPath.perm (σ*τ) = OAI.KirchbergRordam.MatrixPermutationPath.perm σ * OAI.KirchbergRordam.MatrixPermutationPath.perm τ := by
    apply Subtype.ext
    change ((σ*τ)⁻¹).permMatrix ℂ = σ⁻¹.permMatrix ℂ * τ⁻¹.permMatrix ℂ
    simp
  have h_MatrixPermutationPath_perm_one  : OAI.KirchbergRordam.MatrixPermutationPath.perm (1 : Equiv.Perm ι) = 1 := by
    apply Subtype.ext
    change (1⁻¹ : Equiv.Perm ι).permMatrix ℂ = 1
    simp
  have h_MatrixPermutationPath_perm_swap_selfadjoint  (i j : ι) : star (OAI.KirchbergRordam.MatrixPermutationPath.perm (Equiv.swap i j) : OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) =
      (OAI.KirchbergRordam.MatrixPermutationPath.perm (Equiv.swap i j) : OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) := by
    change ((Equiv.swap i j)⁻¹.permMatrix ℂ)ᴴ = (Equiv.swap i j)⁻¹.permMatrix ℂ
    simp
  have h_MatrixPermutationPath_joined_one_perm  (σ : Equiv.Perm ι) : Joined (1 : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι)) (OAI.KirchbergRordam.MatrixPermutationPath.perm σ) := by
    induction σ using Equiv.Perm.swap_induction_on with
    | one => simpa [h_MatrixPermutationPath_perm_one] using Joined.refl (1 : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι))
    | swap_mul σ i j hij ih =>
      rw [h_MatrixPermutationPath_perm_mul]
      have hi : Joined (1 : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι)) (OAI.KirchbergRordam.MatrixPermutationPath.perm (Equiv.swap i j)) :=
        ⟨UnitaryPaths.involutionPath _ (h_MatrixPermutationPath_perm_swap_selfadjoint i j)⟩
      simpa only [one_mul] using hi.mul ih
  exact
    ((h_MatrixPermutationPath_joined_one_perm σ).symm.trans (h_MatrixPermutationPath_joined_one_perm τ)).somePath

end KirchbergRordam.MatrixPermutationPath

namespace KirchbergRordam.MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [instDecidableEqκ : DecidableEq κ] [Fintype ν] [DecidableEq ν]
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ

def block : (ι → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ × ι) where
  toFun a := CStarMatrix.ofMatrix (Matrix.blockDiagonal a)
  map_zero' := Matrix.blockDiagonal_zero
  map_one' := Matrix.blockDiagonal_one
  map_add' := Matrix.blockDiagonal_add
  map_mul' := Matrix.blockDiagonal_mul
  commutes' z := by
    change Matrix.blockDiagonal (fun _ : ι => (algebraMap ℂ (Matrix κ κ ℂ)) z) =
      algebraMap ℂ (Matrix (κ × ι) (κ × ι) ℂ) z
    simp only [Algebra.algebraMap_eq_smul_one]
    exact (Matrix.blockDiagonal_smul z (1 : ι → Matrix κ κ ℂ)).trans
      (congrArg (z • ·) Matrix.blockDiagonal_one)
  map_star' a := Matrix.blockDiagonal_conjTranspose a |>.symm

def evaluationBlock (ξ : ι → C(unitInterval, unitInterval)) (t : unitInterval) :
    C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ × ι) where
  toFun f := OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => f (ξ i t))
  map_zero' := map_zero OAI.KirchbergRordam.MatrixDiagonalPath.block
  map_one' := map_one OAI.KirchbergRordam.MatrixDiagonalPath.block
  map_add' first second := map_add OAI.KirchbergRordam.MatrixDiagonalPath.block (fun index => first (ξ index t)) (fun index => second (ξ index t))
  map_mul' first second := map_mul OAI.KirchbergRordam.MatrixDiagonalPath.block (fun index => first (ξ index t)) (fun index => second (ξ index t))
  commutes' z := OAI.KirchbergRordam.MatrixDiagonalPath.block.commutes z
  map_star' path := map_star OAI.KirchbergRordam.MatrixDiagonalPath.block (fun index => path (ξ index t))

def diagonal (ξ : ι → C(unitInterval, unitInterval)) :
    C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) →⋆ₐ[ℂ] C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ × ι)) := by
  classical
  have h_MatrixDiagonalPath_evaluationBlock_continuous  (ξ : ι → C(unitInterval, unitInterval))
      (f : C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ)) : Continuous (fun t => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t f) :=
    (map_continuous OAI.KirchbergRordam.MatrixDiagonalPath.block).comp (continuous_pi (fun i => f.continuous.comp (ξ i).continuous))
  exact {
    toFun f := ⟨fun t => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t f, h_MatrixDiagonalPath_evaluationBlock_continuous ξ f⟩
    map_zero' := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_zero) _) _
    map_one' := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_one) _) _
    map_add' f g := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_add f g) _) _
    map_mul' f g := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_mul f g) _) _
    commutes' z := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).commutes z) _) _
    map_star' f := by ext t; exact congrFun (congrFun (map_star (OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t) f) _) _
  }

def interpolate (e₀ e₁ : κ ≃ ν) (t : unitInterval) : OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ ≃⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν :=
  (CStarMatrix.reindexₐ ℂ ℂ e₀).trans
    (Unitary.conjStarAlgAut ℂ _
      ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t))

end KirchbergRordam.MatrixDiagonalPath

namespace KirchbergRordam.MatrixBlockReindex
open MatrixTensor (leftMatrix rightMatrix)
open MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix Kronecker
variable {P Q L R S T : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T]

def sumBlock : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P × OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P ⊕ Q) where
  toFun a := CStarMatrix.ofMatrix (Matrix.fromBlocks a.1 0 0 a.2)
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := by
    change Matrix.fromBlocks (1 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ) = 1
    exact Matrix.fromBlocks_one
  map_add' a b := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_mul' a b := by
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1 * CStarMatrix.ofMatrix.symm b.1) 0 0
      (CStarMatrix.ofMatrix.symm a.2 * CStarMatrix.ofMatrix.symm b.2) =
      Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1) 0 0 (CStarMatrix.ofMatrix.symm a.2) *
        Matrix.fromBlocks (CStarMatrix.ofMatrix.symm b.1) 0 0 (CStarMatrix.ofMatrix.symm b.2)
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  commutes' z := by
    ext i j; cases i <;> cases j <;>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.fromBlocks, CStarMatrix.one_apply]
  map_star' a := by
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1)ᴴ 0 0
      (CStarMatrix.ofMatrix.symm a.2)ᴴ =
        (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1) 0 0
          (CStarMatrix.ofMatrix.symm a.2))ᴴ
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]

end KirchbergRordam.MatrixBlockReindex

namespace KirchbergRordam.MatrixBlockReindex
open MatrixDiagonalPath
open MatrixTensor (leftMatrix rightMatrix)
open scoped ComplexOrder CStarAlgebra Matrix
variable {P Q R S : Type*} [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [DecidableEq R] [DecidableEq S]
end KirchbergRordam.MatrixBlockReindex

namespace KirchbergRordam.BalancedDropSystem

def cardEquiv {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α = Fintype.card β) : α ≃ β :=
  Classical.choice ((Fintype.card_eq.mp h))

def half : unitInterval := by
  classical
  have h_BalancedDropSystem_half_mem  : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  exact
    ⟨@Div.div ℝ Real.instDivInvMonoid.toDiv Real.instOne.one
        (Real.instNatCast.natCast 2), h_BalancedDropSystem_half_mem⟩

def lowerPath : C(unitInterval, unitInterval) :=
  ⟨fun point => ⟨@Div.div ℝ Real.instDivInvMonoid.toDiv point.val
    (Real.instNatCast.natCast 2), by
      change (point : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1
      constructor <;> linarith [point.property.1, point.property.2]⟩, by
    apply Continuous.subtype_mk
    change Continuous (fun point : unitInterval => (point : ℝ) / 2)
    fun_prop⟩

def upperPath : C(unitInterval, unitInterval) :=
  ⟨fun point => ⟨@Div.div ℝ Real.instDivInvMonoid.toDiv
    (@Add.add ℝ Real.instAdd point.val Real.instOne.one)
    (Real.instNatCast.natCast 2), by
      change ((point : ℝ) + 1) / 2 ∈ Set.Icc (0 : ℝ) 1
      constructor <;> linarith [point.property.1, point.property.2]⟩, by
    apply Continuous.subtype_mk
    change Continuous (fun point : unitInterval => ((point : ℝ) + 1) / 2)
    fun_prop⟩

end KirchbergRordam.BalancedDropSystem

namespace KirchbergRordam.GeneralBlockReindex
open MatrixBlockReindex MatrixDiagonalPath

open scoped CStarAlgebra Matrix
variable {P Q L R S T U : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]
def repackLeft (hL : Q × L ≃ U × T) (hR : R ≃ S × T) :
    (P × Q) × (L ⊕ R) ≃ ((P × U) ⊕ ((P × Q) × S)) × T where
  toFun x := match x.2 with
    | .inl l => (.inl (x.1.1,(hL (x.1.2,l)).1),(hL (x.1.2,l)).2)
    | .inr r => (.inr (x.1,(hR r).1),(hR r).2)
  invFun x := match x.1 with
    | .inl y => ((y.1,(hL.symm (y.2,x.2)).1),.inl (hL.symm (y.2,x.2)).2)
    | .inr y => (y.1,.inr (hR.symm (y.2,x.2)))
  left_inv x := by rcases x with ⟨⟨i,j⟩,l|r⟩ <;> simp
  right_inv x := by rcases x with ⟨⟨i,u⟩|⟨ij,s⟩,t⟩ <;> simp

def repackRight (hL : P × L ≃ T × U) (hR : R ≃ T × S) :
    (P × Q) × (L ⊕ R) ≃ T × ((Q × U) ⊕ ((P × Q) × S)) := by
  classical
  have h_GeneralBlockReindex_left_low
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (l : L) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inl l) = (.inl (i,(hL (j,l)).1),(hL (j,l)).2) := rfl
  have h_GeneralBlockReindex_left_full
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (r : R) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inr r) = (.inr ((i,j),(hR r).1),(hR r).2) := rfl
  exact {
    toFun x := match x.2 with
      | .inl l => ((hL (x.1.1,l)).1,.inl (x.1.2,(hL (x.1.1,l)).2))
      | .inr r => ((hR r).1,.inr (x.1,(hR r).2))
    invFun x := match x.2 with
      | .inl y => (((hL.symm (x.1,y.2)).1,y.1),.inl (hL.symm (x.1,y.2)).2)
      | .inr y => (y.1,.inr (hR.symm (x.1,y.2)))
    left_inv x := by rcases x with ⟨⟨i,j⟩,l|r⟩ <;> simp
    right_inv x := by rcases x with ⟨t,⟨j,u⟩|⟨ij,s⟩⟩ <;> simp
  }

end KirchbergRordam.GeneralBlockReindex

namespace KirchbergRordam.GeneralDropSystem
open MatrixDiagonalPath MatrixBlockReindex
open BalancedDropSystem (half lowerPath upperPath)
open scoped CStarAlgebra Matrix ComplexOrder

structure Data (p q P Q : ℕ) where
  lower : ℕ
  upper : ℕ
  middle : ℕ
  zeroEnd : ℕ
  zeroMid : ℕ
  oneEnd : ℕ
  oneMid : ℕ
  lower_pos : 0<lower
  upper_pos : 0<upper
  zero_low : q*lower=zeroEnd*Q
  zero_mid : upper+middle=zeroMid*Q
  one_low : p*upper=P*oneEnd
  one_mid : lower+middle=P*oneMid
  zero_dim : p*zeroEnd+p*q*zeroMid=P
  one_dim : q*oneEnd+p*q*oneMid=Q

variable {p q P Q : ℕ} (d : Data p q P Q)
abbrev Low := Fin d.lower

abbrev High := Fin d.upper

abbrev Mid := Fin d.middle

abbrev Slot := OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ (OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d)

abbrev Index := (Fin p × Fin q) × OAI.KirchbergRordam.GeneralDropSystem.Slot d

abbrev ZeroSpace := (Fin p × Fin d.zeroEnd) ⊕ ((Fin p × Fin q) × Fin d.zeroMid)

abbrev OneSpace := (Fin q × Fin d.oneEnd) ⊕ ((Fin p × Fin q) × Fin d.oneMid)

def zeroLow : Fin q × OAI.KirchbergRordam.GeneralDropSystem.Low d ≃ Fin d.zeroEnd × Fin Q :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_prod,Fintype.card_fin] using d.zero_low)

def zeroMid : OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d ≃ Fin d.zeroMid × Fin Q :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.zero_mid)

def zeroOuter : OAI.KirchbergRordam.GeneralDropSystem.ZeroSpace d ≃ Fin P :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.zero_dim)

def oneLow : Fin p × OAI.KirchbergRordam.GeneralDropSystem.High d ≃ Fin P × Fin d.oneEnd :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_prod,Fintype.card_fin] using d.one_low)

def oneMid : OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d ≃ Fin P × Fin d.oneMid :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.one_mid)

def oneOuter : OAI.KirchbergRordam.GeneralDropSystem.OneSpace d ≃ Fin Q :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.one_dim)

def slotSwap : OAI.KirchbergRordam.GeneralDropSystem.Slot d ≃ OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ (OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d) where
  toFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  invFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  left_inv x := by rcases x with x|x|x <;> rfl
  right_inv x := by rcases x with x|x|x <;> rfl

def zeroReindex : OAI.KirchbergRordam.GeneralDropSystem.Index d ≃ Fin P × Fin Q :=
  (GeneralBlockReindex.repackLeft (OAI.KirchbergRordam.GeneralDropSystem.zeroLow d) (OAI.KirchbergRordam.GeneralDropSystem.zeroMid d)).trans
    (Equiv.prodCongr (OAI.KirchbergRordam.GeneralDropSystem.zeroOuter d) (Equiv.refl _))

def oneReindex : OAI.KirchbergRordam.GeneralDropSystem.Index d ≃ Fin P × Fin Q :=
  (Equiv.prodCongr (Equiv.refl _) (OAI.KirchbergRordam.GeneralDropSystem.slotSwap d)).trans
    ((GeneralBlockReindex.repackRight (OAI.KirchbergRordam.GeneralDropSystem.oneLow d) (OAI.KirchbergRordam.GeneralDropSystem.oneMid d)).trans
      (Equiv.prodCongr (Equiv.refl _) (OAI.KirchbergRordam.GeneralDropSystem.oneOuter d)))

def eigenpath : OAI.KirchbergRordam.GeneralDropSystem.Slot d → C(unitInterval,unitInterval) :=
  Sum.elim (fun _ => OAI.KirchbergRordam.BalancedDropSystem.lowerPath) (Sum.elim (fun _ => OAI.KirchbergRordam.BalancedDropSystem.upperPath) (fun _ => ContinuousMap.const _ OAI.KirchbergRordam.BalancedDropSystem.half))

section

def interpolatedEvaluation.{sourceLevel, blockLevel, targetLevel}
    {SourceIndex : Type sourceLevel} {BlockIndex : Type blockLevel}
    {TargetIndex : Type targetLevel}
    [sourceFintype : Fintype SourceIndex] [sourceDecidableEq : DecidableEq SourceIndex]
    [blockFintype : Fintype BlockIndex] [blockDecidableEq : DecidableEq BlockIndex]
    [targetFintype : Fintype TargetIndex] [targetDecidableEq : DecidableEq TargetIndex]
    (zeroReindex oneReindex : SourceIndex × BlockIndex ≃ TargetIndex)
    (eigenpath : BlockIndex → C(unitInterval, unitInterval)) (point : unitInterval) :
    C(unitInterval, MatrixDiagonalPath.Mat SourceIndex) →⋆ₐ[ℂ]
      MatrixDiagonalPath.Mat TargetIndex :=
  (@MatrixDiagonalPath.interpolate (SourceIndex × BlockIndex) TargetIndex
    (instFintypeProd SourceIndex BlockIndex)
    targetFintype targetDecidableEq zeroReindex oneReindex point).toStarAlgHom.comp
      (@MatrixDiagonalPath.evaluationBlock BlockIndex SourceIndex
        blockFintype blockDecidableEq sourceFintype sourceDecidableEq eigenpath point)

end

def fiberMap (t : unitInterval) :
    C(unitInterval,PrimeDimensionDrop.Fiber p q) →⋆ₐ[ℂ] PrimeDimensionDrop.Fiber P Q :=
  @OAI.KirchbergRordam.GeneralDropSystem.interpolatedEvaluation (Fin p × Fin q) (OAI.KirchbergRordam.GeneralDropSystem.Slot d) (Fin P × Fin Q)
    (instFintypeProd (Fin p) (Fin q)) inferInstance
    (instFintypeSum (OAI.KirchbergRordam.GeneralDropSystem.Low d) (OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d)) inferInstance
    (instFintypeProd (Fin P) (Fin Q)) inferInstance
    (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d) (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) t

def continuousFamily {Source Target : Type*} [CStarAlgebra Source] [CStarAlgebra Target]
    (family : unitInterval → Source →⋆ₐ[ℂ] Target)
    (continuous_family : ∀ value, Continuous (fun point => family point value)) :
    Source →⋆ₐ[ℂ] C(unitInterval, Target) where
  toFun value := ⟨fun point => family point value, continuous_family value⟩
  map_zero' := ContinuousMap.ext fun point => (family point).map_zero
  map_one' := ContinuousMap.ext fun point => (family point).map_one
  map_add' first second := ContinuousMap.ext fun point => (family point).map_add first second
  map_mul' first second := ContinuousMap.ext fun point => (family point).map_mul first second
  commutes' scalar := ContinuousMap.ext fun point => (family point).commutes scalar
  map_star' value := ContinuousMap.ext fun point => map_star (family point) value

def rawStep :
    C(unitInterval, PrimeDimensionDrop.Fiber p q) →⋆ₐ[ℂ]
      C(unitInterval, PrimeDimensionDrop.Fiber P Q) := by
  classical
  have h_MatrixDiagonalPath_evaluationBlock_continuous {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (ξ : ι → C(unitInterval, unitInterval))
      (f : C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ)) : Continuous (fun t => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t f) :=
    (map_continuous OAI.KirchbergRordam.MatrixDiagonalPath.block).comp (continuous_pi (fun i => f.continuous.comp (ξ i).continuous))
  have h_MatrixDiagonalPath_interpolate_continuous
      {κ : Type 0}
      {ν : Type 0}
      [Fintype κ]
      [DecidableEq κ]
      [Fintype ν]
      [DecidableEq ν]
      (e₀ e₁ : κ ≃ ν) (f : unitInterval → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ)
      (hf : Continuous f) : Continuous (fun t => OAI.KirchbergRordam.MatrixDiagonalPath.interpolate e₀ e₁ t (f t)) := by
    change Continuous (fun t => ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν) *
      (CStarMatrix.reindexₐ ℂ ℂ e₀) (f t) *
      star ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν))
    have hu : Continuous (fun t => ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν)) :=
      continuous_subtype_val.comp (Path.continuous _)
    exact (hu.mul ((map_continuous (CStarMatrix.reindexₐ ℂ ℂ e₀)).comp hf)).mul hu.star
  have h_GeneralDropSystem_fiberMap_continuous (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (path : C(unitInterval, PrimeDimensionDrop.Fiber p q)) :
      Continuous (fun point => OAI.KirchbergRordam.GeneralDropSystem.fiberMap d point path) :=
    h_MatrixDiagonalPath_interpolate_continuous (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d)
      (fun point => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) point path)
      (h_MatrixDiagonalPath_evaluationBlock_continuous (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) path)
  exact
    @OAI.KirchbergRordam.GeneralDropSystem.continuousFamily C(unitInterval, PrimeDimensionDrop.Fiber p q)
        (PrimeDimensionDrop.Fiber P Q)
        (@ContinuousMap.instCStarAlgebra unitInterval (PrimeDimensionDrop.Fiber p q)
          inferInstance inferInstance
          (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
            (Fin p × Fin q) (instFintypeProd (Fin p) (Fin q)) inferInstance))
        (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
          (Fin P × Fin Q) (instFintypeProd (Fin P) (Fin Q)) inferInstance)
        (OAI.KirchbergRordam.GeneralDropSystem.fiberMap d) (h_GeneralDropSystem_fiberMap_continuous d)

def restrictToSubalgebras {Source Target : Type*} [CStarAlgebra Source] [CStarAlgebra Target]
    (hom : Source →⋆ₐ[ℂ] Target) (domain : StarSubalgebra ℂ Source)
    (codomain : StarSubalgebra ℂ Target)
    (map_mem : ∀ value ∈ domain, hom value ∈ codomain) : domain →⋆ₐ[ℂ] codomain :=
  (hom.comp domain.subtype).codRestrict codomain (fun value => map_mem value value.property)

def step := by
  classical
  have h_GeneralBlockReindex_right_low
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (i : P) (j : Q) (l : L) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR ((i,j),.inl l) = ((hL (i,l)).1,.inl (j,(hL (i,l)).2)) := rfl
  have h_GeneralBlockReindex_right_full
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (i : P) (j : Q) (r : R) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR ((i,j),.inr r) = ((hR r).1,.inr ((i,j),(hR r).2)) := rfl
  have h_MatrixBlockReindex_sumBlock_ll {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i j : P) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inl i) (Sum.inl j) = a i j := rfl
  have h_MatrixBlockReindex_sumBlock_lr {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i : P) (j : Q) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inl i) (Sum.inr j) = 0 := rfl
  have h_MatrixBlockReindex_sumBlock_rl {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i : Q) (j : P) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inr i) (Sum.inl j) = 0 := rfl
  have h_MatrixBlockReindex_sumBlock_rr {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i j : Q) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inr i) (Sum.inr j) = b i j := rfl
  have h_MatrixBlockReindex_right_apply {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i j : P) (k l : Q) :
      OAI.KirchbergRordam.MatrixTensor.rightMatrix a (i,k) (j,l) = (if i=j then 1 else 0) * a k l := by
    change (Matrix.kronecker (1 : Matrix P P ℂ) (CStarMatrix.ofMatrix.symm a)) (i,k) (j,l)=_
    simp [Matrix.one_apply]
  have h_MatrixDiagonalPath_block_apply {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (a : ι → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) (i j : κ) (k l : ι) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block a (i,k) (j,l) = if k=l then a k i j else 0 := rfl
  have h_GeneralBlockReindex_right_entry {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m)) x y =
        MatrixTensor.rightMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m)))
          (OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR x) (OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR y) := by
    rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
    · by_cases he : (i,l)=(i',l')
      · cases he; simp [h_GeneralBlockReindex_right_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
      · have hh : (hL (i,l)).1≠(hL (i',l')).1 ∨ (hL (i,l)).2≠(hL (i',l')).2 := by
          by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
        have hil : i≠i' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
        rcases hh with h|h <;> rcases hil with hil|hil <;>
          simp [h_GeneralBlockReindex_right_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply,h,hil]
    · simp [h_GeneralBlockReindex_right_low, h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_lr, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
    · simp [h_GeneralBlockReindex_right_low, h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_rl, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
    · by_cases hr : r=r'
      · subst r'; simp [h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
      · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
          by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
        rcases hrr with h|h <;> simp [h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply,hr,h]
  have h_GeneralBlockReindex_right_matrix {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) :
      CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR)
        (OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m))) =
          MatrixTensor.rightMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m))) := by
    ext x y
    exact h_GeneralBlockReindex_right_entry hL hR a m ((OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR).symm x)
      ((OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR).symm y) |>.trans (by simp [h_MatrixBlockReindex_right_apply] )
  have h_BalancedDropSystem_lower_one  : OAI.KirchbergRordam.BalancedDropSystem.lowerPath 1 = OAI.KirchbergRordam.BalancedDropSystem.half := by
    apply Subtype.ext
    change (1 : ℝ) / 2 = (1 : ℝ) / 2
    rfl
  have h_BalancedDropSystem_upper_one  : OAI.KirchbergRordam.BalancedDropSystem.upperPath 1 = 1 := by
    apply Subtype.ext
    change ((1 : ℝ) + 1) / 2 = 1
    norm_num
  have h_GeneralDropSystem_rawStep_apply (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f) (t : unitInterval) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d f t=OAI.KirchbergRordam.MatrixDiagonalPath.interpolate (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d) t (OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) t f) := rfl
  have h_MatrixBlockReindex_reindex_block {P : Type 0} {Q : Type 0} {R : Type 0} [inst3 : Fintype P] [inst4 : Fintype Q] [inst5 : Fintype R] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [inst8 : DecidableEq R]  (e : P ≃ Q) (a : P → OAI.KirchbergRordam.MatrixDiagonalPath.Mat R) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl R) e) (OAI.KirchbergRordam.MatrixDiagonalPath.block a) =
        OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => a (e.symm i)) := by
    ext i j
    rcases i with ⟨r,p⟩; rcases j with ⟨s,q⟩
    change (if e.symm p=e.symm q then a (e.symm p) r s else 0) =
      (if p=q then a (e.symm p) r s else 0)
    simp only [e.symm.injective.eq_iff]
  have h_GeneralDropSystem_one_eval (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl (Fin p × Fin q)) (OAI.KirchbergRordam.GeneralDropSystem.slotSwap d))
        (OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) 1 f)=
        OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : OAI.KirchbergRordam.GeneralDropSystem.High d => MatrixTensor.rightMatrix (ι:=Fin p) b)
          (fun _ : OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d => f OAI.KirchbergRordam.BalancedDropSystem.half)) := by
    change CStarMatrix.reindexₐ ℂ ℂ _ (OAI.KirchbergRordam.MatrixDiagonalPath.block _) = _
    rw [h_MatrixBlockReindex_reindex_block]
    apply congrArg OAI.KirchbergRordam.MatrixDiagonalPath.block
    funext k
    rcases k with k|k|k <;> simp [h_BalancedDropSystem_lower_one, h_BalancedDropSystem_upper_one, OAI.KirchbergRordam.GeneralDropSystem.slotSwap,OAI.KirchbergRordam.GeneralDropSystem.eigenpath,hb]
  have h_MatrixBlockReindex_reindex_right {P : Type 0} {Q : Type 0} {R : Type 0} {S : Type 0} [inst4 : Fintype P] [inst5 : Fintype Q] [inst6 : Fintype R] [inst7 : Fintype S] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [inst10 : DecidableEq R] [inst11 : DecidableEq S]  (e : P ≃ Q) (f : R ≃ S) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat R) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι:=P) a) =
        OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι:=Q) (CStarMatrix.reindexₐ ℂ ℂ f a) := by
    ext i j
    rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
    change OAI.KirchbergRordam.MatrixTensor.rightMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
    simp only [h_MatrixBlockReindex_right_apply, e.symm.injective.eq_iff]
    rfl
  have h_MatrixBlockReindex_reindex_trans
      {P : Type 0}
      {Q : Type 0}
      [Fintype P]
      [Fintype Q]
      [DecidableEq P]
      [DecidableEq Q]
      {T : Type 0} [Fintype T] [DecidableEq T]
      (e : P ≃ Q) (f : Q ≃ T) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) :
      CStarMatrix.reindexₐ ℂ ℂ (e.trans f) a =
        CStarMatrix.reindexₐ ℂ ℂ f (CStarMatrix.reindexₐ ℂ ℂ e a) := rfl
  have h_MatrixPermutationPath_perm_conjugation {ι : Type 0} [inst1 : Fintype ι] [inst2 : DecidableEq ι]  (σ : Equiv.Perm ι) (a : OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) :
      Unitary.conjStarAlgAut ℂ _ (OAI.KirchbergRordam.MatrixPermutationPath.perm σ) a = CStarMatrix.reindexₐ ℂ ℂ σ a := by
    change σ⁻¹.permMatrix ℂ * CStarMatrix.ofMatrix.symm a * (σ⁻¹.permMatrix ℂ)ᴴ =
      Matrix.reindex σ σ (CStarMatrix.ofMatrix.symm a)
    rw [Matrix.conjTranspose_permMatrix]
    change σ.symm.toPEquiv.toMatrix * CStarMatrix.ofMatrix.symm a * σ.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have h_MatrixDiagonalPath_interpolate_one
      {κ : Type 0}
      {ν : Type 0}
      [Fintype κ]
      [DecidableEq κ]
      [Fintype ν]
      [DecidableEq ν]
      (e₀ e₁ : κ ≃ ν) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) :
      OAI.KirchbergRordam.MatrixDiagonalPath.interpolate e₀ e₁ 1 a = CStarMatrix.reindexₐ ℂ ℂ e₁ a := by
    simp only [OAI.KirchbergRordam.MatrixDiagonalPath.interpolate, StarAlgEquiv.trans_apply, Path.target,
      (@h_MatrixPermutationPath_perm_conjugation)]
    ext i j
    change a (e₀.symm ((e₀.symm.trans e₁).symm i))
      (e₀.symm ((e₀.symm.trans e₁).symm j)) = a (e₁.symm i) (e₁.symm j)
    simp
  have h_GeneralDropSystem_rawStep_one (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d f 1=MatrixTensor.rightMatrix (ι:=Fin P)
        (CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralDropSystem.oneOuter d)
          (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.oneEnd => b),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.oneMid => f OAI.KirchbergRordam.BalancedDropSystem.half)))) := by
    rw [h_GeneralDropSystem_rawStep_apply,h_MatrixDiagonalPath_interpolate_one]
    unfold OAI.KirchbergRordam.GeneralDropSystem.oneReindex
    rw [h_MatrixBlockReindex_reindex_trans,h_GeneralDropSystem_one_eval d f b hb,h_MatrixBlockReindex_reindex_trans,(@h_GeneralBlockReindex_right_matrix),h_MatrixBlockReindex_reindex_right]
  have h_GeneralBlockReindex_left_low
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (l : L) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inl l) = (.inl (i,(hL (j,l)).1),(hL (j,l)).2) := rfl
  have h_GeneralBlockReindex_left_full
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (r : R) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inr r) = (.inr ((i,j),(hR r).1),(hR r).2) := rfl
  have h_MatrixBlockReindex_left_apply {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (i j : P) (k l : Q) :
      OAI.KirchbergRordam.MatrixTensor.leftMatrix a (i,k) (j,l) = a i j * if k=l then 1 else 0 := by
    change (Matrix.kronecker (CStarMatrix.ofMatrix.symm a) (1 : Matrix Q Q ℂ)) (i,k) (j,l)=_
    simp [Matrix.one_apply]
  have h_GeneralBlockReindex_left_entry {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m)) x y =
        MatrixTensor.leftMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m)))
          (OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR x) (OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR y) := by
    rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
    · by_cases he : (j,l)=(j',l')
      · cases he; simp [h_GeneralBlockReindex_left_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
      · have hh : (hL (j,l)).1≠(hL (j',l')).1 ∨ (hL (j,l)).2≠(hL (j',l')).2 := by
          by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
        have hjl : j≠j' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
        rcases hh with h|h <;> rcases hjl with hjl|hjl <;>
          simp [h_GeneralBlockReindex_left_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply,h,hjl]
    · simp [h_GeneralBlockReindex_left_low, h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_lr, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
    · simp [h_GeneralBlockReindex_left_low, h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_rl, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
    · by_cases hr : r=r'
      · subst r'; simp [h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
      · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
          by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
        rcases hrr with h|h <;> simp [h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply,hr,h]
  have h_GeneralBlockReindex_left_matrix {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) :
      CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR)
        (OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m))) =
          MatrixTensor.leftMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m))) := by
    ext x y
    exact h_GeneralBlockReindex_left_entry hL hR a m ((OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR).symm x)
      ((OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR).symm y) |>.trans (by simp [h_MatrixBlockReindex_left_apply] )
  have h_BalancedDropSystem_lower_zero  : OAI.KirchbergRordam.BalancedDropSystem.lowerPath 0 = 0 := by
    apply Subtype.ext
    change (0 : ℝ) / 2 = 0
    norm_num
  have h_BalancedDropSystem_upper_zero  : OAI.KirchbergRordam.BalancedDropSystem.upperPath 0 = OAI.KirchbergRordam.BalancedDropSystem.half := by
    apply Subtype.ext
    change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
    rw [zero_add]
  have h_GeneralDropSystem_zero_eval (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
      OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) 0 f =
        OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : OAI.KirchbergRordam.GeneralDropSystem.Low d => MatrixTensor.leftMatrix (κ:=Fin q) a)
          (fun _ : OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d => f OAI.KirchbergRordam.BalancedDropSystem.half)) := by
    apply congrArg OAI.KirchbergRordam.MatrixDiagonalPath.block
    funext k
    rcases k with k|k|k <;> simp [h_BalancedDropSystem_lower_zero, h_BalancedDropSystem_upper_zero, OAI.KirchbergRordam.GeneralDropSystem.eigenpath,ha]
  have h_MatrixBlockReindex_reindex_left {P : Type 0} {Q : Type 0} {R : Type 0} {S : Type 0} [inst4 : Fintype P] [inst5 : Fintype Q] [inst6 : Fintype R] [inst7 : Fintype S] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [inst10 : DecidableEq R] [inst11 : DecidableEq S]  (e : P ≃ Q) (f : R ≃ S) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (OAI.KirchbergRordam.MatrixTensor.leftMatrix (κ:=R) a) =
        OAI.KirchbergRordam.MatrixTensor.leftMatrix (κ:=S) (CStarMatrix.reindexₐ ℂ ℂ e a) := by
    ext i j
    rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
    change OAI.KirchbergRordam.MatrixTensor.leftMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
    simp only [h_MatrixBlockReindex_left_apply, f.symm.injective.eq_iff]
    rfl
  have h_MatrixPermutationPath_perm_one {ι : Type 0} [inst1 : Fintype ι] [inst2 : DecidableEq ι]  : OAI.KirchbergRordam.MatrixPermutationPath.perm (1 : Equiv.Perm ι) = 1 := by
    apply Subtype.ext
    change (1⁻¹ : Equiv.Perm ι).permMatrix ℂ = 1
    simp
  have h_MatrixDiagonalPath_interpolate_zero
      {κ : Type 0}
      {ν : Type 0}
      [Fintype κ]
      [DecidableEq κ]
      [Fintype ν]
      [DecidableEq ν]
      (e₀ e₁ : κ ≃ ν) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) :
      OAI.KirchbergRordam.MatrixDiagonalPath.interpolate e₀ e₁ 0 a = CStarMatrix.reindexₐ ℂ ℂ e₀ a := by
    simp only [OAI.KirchbergRordam.MatrixDiagonalPath.interpolate, StarAlgEquiv.trans_apply, Path.source,
      (@h_MatrixPermutationPath_perm_one)]
    simp
  have h_GeneralDropSystem_rawStep_zero (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d f 0=MatrixTensor.leftMatrix (κ:=Fin Q)
        (CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralDropSystem.zeroOuter d)
          (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.zeroEnd => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.zeroMid => f OAI.KirchbergRordam.BalancedDropSystem.half)))) := by
    rw [h_GeneralDropSystem_rawStep_apply,h_MatrixDiagonalPath_interpolate_zero,h_GeneralDropSystem_zero_eval d f a ha]
    unfold OAI.KirchbergRordam.GeneralDropSystem.zeroReindex
    rw [h_MatrixBlockReindex_reindex_trans,(@h_GeneralBlockReindex_left_matrix),h_MatrixBlockReindex_reindex_left]
  have h_GeneralDropSystem_rawStep_mem (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (path : C(unitInterval, PrimeDimensionDrop.Fiber p q))
      (path_mem : path ∈ PrimeDimensionDrop.subalgebra p q) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d path ∈ PrimeDimensionDrop.subalgebra P Q := by
    obtain ⟨⟨leftValue, left_eq⟩, ⟨rightValue, right_eq⟩⟩ := path_mem
    exact ⟨⟨_, (h_GeneralDropSystem_rawStep_zero d path leftValue left_eq).symm⟩,
      ⟨_, (h_GeneralDropSystem_rawStep_one d path rightValue right_eq).symm⟩⟩
  exact
    @OAI.KirchbergRordam.GeneralDropSystem.restrictToSubalgebras C(unitInterval, PrimeDimensionDrop.Fiber p q)
        C(unitInterval, PrimeDimensionDrop.Fiber P Q)
        (@ContinuousMap.instCStarAlgebra unitInterval (PrimeDimensionDrop.Fiber p q)
          inferInstance inferInstance
          (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
            (Fin p × Fin q) (instFintypeProd (Fin p) (Fin q)) inferInstance))
        (@ContinuousMap.instCStarAlgebra unitInterval (PrimeDimensionDrop.Fiber P Q)
          inferInstance inferInstance
          (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
            (Fin P × Fin Q) (instFintypeProd (Fin P) (Fin Q)) inferInstance))
        (OAI.KirchbergRordam.GeneralDropSystem.rawStep d) (PrimeDimensionDrop.subalgebra p q) (PrimeDimensionDrop.subalgebra P Q)
        (h_GeneralDropSystem_rawStep_mem d)

end KirchbergRordam.GeneralDropSystem

namespace KirchbergRordam

structure PrimeDropPresentation where
  size : ℕ → ℕ
  exponent : ℕ → ℕ
  size_power : ∀ n, size n=2^(exponent n+1)
  stepData : ∀ n, GeneralDropSystem.Data (size n) (size n+1) (size (n+1)) (size (n+1)+1)
  zero_copies : ∀ n, 2≤(stepData n).zeroEnd+(size n+1)*(stepData n).zeroMid
  one_copies : ∀ n, 2≤(stepData n).oneEnd+size n*(stepData n).oneMid

namespace PrimeDropPresentation
variable (S : PrimeDropPresentation)

def Stage (n : ℕ) : Type := PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)

instance (n : ℕ) : CStarAlgebra (S.Stage n) := inferInstanceAs
  (CStarAlgebra (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))

def chain (S : OAI.KirchbergRordam.PrimeDropPresentation) : CStarInductiveLimit.Chain.{0} := by
  classical
  have h_GeneralDropSystem_eigen_cover {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (s : unitInterval) : ∃ i t, OAI.KirchbergRordam.GeneralDropSystem.eigenpath d i t=s := by
    by_cases hs : (s:ℝ)≤1/2
    · refine ⟨.inl ⟨0,d.lower_pos⟩,⟨2*s,by constructor <;> linarith [s.property.1]⟩,?_⟩
      apply Subtype.ext
      change 2*(s:ℝ)/2=(s:ℝ)
      ring
    · refine ⟨.inr (.inl ⟨0,d.upper_pos⟩),⟨2*s-1,by constructor <;> linarith [s.property.2]⟩,?_⟩
      apply Subtype.ext
      change ((2*(s:ℝ)-1)+1)/2=(s:ℝ)
      ring
  have h_MatrixDiagonalPath_block_apply {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (a : ι → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) (i j : κ) (k l : ι) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block a (i,k) (j,l) = if k=l then a k i j else 0 := rfl
  have h_MatrixDiagonalPath_block_injective {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  : Function.Injective (OAI.KirchbergRordam.MatrixDiagonalPath.block (ι:=ι) (κ:=κ)) := by
    intro a b h
    funext k
    ext i j
    have := congrArg (fun m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ×ι) => m (i,k) (j,k)) h
    simpa [h_MatrixDiagonalPath_block_apply, h_MatrixDiagonalPath_block_apply] using this
  have h_MatrixDiagonalPath_diagonal_injective {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (ξ : ι → C(unitInterval, unitInterval))
      (hcover : ∀ s : unitInterval, ∃ i t, ξ i t = s) :
      Function.Injective (OAI.KirchbergRordam.MatrixDiagonalPath.diagonal (κ:=κ) ξ) := by
    intro f g h
    ext s a b
    obtain ⟨i,t,rfl⟩ := hcover s
    have ht : OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => f (ξ i t)) = OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => g (ξ i t)) :=
      DFunLike.congr_fun h t
    exact congrFun (congrFun (congrFun (h_MatrixDiagonalPath_block_injective ht) i) a) b
  have h_GeneralDropSystem_rawStep_injective {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  : Function.Injective (OAI.KirchbergRordam.GeneralDropSystem.rawStep d) := by
    intro f g h
    apply h_MatrixDiagonalPath_diagonal_injective (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) (h_GeneralDropSystem_eigen_cover d)
    apply ContinuousMap.ext
    intro t
    exact (OAI.KirchbergRordam.MatrixDiagonalPath.interpolate (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d) t).injective (DFunLike.congr_fun h t)
  have h_GeneralDropSystem_step_injective {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  : Function.Injective (OAI.KirchbergRordam.GeneralDropSystem.step d) := by
    intro f g h
    apply Subtype.ext
    exact h_GeneralDropSystem_rawStep_injective d (congrArg Subtype.val h)
  have h_GeneralDropSystem_step_norm {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : PrimeDimensionDrop.Algebra p q) : ‖OAI.KirchbergRordam.GeneralDropSystem.step d f‖=‖f‖ :=
    NonUnitalStarAlgHom.norm_map _ (h_GeneralDropSystem_step_injective d) f
  have h_PrimeDropPresentation_stage_step_norm  (S : OAI.KirchbergRordam.PrimeDropPresentation) :
      ∀ stage (element : S.Stage stage),
        ‖GeneralDropSystem.step (S.stepData stage) element‖ = ‖element‖ :=
    fun stage element => (@h_GeneralDropSystem_step_norm) (S.stepData stage) element
  exact
    @CStarInductiveLimit.Chain.mk.{0}
        (@OAI.KirchbergRordam.PrimeDropPresentation.Stage S)
        (@OAI.KirchbergRordam.PrimeDropPresentation.instCStarAlgebraStage S)
        (fun stage : Nat => @GeneralDropSystem.step
          (@PrimeDropPresentation.size S stage) (Nat.succ (@PrimeDropPresentation.size S stage))
          (@PrimeDropPresentation.size S (Nat.succ stage))
          (Nat.succ (@PrimeDropPresentation.size S (Nat.succ stage)))
          (@PrimeDropPresentation.stepData S stage))
        (@h_PrimeDropPresentation_stage_step_norm S)

abbrev system := S.chain.system

end PrimeDropPresentation
end KirchbergRordam

namespace KirchbergRordam.StandardPrimeMultiplicity

def copies (p : ℕ) : ℕ := (p-1)*(p^4+p^2+1)

def lower (p : ℕ) : ℕ := p*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p+1

def upper (p : ℕ) : ℕ := (p+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p+1

def middle (p : ℕ) : ℕ := p*(p+1)*(OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p)^2-1

def next (p : ℕ) : ℕ := p^7

def data (p : ℕ) (hp : 2≤p) : GeneralDropSystem.Data p (p+1) (OAI.KirchbergRordam.StandardPrimeMultiplicity.next p) (OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1) := by
  classical
  have h_StandardPrimeMultiplicity_dimension  (p : ℕ) (hp : 2≤p) : p+p*(p+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p := by
    cases p with
    | zero => omega
    | succ p => simp only [OAI.KirchbergRordam.StandardPrimeMultiplicity.copies,OAI.KirchbergRordam.StandardPrimeMultiplicity.next,Nat.add_sub_cancel]; ring
  have h_StandardPrimeMultiplicity_lower_pos  (p : ℕ) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p := by unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.lower; omega
  have h_StandardPrimeMultiplicity_one_low  (p : ℕ) (hp : 2≤p) : p*OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p := by
    rw [←h_StandardPrimeMultiplicity_dimension p hp]
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.upper
    ring
  have h_StandardPrimeMultiplicity_copies_pos  (p : ℕ) (hp : 2≤p) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p := by
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.copies
    exact Nat.mul_pos (by omega) (by positivity)
  have h_StandardPrimeMultiplicity_middle_add_one  (p : ℕ) (hp : 2≤p) : OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p+1=p*(p+1)*(OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p)^2 := by
    have hc := h_StandardPrimeMultiplicity_copies_pos p hp
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.middle
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have h_StandardPrimeMultiplicity_one_mid  (p : ℕ) (hp : 2≤p) : OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p := by
    have he : (OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p)+1=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p+1 := by
      rw [add_assoc,h_StandardPrimeMultiplicity_middle_add_one p hp,←h_StandardPrimeMultiplicity_dimension p hp]
      unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.lower
      ring
    omega
  have h_StandardPrimeMultiplicity_upper_pos  (p : ℕ) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p := by unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.upper; omega
  have h_StandardPrimeMultiplicity_zero_low  (p : ℕ) (hp : 2≤p) : (p+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1 := by
    rw [←h_StandardPrimeMultiplicity_dimension p hp]
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.lower
    ring
  have h_StandardPrimeMultiplicity_zero_mid  (p : ℕ) (hp : 2≤p) : OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p=OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p*(OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1) := by
    have he : (OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p)+1=OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p*(OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1)+1 := by
      rw [add_assoc,h_StandardPrimeMultiplicity_middle_add_one p hp,←h_StandardPrimeMultiplicity_dimension p hp]
      unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.upper
      ring
    omega
  exact {
    lower := OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p
    upper := OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p
    middle := OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p
    zeroEnd := 1
    zeroMid := OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p
    oneEnd := 1
    oneMid := OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p
    lower_pos := h_StandardPrimeMultiplicity_lower_pos p
    upper_pos := h_StandardPrimeMultiplicity_upper_pos p
    zero_low := by simpa using h_StandardPrimeMultiplicity_zero_low p hp
    zero_mid := h_StandardPrimeMultiplicity_zero_mid p hp
    one_low := by simpa using h_StandardPrimeMultiplicity_one_low p hp
    one_mid := h_StandardPrimeMultiplicity_one_mid p hp
    zero_dim := by simpa using h_StandardPrimeMultiplicity_dimension p hp
    one_dim := by have := h_StandardPrimeMultiplicity_dimension p hp; omega
  }

def size : ℕ → ℕ
  | 0 => 2
  | n+1 => OAI.KirchbergRordam.StandardPrimeMultiplicity.next (size n)

end KirchbergRordam.StandardPrimeMultiplicity

namespace KirchbergRordam.StandardPrimeModel
open StandardPrimeMultiplicity
def presentation : OAI.KirchbergRordam.PrimeDropPresentation := by
  classical
  have h_StandardPrimeMultiplicity_copies_pos  (p : ℕ) (hp : 2≤p) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p := by
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.copies
    exact Nat.mul_pos (by omega) (by positivity)
  have h_StandardPrimeMultiplicity_size_zero  : OAI.KirchbergRordam.StandardPrimeMultiplicity.size 0=2 := rfl
  have h_StandardPrimeMultiplicity_size_succ  (n : ℕ) : OAI.KirchbergRordam.StandardPrimeMultiplicity.size (n+1)=OAI.KirchbergRordam.StandardPrimeMultiplicity.next (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) := rfl
  have h_StandardPrimeMultiplicity_size_power  (n : ℕ) : OAI.KirchbergRordam.StandardPrimeMultiplicity.size n=2^(7^n) := by
    induction n with
    | zero => simp [h_StandardPrimeMultiplicity_size_zero]
    | succ n ih => rw [h_StandardPrimeMultiplicity_size_succ,OAI.KirchbergRordam.StandardPrimeMultiplicity.next,ih,←pow_mul,pow_succ]
  have h_StandardPrimeMultiplicity_next_two  (p : ℕ) (hp : 2≤p) : 2≤OAI.KirchbergRordam.StandardPrimeMultiplicity.next p := by
    exact hp.trans (Nat.le_self_pow (by decide) p)
  have h_StandardPrimeMultiplicity_size_two  (n : ℕ) : 2 ≤ OAI.KirchbergRordam.StandardPrimeMultiplicity.size n := by
    induction n with
    | zero => simp [h_StandardPrimeMultiplicity_size_zero]
    | succ n ih => exact h_StandardPrimeMultiplicity_next_two _ ih
  exact {
    size := OAI.KirchbergRordam.StandardPrimeMultiplicity.size
    exponent n := 7^n-1
    size_power n := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow n 7 (by decide))]
      exact h_StandardPrimeMultiplicity_size_power n
    stepData n := OAI.KirchbergRordam.StandardPrimeMultiplicity.data (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) (h_StandardPrimeMultiplicity_size_two n)
    zero_copies n := by
      change 2≤1+(OAI.KirchbergRordam.StandardPrimeMultiplicity.size n+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n)
      have h := h_StandardPrimeMultiplicity_copies_pos (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) (h_StandardPrimeMultiplicity_size_two n)
      nlinarith [h_StandardPrimeMultiplicity_size_two n]
    one_copies n := by
      change 2≤1+OAI.KirchbergRordam.StandardPrimeMultiplicity.size n*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n)
      have h := h_StandardPrimeMultiplicity_copies_pos (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) (h_StandardPrimeMultiplicity_size_two n)
      nlinarith [h_StandardPrimeMultiplicity_size_two n]
  }

end KirchbergRordam.StandardPrimeModel

namespace KirchbergRordam.JiangSu

def Algebra : Type := CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system

instance : CStarAlgebra OAI.KirchbergRordam.JiangSu.Algebra := inferInstanceAs
  (CStarAlgebra (CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system))

end KirchbergRordam.JiangSu

namespace KirchbergRordam

def HasNoCharacters (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ χ : A →⋆ₙₐ[ℂ] ℂ, χ=0



end KirchbergRordam
end
end OAI


