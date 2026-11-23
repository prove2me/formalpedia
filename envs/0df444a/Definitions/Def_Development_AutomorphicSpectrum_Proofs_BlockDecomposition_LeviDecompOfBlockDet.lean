-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:27.183262+00:00
-- url     : https://prove2.me/theorems/5a8dc18a-0895-4e82-9062-dcb9bbfcad21
-- title:
--   Levi Decomp Of Block Det
-- statement:
--   Definitions and structural lemmas for Levi Decomp Of Block Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
theorem mem_stab_univ {g : GL (ι ⊕ ι) R} :
    g ∈ stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) ↔
      ∀ r c : ι, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr r) (Sum.inl c) = 0 ∧
        ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr r) (Sum.inl c) = 0 := by
  constructor
  · intro h r c
    exact h (Sum.inr r) (by simp) (Sum.inl c) (by simp)
  · intro h r hr c hc
    obtain ⟨c', -, rfl⟩ := hc
    rcases r with r | r
    · exact absurd ⟨r, trivial, rfl⟩ hr
    · exact h r c'
theorem blk_mul (x y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (hy : ∀ r c, y (Sum.inr r) (Sum.inl c) = 0) :
    (x * y).toBlocks₁₁ = x.toBlocks₁₁ * y.toBlocks₁₁ := by
  ext r c
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, hy]
theorem blk_one : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ = 1 := by
  ext r c
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]
def piP : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) →* GL ι R where
  toFun q := ⟨(q.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁, ((q.1⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁,
    by rw [← blk_mul _ _ (fun r c => (mem_stab_univ.1 q.2 r c).2), Units.mul_inv, blk_one],
    by rw [← blk_mul _ _ (fun r c => (mem_stab_univ.1 q.2 r c).1), Units.inv_mul, blk_one]⟩
  map_one' := Units.ext (by simp [blk_one])
  map_mul' a b := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk]
    exact blk_mul _ _ (fun r c => (mem_stab_univ.1 b.2 r c).1))
theorem dual_mul (σ : R →+* R) (a b : Matrix ι ι R) : (aᵀ.map σ) * (bᵀ.map σ) = ((b * a)ᵀ).map σ := by
  rw [Matrix.transpose_mul, Matrix.map_mul]
def jG (σ : R →+* R) : GL ι R →* GL (ι ⊕ ι) R where
  toFun m := ⟨fromBlocks (m : Matrix ι ι R) 0 0 (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map σ),
    fromBlocks ((m⁻¹ : GL ι R) : Matrix ι ι R) 0 0 ((m : Matrix ι ι R)ᵀ.map σ),
    by
      rw [Matrix.fromBlocks_multiply, dual_mul]
      simp [Matrix.map_one _ (map_zero σ) (map_one σ)],
    by
      rw [Matrix.fromBlocks_multiply, dual_mul]
      simp [Matrix.map_one _ (map_zero σ) (map_one σ)]⟩
  map_one' := Units.ext (by simp [Matrix.map_one _ (map_zero σ) (map_one σ)])
  map_mul' a b := Units.ext (by
    simp only [Units.val_mul, Units.val_mk, Matrix.fromBlocks_multiply, _root_.mul_inv_rev]
    simp [Matrix.transpose_mul, Matrix.map_mul])
theorem jG_val (σ : R →+* R) (m : GL ι R) : ((jG σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    fromBlocks (m : Matrix ι ι R) 0 0 (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map σ) := rfl
theorem jG_inv_val (σ : R →+* R) (m : GL ι R) : (((jG σ m)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    fromBlocks ((m⁻¹ : GL ι R) : Matrix ι ι R) 0 0 ((m : Matrix ι ι R)ᵀ.map σ) := rfl
theorem jG_mem_stab (σ : R →+* R) (m : GL ι R) : jG σ m ∈ stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) :=
  mem_stab_univ.2 fun r c => by rw [jG_val, jG_inv_val]; simp
theorem jG_mem_uSub (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (m : GL ι R) : jG A.σ m ∈ A.uSub ε ι := by
  show ((jG A.σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι * ((jG A.σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = Ad.J R ε ι
  have hmm : ((((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ).map A.σ) = ((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ := by
    ext r c; simp [h]
  have h1 : (m : Matrix ι ι R)ᵀ * ((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have h2 : (((m⁻¹ : GL ι R) : Matrix ι ι R).map A.σ) * ((m : Matrix ι ι R).map A.σ) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ)ᵀ = ((m⁻¹ : GL ι R) : Matrix ι ι R).map A.σ := by
    ext r c; simp
  rw [jG_val, Ad.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, hmm, h3]
  simp [-Matrix.coe_units_inv, h1, h2, Matrix.mul_assoc]
section Alg
variable (A : Ad E R) (ε : ℤˣ)
def piQ : A.uQ ε (Set.univ : Set ι) →* GL ι R where
  toFun q := piP ⟨q.1.1, Subgroup.mem_subgroupOf.1 q.2⟩
  map_one' := map_one piP
  map_mul' a b := map_mul piP ⟨a.1.1, Subgroup.mem_subgroupOf.1 a.2⟩ ⟨b.1.1, Subgroup.mem_subgroupOf.1 b.2⟩
def jQ (h : ∀ x, A.σ (A.σ x) = x) : GL ι R →* A.uQ ε (Set.univ : Set ι) where
  toFun m := ⟨⟨jG A.σ m, jG_mem_uSub A ε h m⟩, Subgroup.mem_subgroupOf.2 (jG_mem_stab _ m)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (jG A.σ)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (jG A.σ) a b))
end Alg
def tau (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) : E →+* E where
  toFun x := (h x).choose
  map_one' := hi (by rw [← (h 1).choose_spec]; simp)
  map_mul' a b := hi (by rw [← (h (a * b)).choose_spec, map_mul, map_mul, map_mul, ← (h a).choose_spec, ← (h b).choose_spec])
  map_zero' := hi (by rw [← (h 0).choose_spec]; simp)
  map_add' a b := hi (by rw [← (h (a + b)).choose_spec, map_add, map_add, map_add, ← (h a).choose_spec, ← (h b).choose_spec])
section Top
variable [TopologicalSpace R] [IsTopologicalRing R]
end Top
section Main
variable [TopologicalSpace R]
end Main
section Ext
variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
end Ext
end GlobalTheory.CompanionTheory.RgEisLevi


