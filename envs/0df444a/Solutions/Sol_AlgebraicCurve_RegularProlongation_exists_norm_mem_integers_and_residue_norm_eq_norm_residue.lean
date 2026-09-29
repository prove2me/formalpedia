-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_norm_mem_integers_and_residue_norm_eq_norm_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/35bc46c4-b133-59aa-90d9-df570de1c247

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue

set_option autoImplicit false

open AlgebraicCurve

namespace Ws49
namespace NormReduce

variable {L F F' k k' : Type*} [Field L] [Field F] [Field F'] [Field k] [Field k']
  [Algebra L F] [Algebra L F']

theorem residue_eq_zero_iff {A : ValuationSubring L} [Algebra (IsLocalRing.ResidueField ↥A) k']
    (R' : RegularProlongation A F' k') (x : R'.integers) :
    R'.residue x = 0 ↔ R'.integers.valuation (x : F') < 1 := by
  rw [← ValuationSubring.valuation_lt_one_iff, ← R'.ker_residue, RingHom.mem_ker]

end Ws49.NormReduce

open Ws49.NormReduce in
theorem solution
    {L F F' k k' : Type*} [Field L] [Field F] [Field F'] [Field k] [Field k']
    [Algebra L F] [Algebra L F']
    (A : ValuationSubring L) [Algebra (IsLocalRing.ResidueField ↥A) k] [Algebra (IsLocalRing.ResidueField ↥A) k']
    (R : AlgebraicCurve.RegularProlongation A F k) (R' : AlgebraicCurve.RegularProlongation A F' k')
    (φ : F →ₐ[L] F') (ι : k →+* k')

    (hint : ∀ f : F, φ f ∈ R'.integers ↔ f ∈ R.integers)
    (hres : ∀ (f : F) (hf : f ∈ R.integers) (hf' : φ f ∈ R'.integers), R'.residue ⟨φ f, hf'⟩ = ι (R.residue ⟨f, hf⟩))

    (n : ℕ) (hn : AlgebraicCurve.finrankAlong L φ = n)
    (b : Fin n → F') (hb : ∀ i, b i ∈ R'.integers)
    (hli : letI := ι.toAlgebra; LinearIndependent k (fun i => R'.residue ⟨b i, hb i⟩))
    (hsp : letI := ι.toAlgebra; Submodule.span k (Set.range (fun i => R'.residue ⟨b i, hb i⟩)) = ⊤)
    (h : F') (hh : h ∈ R'.integers) :
    ∃ hN : (letI := AlgebraicCurve.algebraAlong φ; Algebra.norm F h) ∈ R.integers,
      R.residue ⟨_, hN⟩ = (letI := ι.toAlgebra; Algebra.norm k (R'.residue ⟨h, hh⟩)) := by
  classical
  letI : Algebra F F' := AlgebraicCurve.algebraAlong φ
  letI : Algebra k k' := ι.toAlgebra
  have hφ : ∀ c : F, algebraMap F F' c = φ c := fun _ => rfl
  have hι : ∀ a : k, algebraMap k k' a = ι a := fun _ => rfl

  set O' := R'.integers with hO'
  set v' := R'.integers.valuation with hv'

  let bbar : Module.Basis (Fin n) k k' := Module.Basis.mk hli (by rw [hsp])
  have hbbar : ∀ i, bbar i = R'.residue ⟨b i, hb i⟩ := fun i => by simp [bbar]

  have hcoord : ∀ c : Fin n → F, (∑ i, φ (c i) * b i) ∈ O' → ∀ i, c i ∈ R.integers := by
    intro c hx
    by_contra hnot
    push_neg at hnot

    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      obtain ⟨i, _⟩ := hnot; exact ⟨i, Finset.mem_univ _⟩
    obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ (fun i => v' (φ (c i))) hne
    have hcj : c j ∉ R.integers := by
      obtain ⟨i₀, hi₀⟩ := hnot
      intro hcjR

      have h1 : v' (φ (c j)) ≤ 1 := (R'.integers.valuation_le_one_iff _).mpr ((hint _).mpr hcjR)
      have h2 : v' (φ (c i₀)) ≤ 1 := (hjmax i₀ (Finset.mem_univ _)).trans h1
      exact hi₀ ((hint _).mp ((R'.integers.valuation_le_one_iff _).mp h2))
    have hφcj : φ (c j) ∉ O' := fun h => hcj ((hint _).mp h)
    have hcj0 : c j ≠ 0 := by rintro h0; exact hcj (h0 ▸ zero_mem _)
    have hφcj0 : φ (c j) ≠ 0 := (map_ne_zero φ).mpr hcj0

    have he : ∀ i, c i / c j ∈ R.integers := by
      intro i
      apply (hint _).mp
      rw [map_div₀]
      apply (R'.integers.valuation_le_one_iff _).mp
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff v').mpr hφcj0))]
      exact hjmax i (Finset.mem_univ _)

    have hvx : v' ((∑ i, φ (c i) * b i) / φ (c j)) < 1 := by
      rw [map_div₀]
      have hxle : v' (∑ i, φ (c i) * b i) ≤ 1 := (R'.integers.valuation_le_one_iff _).mpr hx
      have hgt : 1 < v' (φ (c j)) := by
        rw [← not_le]; intro hle; exact hφcj ((R'.integers.valuation_le_one_iff _).mp hle)
      rw [div_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff v').mpr hφcj0))]
      exact hxle.trans_lt hgt

    have hmem : (∑ i, φ (c i) * b i) / φ (c j) ∈ O' := (R'.integers.valuation_le_one_iff _).mp hvx.le
    have hsum : (∑ i, φ (c i) * b i) / φ (c j) = ∑ i, φ (c i / c j) * b i := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_div₀]; ring
    have hres0 : R'.residue ⟨_, hmem⟩ = 0 := (residue_eq_zero_iff R' _).mpr hvx
    have hresSum : R'.residue ⟨_, hmem⟩ = ∑ i, ι (R.residue ⟨c i / c j, he i⟩) • bbar i := by
      have : (⟨_, hmem⟩ : O') = ∑ i, (⟨φ (c i / c j), (hint _).mpr (he i)⟩ : O') * ⟨b i, hb i⟩ := by
        apply Subtype.ext; simp only [hsum]; push_cast; rfl
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hres (c i / c j) (he i), hbbar, smul_eq_mul]
    have hindep := bbar.linearIndependent
    have hcoef : ∀ i, ι (R.residue ⟨c i / c j, he i⟩) = 0 := by
      have h0 : ∑ i, ι (R.residue ⟨c i / c j, he i⟩) • bbar i = 0 := by rw [← hresSum, hres0]

      have h0' : ∑ i, (R.residue ⟨c i / c j, he i⟩) • bbar i = 0 := by
        simp only [Algebra.smul_def, hι] at h0
        exact h0
      intro i
      have := Fintype.linearIndependent_iff.mp hindep (fun i => R.residue ⟨c i / c j, he i⟩) h0' i
      rw [this, map_zero]
    have hj1 : ι (R.residue ⟨c j / c j, he j⟩) = 1 := by
      have : (⟨c j / c j, he j⟩ : R.integers) = 1 := Subtype.ext (div_self hcj0)
      rw [this, map_one, map_one]
    exact one_ne_zero (hj1.symm.trans (hcoef j))

  have hliF : LinearIndependent F b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i

    by_contra hci
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ _⟩
    obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ (fun i => v' (φ (c i))) hne
    have hcj0 : c j ≠ 0 := by
      intro h0
      have : v' (φ (c i)) ≤ v' (φ (c j)) := hjmax i (Finset.mem_univ _)
      rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero] at this
      exact hci this

    have he : ∀ i, c i / c j ∈ R.integers := by
      intro i
      apply (hint _).mp
      rw [map_div₀]
      apply (R'.integers.valuation_le_one_iff _).mp
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff v').mpr ((map_ne_zero φ).mpr hcj0)))]
      exact hjmax i (Finset.mem_univ _)
    have hsum0 : ∑ i, φ (c i / c j) * b i = 0 := by
      have hc' : ∑ i, φ (c i) * b i = 0 := by simpa only [Algebra.smul_def, hφ] using hc
      have : (∑ i, φ (c i) * b i) / φ (c j) = 0 := by rw [hc', zero_div]
      rw [Finset.sum_div] at this
      rw [← this]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_div₀]; ring
    have hmem : (∑ i, φ (c i / c j) * b i) ∈ O' := by rw [hsum0]; exact zero_mem _
    have hres0 : R'.residue ⟨_, hmem⟩ = 0 := by
      have : (⟨_, hmem⟩ : O') = 0 := Subtype.ext hsum0
      rw [this, map_zero]
    have hresSum : R'.residue ⟨_, hmem⟩ = ∑ i, (R.residue ⟨c i / c j, he i⟩) • bbar i := by
      have : (⟨_, hmem⟩ : O') = ∑ i, (⟨φ (c i / c j), (hint _).mpr (he i)⟩ : O') * ⟨b i, hb i⟩ := by
        apply Subtype.ext; push_cast; rfl
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hres (c i / c j) (he i), hbbar, Algebra.smul_def, hι]
    have hcoef := Fintype.linearIndependent_iff.mp bbar.linearIndependent (fun i => R.residue ⟨c i / c j, he i⟩) (by rw [← hresSum, hres0]) j
    have hj1 : R.residue ⟨c j / c j, he j⟩ = 1 := by
      have : (⟨c j / c j, he j⟩ : R.integers) = 1 := Subtype.ext (div_self hcj0)
      rw [this, map_one]
    exact one_ne_zero (hj1.symm.trans hcoef)

  have hn' : Fintype.card (Fin n) = Module.finrank F F' := by rw [Fintype.card_fin]; exact hn.symm
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      subst h0
      have : (⊤ : Submodule k k') = ⊥ := by
        rw [← hsp, Set.range_eq_empty, Submodule.span_empty]
      exact bot_ne_top this.symm
    · exact hpos
  have hfr : Module.finrank F F' = n := hn
  haveI : FiniteDimensional F F' := Module.finite_of_finrank_pos (hfr ▸ hnpos)
  haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  let B : Module.Basis (Fin n) F F' := basisOfLinearIndependentOfCardEqFinrank hliF hn'
  have hB : ∀ i, B i = b i := fun i => by simp [B]

  set Mh : Matrix (Fin n) (Fin n) F := Algebra.leftMulMatrix B h with hMh
  have hMcol : ∀ j, h * b j = ∑ i, φ (Mh i j) * b i := by
    intro j
    have hrep : ∑ i, (B.repr (h * b j) i) • B i = h * b j := B.sum_repr (h * b j)
    have hentry : ∀ i, Mh i j = B.repr (h * b j) i := by
      intro i
      rw [hMh, Algebra.leftMulMatrix_eq_repr_mul, hB]
    rw [← hrep]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hentry, hB, Algebra.smul_def, hφ]
  have hMint : ∀ i j, Mh i j ∈ R.integers := by
    intro i j
    have hx : (∑ i, φ (Mh i j) * b i) ∈ O' := by
      rw [← hMcol]; exact mul_mem hh (hb j)
    exact hcoord (fun i => Mh i j) hx i

  let M' : Matrix (Fin n) (Fin n) R.integers := fun i j => ⟨Mh i j, hMint i j⟩
  have hM' : (R.integers.subtype).mapMatrix M' = Mh := by ext i j; rfl
  have hnorm : Algebra.norm F h = Mh.det := Algebra.norm_eq_matrix_det B h
  have hdet : Mh.det = ((M'.det : R.integers) : F) := by
    rw [← hM']; exact (RingHom.map_det R.integers.subtype M').symm
  have hN : Algebra.norm F h ∈ R.integers := by rw [hnorm, hdet]; exact (M'.det).2
  refine ⟨hN, ?_⟩

  have hsub : (⟨Algebra.norm F h, hN⟩ : R.integers) = M'.det := Subtype.ext (hnorm.trans hdet)
  have hsub' : R.residue ⟨Algebra.norm F h, hN⟩ = R.residue M'.det := congrArg _ hsub
  rw [hsub', RingHom.map_det]
  have hredM : (R.residue).mapMatrix M' = Algebra.leftMulMatrix bbar (R'.residue ⟨h, hh⟩) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]

    have hcolres : R'.residue ⟨h, hh⟩ * bbar j = ∑ i, (R.residue (M' i j)) • bbar i := by
      have hO : (⟨h, hh⟩ : O') * ⟨b j, hb j⟩ = ∑ i, (⟨φ (Mh i j), (hint _).mpr (hMint i j)⟩ : O') * ⟨b i, hb i⟩ := by
        apply Subtype.ext; push_cast; exact hMcol j
      rw [hbbar j, ← map_mul, hO, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hres (Mh i j) (hMint i j), hbbar, Algebra.smul_def, hι]
    rw [hcolres, Module.Basis.repr_sum_self]
  rw [hredM, ← Algebra.norm_eq_matrix_det bbar]

end S_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue (solution)
