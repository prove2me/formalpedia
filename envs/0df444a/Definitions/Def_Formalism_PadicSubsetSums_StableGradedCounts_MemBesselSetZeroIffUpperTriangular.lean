-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:28.729044+00:00
-- url     : https://prove2.me/theorems/ec24eab9-403a-40dd-b176-4304206c2c6f
-- title:
--   Mem Bessel Set Zero Iff Upper Triangular
-- statement:
--   Definitions and structural lemmas for Mem Bessel Set Zero Iff Upper Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8


set_option autoImplicit false
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section GelfandTrick
variable {G : Type} [Group G] [Fintype G]
noncomputable def antiLift (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) :
    MonoidAlgebra ℂ G →ₐ[ℂ] (MonoidAlgebra ℂ G)ᵐᵒᵖ :=
  MonoidAlgebra.lift ℂ _ G
    { toFun := fun g => MulOpposite.op (MonoidAlgebra.of ℂ G (σ g))
      map_one' := by
        have h1 : σ 1 = 1 := by
          have := hσ 1 1
          rw [mul_one] at this
          exact (mul_eq_left.mp this.symm)
        rw [h1, map_one, MulOpposite.op_one]
      map_mul' := by
        intro x y
        rw [hσ, map_mul, MulOpposite.op_mul] }
end GelfandTrick
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Matrix
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section GG
variable {K : Type} [Field K] {N : ℕ}
def IsUT (A : Matrix (Fin N) (Fin N) K) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0
theorem IsUT.det {A : Matrix (Fin N) (Fin N) K} (h : IsUT A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h.1 i
noncomputable def utMk (A : Matrix (Fin N) (Fin N) K) (h : IsUT A) : GL (Fin N) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h.det]; exact one_ne_zero)
@[simp] theorem utMk_val (A : Matrix (Fin N) (Fin N) K) (h : IsUT A) :
    ((utMk A h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = A := rfl
theorem IsUT.one : IsUT (1 : Matrix (Fin N) (Fin N) K) :=
  ⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_gt h)⟩
theorem IsUT.mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUT A) (hB : IsUT B) : IsUT (A * B) := by
  constructor
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.1, hB.1, one_mul]
    · intro m _ hm
      rcases lt_or_gt_of_ne hm with h | h
      · rw [hA.2 i m h, zero_mul]
      · rw [hB.2 m i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hA.2 i m h, zero_mul]
    · rw [hB.2 m j (lt_of_lt_of_le hij h), mul_zero]
def edgeSum (A : Matrix (Fin N) (Fin N) K) : K :=
  ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then A i j else 0
theorem edgeSum_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUT A) (hB : IsUT B) :
    edgeSum (A * B) = edgeSum A + edgeSum B := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hij : i ≠ j := by
      intro h'; rw [h'] at h; omega
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      hA.1, hB.1, one_mul, mul_one, Finset.sum_eq_zero, add_zero, add_comm]
    intro m hm
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
    rcases lt_or_ge m i with h1 | h1
    · rw [hA.2 i m h1, zero_mul]
    · have : j < m := by
        have h2 : (m : ℕ) ≠ i := fun h' => hm.2 (Fin.ext h')
        have h3 : (m : ℕ) ≠ j := fun h' => hm.1 (Fin.ext h')
        have h4 : (i : ℕ) ≤ m := h1
        show (j : ℕ) < m
        omega
      rw [hB.2 m j this, mul_zero]
  · rw [add_zero]
theorem IsUT.inv_val (u : GL (Fin N) K) (h : IsUT (u : Matrix (Fin N) (Fin N) K)) :
    IsUT ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  have hlow : ∀ i j, j < i → ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j = 0 := by
    intro i j hij
    rw [Matrix.coe_units_inv]
    have : Invertible (u : Matrix (Fin N) (Fin N) K) := u.invertible
    have hb : Matrix.BlockTriangular (u : Matrix (Fin N) (Fin N) K) id := fun i j hij => h.2 i j hij
    exact Matrix.blockTriangular_inv_of_blockTriangular hb hij
  refine ⟨fun i => ?_, hlow⟩
  have h1 : ((u * u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i i = 1 := by
    rw [mul_inv_cancel]; simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, h.1, one_mul] at h1
  · exact h1
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h' | h'
    · rw [h.2 i m h', zero_mul]
    · rw [hlow m i h', mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'
def uniSub (K : Type) [Field K] (N : ℕ) : Subgroup (GL (Fin N) K) where
  carrier := {u | IsUT (u : Matrix (Fin N) (Fin N) K)}
  mul_mem' := fun {a b} ha hb => by
    show IsUT ((a * b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    rw [Units.val_mul]; exact IsUT.mul ha hb
  one_mem' := by
    show IsUT ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    rw [Units.val_one]; exact IsUT.one
  inv_mem' := fun {a} ha => IsUT.inv_val a ha
noncomputable def uniChar (ψ₀ : AddChar K ℂ) (N : ℕ) : uniSub K N →* ℂˣ where
  toFun u := (ψ₀.toMonoidHom.toHomUnits) (Multiplicative.ofAdd (edgeSum ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
  map_one' := by
    have : edgeSum (((1 : uniSub K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 0 := by
      have h := edgeSum_mul (K := K) (N := N) IsUT.one IsUT.one
      rw [mul_one] at h
      simpa using h
    rw [this]; simp
  map_mul' := fun a b => by
    have : edgeSum (((a * b : uniSub K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        edgeSum ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) +
          edgeSum ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
      rw [Subgroup.coe_mul, Units.val_mul]
      exact edgeSum_mul a.2 b.2
    rw [this, ofAdd_add, map_mul]
end GG
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section Comb
variable {N : ℕ}
end Comb
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Matrix
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section Bruhat
variable {K : Type} [Field K] {N : ℕ}
def rowOp (a : Fin N → K) (r : Fin N) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun i m => if m = r then a i else 0
def colOp (k : Fin N) (b : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun m c => if m = k then b c else 0
def Cleared (h : Matrix (Fin N) (Fin N) K) (k : ℕ) (p : Fin N → Fin N) : Prop :=
  ∀ j : Fin N, (j : ℕ) < k →
    h (p j) j ≠ 0 ∧ (∀ i, i ≠ p j → h i j = 0) ∧ (∀ c, c ≠ j → h (p j) c = 0)
end Bruhat
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Matrix
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section Transfer
variable {G : Type} [Group G]
def GTAlt (σ : G → G) (J : Subgroup G) (χ : J →* ℂˣ) (g : G) : Prop :=
  (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
    (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)
end Transfer
section Flip
variable {K : Type} [Field K] {N : ℕ}
def flipM (A : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => A (Fin.rev j) (Fin.rev i)
theorem flipM_apply (A : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    flipM A i j = A (Fin.rev j) (Fin.rev i) := rfl
theorem flipM_mul (A B : Matrix (Fin N) (Fin N) K) : flipM (A * B) = flipM B * flipM A := by
  ext i j
  simp only [flipM_apply, Matrix.mul_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun m => ?_)
  simp [mul_comm]
theorem flipM_one : flipM (1 : Matrix (Fin N) (Fin N) K) = 1 := by
  ext i j
  rw [flipM_apply, Matrix.one_apply, Matrix.one_apply]
  simp only [Fin.rev_inj]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
def flipG (g : GL (Fin N) K) : GL (Fin N) K :=
  ⟨flipM g.1, flipM (g⁻¹).1, by
    rw [← flipM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, flipM_one], by
    rw [← flipM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, flipM_one]⟩
end Flip
section Elem
variable {K : Type} [Field K] {N : ℕ}
def elM (p q : Fin N) (v : K) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun x c => if x = p ∧ c = q then v else 0
end Elem
section Mono
variable {K : Type} [Field K] {N : ℕ}
def MonoAdm (π : Equiv.Perm (Fin N)) (t : Fin N → K) : Prop :=
  ∀ i j : Fin N, (j : ℕ) = i + 1 → π i < π j → (π j : ℕ) = π i + 1 ∧ t i = t j
end Mono
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end


