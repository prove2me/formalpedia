-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
-- name    : GroundTheory_PAdicHodge_FieldOfNormsField
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:16.395617+00:00
-- url     : https://prove2.me/theorems/17249e90-db6b-5608-8113-fe715f06d200
-- title:
--   Field Of Norms Field
-- statement:
--   Definitions and structural lemmas for Field Of Norms Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsField.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_D_pos
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_IsFam_nrm_eq
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_inv
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mem
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mul
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_pow
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_isFam
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_nrm
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
namespace NormTower
variable (t : NormTower K Ω p)
theorem exists_intFam_mem {C : ℕ → Set Ω} (hcl : ∀ n, IsClosed (C n))
    (hne : ∀ n, (t.intSet n ∩ C n).Nonempty)
    (hN : ∀ n, ∀ y ∈ t.intSet (n + 1) ∩ C (n + 1), t.N n y ∈ C n) :
    ∃ z, t.IsIntFam z ∧ ∀ n, z n ∈ C n := by
  have hNint : ∀ n, ∀ y ∈ t.intSet (n + 1), t.N n y ∈ t.intSet n :=
    fun n y hy ↦ ⟨t.N_mem n hy.1, t.nrm_N_le_one n hy.2⟩

  have hNto : ∀ i j, ∀ y ∈ t.intSet (i + j) ∩ C (i + j), t.Nto i j y ∈ t.intSet i ∩ C i := by
    intro i j
    induction j with
    | zero => exact fun y hy ↦ hy
    | succ j ih =>
      intro y hy
      rw [Nto_succ]
      exact ih _ ⟨hNint _ _ hy.1, hN _ _ hy⟩
  let S : ℕ → Set (ℕ → Ω) := fun m ↦
    {z | (∀ n < m, nrm K (t.N n (z (n + 1)) - z n) ≤ 0) ∧ ∀ n ≤ m, z n ∈ C n}
  have hP : IsCompact {z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} :=
    isCompact_pi_infinite t.isCompact_intSet
  have hcont : ∀ n, Continuous fun z : ℕ → Ω ↦ nrm K (t.N n (z (n + 1)) - z n) := fun n ↦
    (continuous_nrm K Ω).comp (((t.continuous_N n).comp (continuous_apply _)).sub
      (continuous_apply _))
  have hcl' : ∀ m, IsClosed (S m) := by
    intro m
    have e : S m = (⋂ n ∈ {n | n < m}, {z : ℕ → Ω | nrm K (t.N n (z (n + 1)) - z n) ≤ 0}) ∩
        ⋂ n ∈ {n | n ≤ m}, (fun z : ℕ → Ω ↦ z n) ⁻¹' C n := by
      ext z; simp [S]
    rw [e]
    exact (isClosed_biInter fun n _ ↦ isClosed_le (hcont n) continuous_const).inter
      (isClosed_biInter fun n _ ↦ (hcl n).preimage (continuous_apply n))
  have hanti : ∀ {m m'}, m ≤ m' → S m' ⊆ S m := fun hmm' z hz ↦
    ⟨fun n hn ↦ hz.1 n (by omega), fun n hn ↦ hz.2 n (by omega)⟩
  have hne' : ∀ m, ({z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} ∩ S m).Nonempty := by
    intro m
    obtain ⟨y, hy⟩ := hne m
    refine ⟨fun n ↦ if n ≤ m then t.Nto n (m - n) y else 0, ?_, ?_, ?_⟩
    · intro n
      dsimp only
      split_ifs with h
      · have hy' : y ∈ t.intSet (n + (m - n)) ∩ C (n + (m - n)) := by
          rw [Nat.add_sub_cancel' h]; exact hy
        exact (hNto n _ y hy').1
      · exact ⟨zero_mem _, by simp⟩
    · intro n hn
      simp only [if_pos hn.le, if_pos (show n + 1 ≤ m by omega)]
      rw [← Nto_succ', show m - n = m - (n + 1) + 1 by omega]
      simp
    · intro n hn
      simp only [if_pos hn]
      have hy' : y ∈ t.intSet (n + (m - n)) ∩ C (n + (m - n)) := by
        rw [Nat.add_sub_cancel' hn]; exact hy
      exact (hNto n _ y hy').2
  obtain ⟨z, hzP, hz⟩ := hP.inter_iInter_nonempty S hcl' fun u ↦ by
    obtain ⟨z, hzP, hzS⟩ := hne' (u.sup id)
    refine ⟨z, hzP, Set.mem_iInter₂.mpr fun m hm ↦ hanti (Finset.le_sup (f := id) hm) hzS⟩
  rw [Set.mem_iInter] at hz
  refine ⟨z, ⟨fun n ↦ ⟨(hzP n).1, ?_⟩, fun n ↦ (hzP n).2⟩, fun n ↦ (hz n).2 n le_rfl⟩
  have := (hz (n + 1)).1 n (Nat.lt_succ_self n)
  rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
  exact le_antisymm this (nrm_nonneg _)
namespace Plus
variable {t}
theorem nrm_val_zero (x : t.Plus) (n : ℕ) : nrm K (x.1 0) = nrm K (x.1 n) ^ t.D 0 n := by
  have := x.isFam.nrm_eq 0 n
  rwa [zero_add] at this
theorem val_eq_zero_iff (x : t.Plus) (n : ℕ) : x.1 n = 0 ↔ x.1 0 = 0 := by
  rw [← nrm_eq_zero (K := K), ← nrm_eq_zero (K := K) (x := x.1 0), nrm_val_zero x n,
    pow_eq_zero_iff (t.D_pos 0 n).ne']
theorem eq_zero_iff (x : t.Plus) : x = 0 ↔ x.1 0 = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h
    exact Subtype.ext (funext fun n ↦ (val_eq_zero_iff x n).mpr h)
instance instNontrivial : Nontrivial t.Plus :=
  ⟨⟨0, 1, fun h ↦ by simpa using congrArg (fun x : t.Plus ↦ x.1 0) h⟩⟩
instance instNoZeroDivisors : NoZeroDivisors t.Plus where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    rw [eq_zero_iff] at h
    simp only [mul_val, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl ((eq_zero_iff x).mpr h)
    · exact Or.inr ((eq_zero_iff y).mpr h)
instance instIsDomain : IsDomain t.Plus :=
  NoZeroDivisors.to_isDomain _
variable (t) in

theorem exists_unif : ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n) = t.value n := by
  refine t.exists_intFam_mem (C := fun n ↦ {y | nrm K y = t.value n})
    (fun n ↦ isClosed_eq (continuous_nrm K Ω) continuous_const) (fun n ↦ ?_) (fun n y hy ↦ ?_)
  · obtain ⟨π, hπ, hπv⟩ := t.exists_value n
    exact ⟨π, ⟨hπ, hπv ▸ (t.value_lt_one n).le⟩, hπv⟩
  · simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [t.nrm_N, hy.2, t.value_succ]
variable (t) in

def unif : t.Plus :=
  ⟨(exists_unif t).choose, (exists_unif t).choose_spec.1⟩
theorem nrm_unif (n : ℕ) : nrm K ((unif t).1 n) = t.value n :=
  (exists_unif t).choose_spec.2 n
theorem unif_ne_zero : unif t ≠ 0 := by
  rw [Ne, eq_zero_iff, ← nrm_eq_zero (K := K), nrm_unif]
  exact (t.value_pos 0).ne'
theorem unif_val_ne_zero (n : ℕ) : (unif t).1 n ≠ 0 := by
  rw [← nrm_pos (K := K), nrm_unif]; exact t.value_pos n
theorem val_ne_zero {x : t.Plus} (hx : x ≠ 0) (n : ℕ) : x.1 n ≠ 0 := by
  rw [Ne, val_eq_zero_iff, ← eq_zero_iff]; exact hx
theorem pow_val (x : t.Plus) (k n : ℕ) : (x ^ k).1 n = x.1 n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_val, ih, pow_succ]
end Plus
section Fam
def Fam : Type _ :=
  {z : ℕ → Ω // t.IsFam z}
namespace Plus
variable {t}
def toFam (x : t.Plus) : t.Fam := ⟨x.1, x.2.1⟩
@[simp] theorem toFam_val (x : t.Plus) : x.toFam.1 = x.1 := rfl
end Plus
namespace Fam
variable {t}
theorem mem (x : t.Fam) (n : ℕ) : x.1 n ∈ t.E n := (x.2 n).1
theorem N_eq (x : t.Fam) (n : ℕ) : t.N n (x.1 (n + 1)) = x.1 n := (x.2 n).2
theorem nrm_val_zero (x : t.Fam) (n : ℕ) : nrm K (x.1 0) = nrm K (x.1 n) ^ t.D 0 n := by
  have := x.2.nrm_eq 0 n
  rwa [zero_add] at this
theorem isIntFam_of_nrm_le {x : t.Fam} (h : nrm K (x.1 0) ≤ 1) : t.IsIntFam x.1 := by
  refine ⟨x.2, fun n ↦ ?_⟩
  rw [nrm_val_zero x n] at h
  exact (pow_le_one_iff_of_nonneg (nrm_nonneg _) (t.D_pos 0 n).ne').mp h
def scale (x : t.Fam) (m : ℕ) : t.Fam :=
  ⟨fun n ↦ (Plus.unif t).1 n ^ m * x.1 n, fun n ↦ ⟨mul_mem (pow_mem ((Plus.unif t).mem n) m) (x.mem n),
    by rw [t.N_mul, t.N_pow, (Plus.unif t).N_eq, x.N_eq]⟩⟩
theorem nrm_scale_val_zero (x : t.Fam) (m : ℕ) :
    nrm K ((x.scale m).1 0) = t.value 0 ^ m * nrm K (x.1 0) := by
  show nrm K ((Plus.unif t).1 0 ^ m * x.1 0) = _
  rw [nrm_mul, nrm_pow, Plus.nrm_unif]
theorem exists_scale (x : t.Fam) : ∃ m, t.value 0 ^ m * nrm K (x.1 0) ≤ 1 := by
  rcases eq_or_lt_of_le (nrm_nonneg (K := K) (x.1 0)) with h | h
  · exact ⟨0, by rw [← h]; simp⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr h) (t.value_lt_one 0)
  refine ⟨m, ?_⟩
  rw [← le_div_iff₀ h, one_div]
  exact hm.le
def scalePlus (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) : t.Plus :=
  ⟨(x.scale m).1, isIntFam_of_nrm_le (by rwa [nrm_scale_val_zero])⟩
theorem unif_pow_mem (m : ℕ) : Plus.unif t ^ m ∈ nonZeroDivisors t.Plus :=
  pow_mem (mem_nonZeroDivisors_of_ne_zero Plus.unif_ne_zero) m
def toFrac (x : t.Fam) : FractionRing t.Plus :=
  IsLocalization.mk' _ (scalePlus x (Nat.find (exists_scale x)) (Nat.find_spec (exists_scale x)))
    ⟨Plus.unif t ^ Nat.find (exists_scale x), unif_pow_mem _⟩
theorem injective_algebraMap :
    Function.Injective (algebraMap t.Plus (FractionRing t.Plus)) :=
  IsFractionRing.injective t.Plus (FractionRing t.Plus)
def ofDiv (a : t.Plus) (b : nonZeroDivisors t.Plus) : t.Fam :=
  ⟨fun n ↦ a.1 n / b.1.1 n, fun n ↦ ⟨div_mem (a.mem n) (b.1.mem n), by
    show t.N n (a.1 (n + 1) / b.1.1 (n + 1)) = a.1 n / b.1.1 n
    rw [div_eq_mul_inv, t.N_mul, t.N_inv, a.N_eq, b.1.N_eq, div_eq_mul_inv]⟩⟩
theorem ofDiv_val (a : t.Plus) (b : nonZeroDivisors t.Plus) (n : ℕ) :
    (ofDiv a b).1 n = a.1 n / b.1.1 n := rfl
theorem val_ne_zero_of_mem {b : t.Plus} (hb : b ∈ nonZeroDivisors t.Plus) (n : ℕ) : b.1 n ≠ 0 :=
  Plus.val_ne_zero (nonZeroDivisors.ne_zero hb) n
theorem ofDiv_eq_ofDiv {a a' : t.Plus} {b b' : nonZeroDivisors t.Plus}
    (h : IsLocalization.mk' (FractionRing t.Plus) a b = IsLocalization.mk' _ a' b') :
    ofDiv a b = ofDiv a' b' := by
  rw [IsLocalization.mk'_eq_iff_eq] at h
  have h' := congrArg (fun z : t.Plus ↦ z.1) (injective_algebraMap h)
  refine Subtype.ext (funext fun n ↦ ?_)
  have hn := congrFun h' n
  simp only [Plus.mul_val] at hn
  simp only [ofDiv_val]
  rw [div_eq_div_iff (val_ne_zero_of_mem b.2 n) (val_ne_zero_of_mem b'.2 n)]
  linear_combination hn
def ofFrac (q : FractionRing t.Plus) : t.Fam :=
  ofDiv (IsLocalization.mk'_surjective (nonZeroDivisors t.Plus) q).choose.1
    (IsLocalization.mk'_surjective (nonZeroDivisors t.Plus) q).choose.2
theorem ofFrac_mk' (a : t.Plus) (b : nonZeroDivisors t.Plus) :
    ofFrac (IsLocalization.mk' (FractionRing t.Plus) a b) = ofDiv a b :=
  ofDiv_eq_ofDiv (IsLocalization.mk'_surjective (nonZeroDivisors t.Plus)
    (IsLocalization.mk' (FractionRing t.Plus) a b)).choose_spec
variable (t) in

def equivFrac : t.Fam ≃ FractionRing t.Plus where
  toFun := toFrac
  invFun := ofFrac
  left_inv x := by
    rw [toFrac, ofFrac_mk']
    refine Subtype.ext (funext fun n ↦ ?_)
    change (Plus.unif t).1 n ^ _ * x.1 n / (Plus.unif t ^ _).1 n = x.1 n
    have := Plus.unif_val_ne_zero (t := t) n
    rw [Plus.pow_val]
    field_simp
    ring
  right_inv q := by
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors t.Plus) q
    rw [ofFrac_mk', toFrac, IsLocalization.mk'_eq_iff_eq]
    congr 1
    refine Subtype.ext (funext fun n ↦ ?_)
    change b.1.1 n * ((Plus.unif t).1 n ^ _ * (a.1 n / b.1.1 n)) = (Plus.unif t ^ _).1 n * a.1 n
    have := val_ne_zero_of_mem b.2 n
    rw [Plus.pow_val]
    field_simp
    ring
instance instField : Field t.Fam :=
  (equivFrac t).field
end Fam
end Fam
end NormTower
end GroundTheory.PAdicHodge


