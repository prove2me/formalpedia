-- Prove2me | solution 1 for AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4600a65a-5ef9-5ca6-b74d-9a98738980fa

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_AdelicLevel
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped Classical

noncomputable section

namespace RS24

variable (K : Type) [Field K] [NumberField K]

theorem exists_le_exp_nat (x : WithZero (Multiplicative ℤ)) : ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · obtain ⟨u, rfl⟩ : ∃ u : Multiplicative ℤ, (u : WithZero (Multiplicative ℤ)) = x :=
      ⟨_, WithZero.coe_unzero hx⟩
    refine ⟨(Multiplicative.toAdd u).toNat, ?_⟩
    show (u : WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd ((Multiplicative.toAdd u).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    conv_lhs => rw [← ofAdd_toAdd u]
    rw [Multiplicative.ofAdd_le]
    exact Int.self_le_toNat _

def ordAt (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk N).factors

theorem idealBound_eq_exp_neg_ordAt {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    idealBound (𝓞 K) N v = WithZero.exp (-(ordAt K N v : ℤ)) :=
  idealBound_of_ne_bot hN v

theorem exists_forall_mul_mem_idealBall {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : FiniteAdeleRing (𝓞 K) K) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ c : FiniteAdeleRing (𝓞 K) K,
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → c w = 0) →
      (∀ v ∈ S, Valued.v (c v) ≤ WithZero.exp (-(n : ℤ))) →
      c * b ∈ idealBall (𝓞 K) K N := by
  choose k hk using fun v : HeightOneSpectrum (𝓞 K) => exists_le_exp_nat (Valued.v (b v))
  refine ⟨∑ v ∈ S, (k v + ordAt K N v), fun n hn c hc0 hcS w => ?_⟩
  rw [coe_mul_apply, map_mul]
  by_cases hw : w ∈ S
  · have hkle : k w + ordAt K N w ≤ n :=
      (Finset.single_le_sum (f := fun v => k v + ordAt K N v) (fun _ _ => Nat.zero_le _) hw).trans hn
    calc Valued.v (c w) * Valued.v (b w)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' (hcS w hw) (hk w)
      _ = WithZero.exp (-(n : ℤ) + k w) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(ordAt K N w : ℤ)) := by
          rw [WithZero.exp_le_exp]; omega
      _ = idealBound (𝓞 K) N w := (idealBound_eq_exp_neg_ordAt K hN w).symm
  · rw [hc0 w hw, map_zero, zero_mul]
    exact zero_le'

def E21 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) := !![0, 0; 1, 0]

theorem lowerUnipotentGL2_val_eq (γ : AdeleRing (𝓞 K) K) :
    ((lowerUnipotentGL2 γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + γ • E21 K := by
  rw [lowerUnipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E21]

theorem lowerUnipotentGL2_inv (γ : AdeleRing (𝓞 K) K) :
    (lowerUnipotentGL2 γ : GL (Fin 2) (AdeleRing (𝓞 K) K))⁻¹ = lowerUnipotentGL2 (-γ) := by
  rw [inv_eq_iff_mul_eq_one, ← lowerUnipotentGL2_add, add_neg_cancel, lowerUnipotentGL2_zero]

def Bmat (A : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  ((A⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * E21 K *
    (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))

theorem conj_lowerUnipotentGL2_val (A : GL (Fin 2) (AdeleRing (𝓞 K) K)) (γ : AdeleRing (𝓞 K) K) :
    ((A⁻¹ * lowerUnipotentGL2 γ * A : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + γ • Bmat K A := by
  rw [Units.val_mul, Units.val_mul, lowerUnipotentGL2_val_eq, Bmat, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_lowerUnipotentGL2_inv_val (A : GL (Fin 2) (AdeleRing (𝓞 K) K)) (γ : AdeleRing (𝓞 K) K) :
    (((A⁻¹ * lowerUnipotentGL2 γ * A)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + (-γ) • Bmat K A := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, lowerUnipotentGL2_inv, conj_lowerUnipotentGL2_val]

theorem glFin_apply_of_val_eq_one_add_smul (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) (γ : AdeleRing (𝓞 K) K)
    (B : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    (hg : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1 + γ • B) (p q : Fin 2) :
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p q =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p q + γ.2 * (B p q).2 := by
  rw [glFin_apply, hg, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem glArch_lowerUnipotentGL2_eq_one (γ : AdeleRing (𝓞 K) K) (hγ : γ.1 = 0) :
    glArch (𝓞 K) K (lowerUnipotentGL2 γ) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, lowerUnipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hγ] | simp [hγ, Prod.fst_one, Prod.fst_zero]

theorem isLevelOneMatrix_of_entries {N : Ideal (𝓞 K)}
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (c : FiniteAdeleRing (𝓞 K) K)
    (b : Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 K) K)
    (hm : ∀ p q, m p q = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p q + c * b p q)
    (hb : ∀ p q, c * b p q ∈ idealBall (𝓞 K) K N) :
    IsLevelOneMatrix (𝓞 K) K N m where
  integral p q := by
    rw [hm]
    refine add_mem_integralFiniteAdeles ?_ (idealBall_subset_integralFiniteAdeles N (hb p q))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [hm, Matrix.one_apply_ne (by decide), zero_add]
    exact hb 1 0
  lowerRight := by
    rw [hm, Matrix.one_apply_eq, add_sub_cancel_left]
    exact hb 1 1

theorem exists_depth_conj_lowerUnipotentGL2_mem_levelOne
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {r : ℕ} (A : Fin r → AdelicGL2 (𝓞 K) K) :
    ∃ nS : ℕ, 0 < nS ∧ ∀ γ : AdeleRing (𝓞 K) K, γ.1 = 0 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → γ.2 w = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤ WithZero.exp (-(nS : ℤ))) →
      ∀ i, (A i)⁻¹ * lowerUnipotentGL2 γ * A i ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by

  choose n₀ hn₀ using fun s : Fin r × Fin 2 × Fin 2 × Bool =>
    exists_forall_mul_mem_idealBall K hN S
      (if s.2.2.2 then ((Bmat K (A s.1)) s.2.1 s.2.2.1).2 else (-(Bmat K (A s.1)) s.2.1 s.2.2.1).2)
  refine ⟨1 + ∑ s, n₀ s, by omega, fun γ hγ1 hγ0 hγS i => ?_⟩
  have hle : ∀ s, n₀ s ≤ 1 + ∑ s, n₀ s := fun s => by
    have := Finset.single_le_sum (f := n₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    omega
  have key : ∀ (p q : Fin 2) (sgn : Bool),
      γ.2 * (if sgn then ((Bmat K (A i)) p q).2 else (-(Bmat K (A i)) p q).2) ∈ idealBall (𝓞 K) K N :=
    fun p q sgn => hn₀ (i, p, q, sgn) _ (hle _) γ.2 hγ0 hγS
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    constructor
    · refine isLevelOneMatrix_of_entries K _ γ.2 (fun p q => ((Bmat K (A i)) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ γ _ (conj_lowerUnipotentGL2_val K (A i) γ)) fun p q => ?_
      simpa using key p q true
    · rw [← map_inv]
      refine isLevelOneMatrix_of_entries K _ (-γ).2 (fun p q => ((Bmat K (A i)) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ (-γ) _ (conj_lowerUnipotentGL2_inv_val K (A i) γ)) fun p q => ?_
      have h := key p q false
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have e : (-γ).2 * ((Bmat K (A i)) p q).2 = γ.2 * ((-(Bmat K (A i))) p q).2 := by
        show -γ.2 * (Bmat K (A i) p q).2 = γ.2 * -((Bmat K (A i) p q).2)
        ring
      rw [e]
      exact h
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_lowerUnipotentGL2_eq_one K γ hγ1,
      mul_one, inv_mul_cancel]

theorem translateFamily_apply_mul_lowerUnipotentGL2
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    {r : ℕ} (A : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * A i))
    (γ : AdeleRing (𝓞 K) K)
    (hγ : ∀ i, (A i)⁻¹ * lowerUnipotentGL2 γ * A i ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (g : AdelicGL2 (𝓞 K) K) :
    x (g * lowerUnipotentGL2 γ) = x g := by
  rw [hxsum, hxsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h := hx₀lev (g * A i) _ (hγ i)
  rw [show g * A i * ((A i)⁻¹ * lowerUnipotentGL2 γ * A i) = g * lowerUnipotentGL2 γ * A i from by group] at h
  exact h

section LCover

def E11 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) := !![1, 0; 0, 0]

theorem diagOne_val_eq (s : (AdeleRing (𝓞 K) K)ˣ) :
    ((diagOne s : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + ((s : AdeleRing (𝓞 K) K) - 1) • E11 K := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [E11]

def Cmat (κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  ((κ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * E11 K *
    (κ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))

theorem conj_diagOne_val (κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (s : (AdeleRing (𝓞 K) K)ˣ) :
    ((κ⁻¹ * diagOne s * κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + ((s : AdeleRing (𝓞 K) K) - 1) • Cmat K κ := by
  rw [Units.val_mul, Units.val_mul, diagOne_val_eq, Cmat, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_diagOne_inv (κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (s : (AdeleRing (𝓞 K) K)ˣ) :
    (κ⁻¹ * diagOne s * κ : GL (Fin 2) (AdeleRing (𝓞 K) K))⁻¹ = κ⁻¹ * diagOne s⁻¹ * κ := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, map_inv]

theorem glArch_diagOne_eq_one (s : (AdeleRing (𝓞 K) K)ˣ) (hs : ((s : AdeleRing (𝓞 K) K)).1 = 1) :
    glArch (𝓞 K) K (diagOne s) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hs] | simp [hs, Prod.fst_one, Prod.fst_zero]

theorem units_inv_snd_apply (s : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w = (((s : AdeleRing (𝓞 K) K)).2 w)⁻¹ := by
  have h : ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w * ((s : AdeleRing (𝓞 K) K)).2 w = 1 := by
    have := congrArg (fun x : AdeleRing (𝓞 K) K => x.2 w) s.inv_mul
    exact this
  exact eq_inv_of_mul_eq_one_left h

theorem units_inv_fst (s : (AdeleRing (𝓞 K) K)ˣ) (hs : ((s : AdeleRing (𝓞 K) K)).1 = 1) :
    ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).1 = 1 := by
  have h : ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).1 * ((s : AdeleRing (𝓞 K) K)).1 = 1 :=
    congrArg Prod.fst s.inv_mul
  rwa [hs, mul_one] at h

theorem valued_inv_sub_one {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (hx : Valued.v x = 1) :
    Valued.v (x⁻¹ - 1) = Valued.v (x - 1) := by
  have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have : x⁻¹ - 1 = x⁻¹ * (1 - x) := by field_simp
  rw [this, map_mul, map_inv₀, hx, inv_one, one_mul, Valuation.map_sub_swap]

theorem exists_threshold_conj_diagOne_mem_levelOne
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (κ : AdelicGL2 (𝓞 K) K) :
    ∃ n₁ : ℕ, 0 < n₁ ∧ ∀ s : (AdeleRing (𝓞 K) K)ˣ, ((s : AdeleRing (𝓞 K) K)).1 = 1 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((s : AdeleRing (𝓞 K) K)).2 w = 1) →
      (∀ v ∈ S, Valued.v (((s : AdeleRing (𝓞 K) K)).2 v) = 1) →
      (∀ v ∈ S, Valued.v (((s : AdeleRing (𝓞 K) K)).2 v - 1) ≤ WithZero.exp (-(n₁ : ℤ))) →
      κ⁻¹ * diagOne s * κ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  choose n₀ hn₀ using fun s : Fin 2 × Fin 2 => exists_forall_mul_mem_idealBall K hN S ((Cmat K κ) s.1 s.2).2
  refine ⟨1 + ∑ s, n₀ s, by omega, fun s hs1 hsS hsv hclose => ?_⟩
  have hle : ∀ pq, n₀ pq ≤ 1 + ∑ s, n₀ s := fun pq => by
    have := Finset.single_le_sum (f := n₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ pq)
    omega

  have hc0 : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (((s : AdeleRing (𝓞 K) K)) - 1).2 w = 0 := fun w hw => by
    show ((s : AdeleRing (𝓞 K) K)).2 w - 1 = 0
    rw [hsS w hw, sub_self]
  have hcS : ∀ v ∈ S, Valued.v ((((s : AdeleRing (𝓞 K) K)) - 1).2 v) ≤ WithZero.exp (-((1 + ∑ s, n₀ s : ℕ) : ℤ)) :=
    fun v hv => hclose v hv
  have hc0' : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (((↑(s⁻¹) : AdeleRing (𝓞 K) K)) - 1).2 w = 0 := fun w hw => by
    show ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w - 1 = 0
    rw [units_inv_snd_apply, hsS w hw, inv_one, sub_self]
  have hcS' : ∀ v ∈ S, Valued.v ((((↑(s⁻¹) : AdeleRing (𝓞 K) K)) - 1).2 v) ≤
      WithZero.exp (-((1 + ∑ s, n₀ s : ℕ) : ℤ)) := fun v hv => by
    show Valued.v (((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 v - 1) ≤ _
    rw [units_inv_snd_apply, valued_inv_sub_one K _ (hsv v hv)]
    exact hclose v hv
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    constructor
    · exact isLevelOneMatrix_of_entries K _ _ (fun p q => ((Cmat K κ) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ _ _ (conj_diagOne_val K κ s))
        fun p q => hn₀ (p, q) _ (hle _) _ hc0 hcS
    · rw [← map_inv, conj_diagOne_inv]
      exact isLevelOneMatrix_of_entries K _ _ (fun p q => ((Cmat K κ) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ _ _ (conj_diagOne_val K κ s⁻¹))
        fun p q => hn₀ (p, q) _ (hle _) _ hc0' hcS'
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_diagOne_eq_one K s hs1, mul_one,
      inv_mul_cancel]

end LCover

section LCoverFinite

theorem exists_finset_sphere_mulCover (v : HeightOneSpectrum (𝓞 K)) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    ∃ Z : Finset (v.adicCompletion K), (∀ z ∈ Z, Valued.v z = WithZero.exp a) ∧
      ∀ u : v.adicCompletion K, Valued.v u = WithZero.exp a →
        ∃ z ∈ Z, Valued.v (z⁻¹ * u - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  by_cases hne : ∃ u₀ : v.adicCompletion K, Valued.v u₀ = WithZero.exp a
  swap
  · refine ⟨∅, by simp, fun u hu => (hne ⟨u, hu⟩).elim⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀0 : u₀ ≠ 0 := fun h => by rw [h, map_zero] at hu₀; exact WithZero.exp_ne_zero hu₀.symm

  obtain ⟨tn, htn0, htn⟩ := exists_valued_eq_exp_neg (K := K) v n

  haveI : CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr inferInstance

  let B : v.adicCompletion K → Set (v.adicCompletion K) := fun z => {u | Valued.v (u - z) ≤ Valued.v tn}
  have hBopen : ∀ z, IsOpen (B z) := fun z =>
    (isOpen_setOf_valued_le v tn htn0).preimage (continuous_id.sub continuous_const)
  have hcover : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ⊆ ⋃ z, B z := fun u _ =>
    Set.mem_iUnion.mpr ⟨u, by show Valued.v (u - u) ≤ _; rw [sub_self, map_zero]; exact zero_le'⟩
  obtain ⟨T, hT⟩ := hO.elim_finite_subcover B hBopen hcover
  refine ⟨(T.filter fun z => Valued.v z = 1).image (fun z => u₀ * z), ?_, ?_⟩
  · intro z hz
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hz
    rw [map_mul, hu₀, (Finset.mem_filter.mp hz₁).2, mul_one]
  · intro u hu

    have hu' : Valued.v (u₀⁻¹ * u) = 1 := by
      rw [map_mul, map_inv₀, hu₀, hu, inv_mul_cancel₀ WithZero.exp_ne_zero]
    have hu'O : u₀⁻¹ * u ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, hu']
    obtain ⟨z, hzT, hz⟩ : ∃ z ∈ T, u₀⁻¹ * u ∈ B z := by
      simpa only [Set.mem_iUnion, exists_prop] using hT hu'O
    have hzclose : Valued.v (u₀⁻¹ * u - z) ≤ WithZero.exp (-(n : ℤ)) := by rw [← htn]; exact hz

    have hlt : Valued.v (z - u₀⁻¹ * u) < Valued.v (u₀⁻¹ * u) := by
      rw [Valuation.map_sub_swap, hu']
      refine lt_of_le_of_lt hzclose ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hz1 : Valued.v z = 1 := by
      rw [← hu']
      exact Valuation.map_eq_of_sub_lt Valued.v hlt
    have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
    refine ⟨u₀ * z, Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzT, hz1⟩, rfl⟩, ?_⟩
    have e : (u₀ * z)⁻¹ * u - 1 = z⁻¹ * (u₀⁻¹ * u - z) := by field_simp
    rw [e, map_mul, map_inv₀, hz1, inv_one, one_mul]
    exact hzclose

end LCoverFinite

section LCoverMain

variable {K}

def unitOf {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) : (v.adicCompletion K)ˣ :=
  if h : x = 0 then 1 else Units.mk0 x h

theorem unitOf_coe {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (hx : x ≠ 0) :
    (unitOf x : v.adicCompletion K) = x := by
  simp [unitOf, hx]

variable (K)

def shellIdele (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    (AdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ S, Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (unitOf (z v)))

theorem finAdele_prod_apply {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) : (∏ i ∈ s, f i) w = ∏ i ∈ s, f i w :=
  map_prod (finAdeleEval (𝓞 K) K w) f s

theorem shellIdele_fst (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    ((shellIdele K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  rw [shellIdele, Units.coe_prod]
  change adeleArch (𝓞 K) K (∏ i ∈ S, ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K i (unitOf (z i))) :
    (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = 1
  rw [map_prod]
  exact Finset.prod_eq_one fun v _ => rfl

theorem shellIdele_snd_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (w : HeightOneSpectrum (𝓞 K)) :
    ((shellIdele K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w =
      if w ∈ S then ((unitOf (z w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
  rw [shellIdele, Units.coe_prod]
  change ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K))
    (∏ i ∈ S, ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K i (unitOf (z i))) :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = _
  rw [map_prod]
  have h : ∀ v ∈ S, ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K))
      (((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (unitOf (z v))) :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        if v = w then ((unitOf (z w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
    intro v _
    show ((localUnit (𝓞 K) K v (unitOf (z v)) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = _
    by_cases hvw : v = w
    · subst hvw
      rw [if_pos rfl]
      exact localUnit_apply_self _ _ _ _
    · rw [if_neg hvw]
      exact localUnit_apply_of_ne _ _ _ _ (Ne.symm hvw)
  rw [Finset.prod_congr rfl h, Finset.prod_ite_eq']

theorem exists_finset_diagOne_mul_mem_mul_levelOne
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (κ : AdelicGL2 (𝓞 K) K)
    (a : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ G : Finset (AdelicGL2 (𝓞 K) K), (∀ g ∈ G, glArch (𝓞 K) K g = glArch (𝓞 K) K κ) ∧
      ∀ t : (AdeleRing (𝓞 K) K)ˣ,
      ((t : AdeleRing (𝓞 K) K)).1 = 1 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((t : AdeleRing (𝓞 K) K)).2 w = 1) →
      (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = WithZero.exp (a v)) →
      ∃ g ∈ G, g⁻¹ * (diagOne t * κ) ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  obtain ⟨n₁, hn₁, hcrit⟩ := exists_threshold_conj_diagOne_mem_levelOne K N hN S κ
  choose Z hZval hZcov using fun v : HeightOneSpectrum (𝓞 K) => exists_finset_sphere_mulCover K v (a v) n₁ hn₁
  refine ⟨(S.pi Z).image fun f =>
    diagOne (shellIdele K S (fun v => if h : v ∈ S then f v h else 0)) * κ, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hg
    rw [map_mul, glArch_diagOne_eq_one K _ (shellIdele_fst K S _), one_mul]
  intro t ht1 htS htv
  choose z hzZ hzclose using fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) =>
    hZcov v (((t : AdeleRing (𝓞 K) K)).2 v) (htv v hv)
  have hzpi : z ∈ S.pi Z := Finset.mem_pi.mpr fun v hv => hzZ v hv
  set t₀ : (AdeleRing (𝓞 K) K)ˣ := shellIdele K S (fun v => if h : v ∈ S then z v h else 0) with ht₀
  refine ⟨diagOne t₀ * κ, Finset.mem_image.mpr ⟨z, hzpi, rfl⟩, ?_⟩
  have hrw : (diagOne t₀ * κ)⁻¹ * (diagOne t * κ) = κ⁻¹ * diagOne (t₀⁻¹ * t) * κ := by
    rw [map_mul, map_inv]; group
  rw [hrw]

  have hz0 : ∀ v (hv : v ∈ S), z v hv ≠ 0 := fun v hv h => by
    have h1 := hZval v _ (hzZ v hv)
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  have ht₀1 : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1 := shellIdele_fst K S _
  have ht₀S : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 w = 1 := fun w hw => by
    rw [ht₀, shellIdele_snd_apply, if_neg hw]
  have ht₀v : ∀ v (hv : v ∈ S), ((t₀ : AdeleRing (𝓞 K) K)).2 v = z v hv := fun v hv => by
    rw [ht₀, shellIdele_snd_apply, if_pos hv, dif_pos hv, unitOf_coe _ (hz0 v hv)]
  apply hcrit
  · show ((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).1 * ((t : AdeleRing (𝓞 K) K)).1 = 1
    rw [units_inv_fst K t₀ ht₀1, ht1, one_mul]
  · intro w hw
    show ((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).2 w * ((t : AdeleRing (𝓞 K) K)).2 w = 1
    rw [units_inv_snd_apply, ht₀S w hw, htS w hw, inv_one, one_mul]
  · intro v hv
    show Valued.v (((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).2 v * ((t : AdeleRing (𝓞 K) K)).2 v) = 1
    rw [map_mul, units_inv_snd_apply, map_inv₀, ht₀v v hv, hZval v _ (hzZ v hv), htv v hv,
      inv_mul_cancel₀ WithZero.exp_ne_zero]
  · intro v hv
    show Valued.v (((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).2 v * ((t : AdeleRing (𝓞 K) K)).2 v - 1) ≤ _
    rw [units_inv_snd_apply, ht₀v v hv]
    exact hzclose v hv

end LCoverMain

end RS24

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    (r : ℕ) (A : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * A i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      x (g * lowerUnipotentGL2 γ) = x g := by
  obtain ⟨n, hn, hconj⟩ := RS24.exists_depth_conj_lowerUnipotentGL2_mem_levelOne K N _hN S A
  refine ⟨n, hn, fun γ g h1 h2 h3 => ?_⟩
  exact RS24.translateFamily_apply_mul_lowerUnipotentGL2 K N S x₀ _hx₀lev A cs x _hxsum γ
    (hconj γ h1 h2 h3) g

end S_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
end P2MW
export P2MW.S_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate (solution)
