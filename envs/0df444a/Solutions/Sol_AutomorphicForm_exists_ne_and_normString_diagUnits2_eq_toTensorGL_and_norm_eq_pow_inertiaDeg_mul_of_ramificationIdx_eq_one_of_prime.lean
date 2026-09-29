-- Prove2me | solution 1 for AutomorphicForm.exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8c9033c5-8dbf-5f57-9533-a737020f2ceb

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions

namespace P2mArchSplitBrick

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem card_aut_dvd_finrank : Fintype.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
  have h1 : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L =
      Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    IntermediateField.finrank_fixedField_eq_card ⊤
  have h2 := Module.finrank_mul_finrank K
    (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
  rw [h1, Subgroup.card_top, Nat.card_eq_fintype_card] at h2
  exact Dvd.intro_left _ h2

variable {K L}

theorem orderOf_eq_finrank (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    orderOf σ = Module.finrank K L := by
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rcases (Nat.dvd_prime hdeg).1 (card_aut_dvd_finrank K L) with h | h
    · exfalso
      have : Subsingleton (L ≃ₐ[K] L) := Fintype.card_le_one_iff_subsingleton.1 h.le
      exact hσ (Subsingleton.elim _ _)
    · exact h
  have hdvd : orderOf σ ∣ Module.finrank K L := hcard ▸ orderOf_dvd_card
  rcases (Nat.dvd_prime hdeg).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hσ
  · exact h

theorem pow_finrank_eq_one (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank hdeg σ hσ]
  exact pow_orderOf_eq_one σ

theorem pow_injective_fin (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    Function.Injective fun i : Fin (Module.finrank K L) => σ ^ (i : ℕ) := by
  intro i j hij
  have h := pow_injOn_Iio_orderOf (x := σ) (by simpa [orderOf_eq_finrank hdeg σ hσ] using i.2)
    (by simpa [orderOf_eq_finrank hdeg σ hσ] using j.2) hij
  exact Fin.ext h

theorem linearIndependent_pow (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    LinearIndependent L fun i : Fin (Module.finrank K L) =>
      (((σ ^ (i : ℕ) : L ≃ₐ[K] L) : L →ₐ[K] L)).toLinearMap := by
  have h := (linearIndependent_toLinearMap K L L).comp
    (fun i : Fin (Module.finrank K L) => ((σ ^ (i : ℕ) : L ≃ₐ[K] L) : L →ₐ[K] L))
    (AlgEquiv.coe_algHom_injective.comp (pow_injective_fin hdeg σ hσ))
  exact h

end Galois

section Split

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)

def embPow (i : ℕ) : L →ₐ[K] A := ι.comp ((σ ^ i : L ≃ₐ[K] L) : L →ₐ[K] L)

@[scoped simp] theorem embPow_apply (i : ℕ) (x : L) : embPow K L A σ ι i x = ι ((σ ^ i) x) := rfl

def psiLeft : L →ₐ[K] (Fin (Module.finrank K L) → A) :=
  Pi.algHom K (fun _ => A) fun i => embPow K L A σ ι (i : ℕ)

@[scoped simp] theorem psiLeft_apply (x : L) (i : Fin (Module.finrank K L)) :
    psiLeft K L A σ ι x i = ι ((σ ^ (i : ℕ)) x) := rfl

def psi : L ⊗[K] A →ₐ[K] (Fin (Module.finrank K L) → A) :=
  Algebra.TensorProduct.lift (psiLeft K L A σ ι) (Pi.constAlgHom K (Fin (Module.finrank K L)) A)
    fun _ _ => Commute.all _ _

@[scoped simp] theorem psi_tmul (x : L) (a : A) (i : Fin (Module.finrank K L)) :
    psi K L A σ ι (x ⊗ₜ a) i = ι ((σ ^ (i : ℕ)) x) * a := by
  simp [psi, Algebra.TensorProduct.lift_tmul]

theorem psi_one_tmul (a : A) : psi K L A σ ι (1 ⊗ₜ a) = fun _ => a := by
  funext i; simp

theorem psi_smul (a : A) (z : L ⊗[K] A) : psi K L A σ ι (a • z) = a • psi K L A σ ι z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      have h : a • (x ⊗ₜ[K] b) = x ⊗ₜ[K] (a * b) := by
        rw [TensorProduct.RightActions.smul_def]
        simp [TensorProduct.smul_tmul', smul_eq_mul]
      rw [h]
      funext i
      simp only [psi_tmul, Pi.smul_apply, smul_eq_mul]
      ring
  | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]

def psiLinear : (L ⊗[K] A) →ₗ[A] (Fin (Module.finrank K L) → A) where
  toFun := psi K L A σ ι
  map_add' := map_add _
  map_smul' a z := psi_smul K L A σ ι a z

@[scoped simp] theorem psiLinear_apply (z : L ⊗[K] A) : psiLinear K L A σ ι z = psi K L A σ ι z := rfl

theorem val_finRotate : ∀ {n : ℕ} (i : Fin n), ((finRotate n i : Fin n) : ℕ) = ((i : ℕ) + 1) % n
  | 0, i => i.elim0
  | n + 1, i => by
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.2) with h | h
      · have hi : i = ⟨(i : ℕ), i.2⟩ := rfl
        rw [hi, finRotate_of_lt h]
        simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]
      · have hi : i = Fin.last n := Fin.ext h
        subst hi
        rw [finRotate_last]
        simp

theorem pow_mod_apply {n : ℕ} (hℓ : σ ^ Module.finrank K L = 1) (x : L) :
    (σ ^ (n % Module.finrank K L)) x = (σ ^ n) x := by
  conv_rhs => rw [← Nat.mod_add_div n (Module.finrank K L), pow_add, pow_mul, hℓ, one_pow, mul_one]

theorem psi_sigmaTensor (hℓ : σ ^ Module.finrank K L = 1) (z : L ⊗[K] A)
    (i : Fin (Module.finrank K L)) :
    psi K L A σ ι (AutomorphicForm.sigmaTensor K L A σ z) i = psi K L A σ ι z (finRotate _ i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      have hs : AutomorphicForm.sigmaTensor K L A σ (x ⊗ₜ[K] b) = σ x ⊗ₜ[K] b := rfl
      rw [hs, psi_tmul, psi_tmul, val_finRotate, pow_mod_apply K L σ hℓ, pow_succ, AlgEquiv.mul_apply]
  | add z w hz hw => simp [map_add, hz, hw]

end Split

section Bijective

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)

noncomputable def aBasis : Module.Basis (Fin (Module.finrank K L)) A (L ⊗[K] A) :=
  TensorProduct.RightActions.Algebra.TensorProduct.basis A (Module.finBasis K L)

theorem aBasis_apply (j : Fin (Module.finrank K L)) :
    aBasis K L A j = (Module.finBasis K L j) ⊗ₜ[K] (1 : A) := by
  simp [aBasis, TensorProduct.RightActions.Algebra.TensorProduct.basis, Algebra.TensorProduct.basis_apply]

noncomputable def dedekindMatrix : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) L :=
  Matrix.of fun i j => (σ ^ (i : ℕ)) (Module.finBasis K L j)

@[scoped simp] theorem dedekindMatrix_apply (i j : Fin (Module.finrank K L)) :
    dedekindMatrix K L σ i j = (σ ^ (i : ℕ)) (Module.finBasis K L j) := rfl

variable {K L} in

theorem det_dedekindMatrix_ne_zero (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (dedekindMatrix K L σ).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hlin := linearIndependent_pow hdeg σ hσ
  rw [Fintype.linearIndependent_iff] at hlin
  apply hc0
  funext i
  refine hlin c ?_ i
  apply (Module.finBasis K L).ext
  intro j
  have hj := congrFun hc j
  simp only [Matrix.vecMul, dotProduct, dedekindMatrix_apply, Pi.zero_apply] at hj
  simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hj

theorem toMatrix_psiLinear :
    LinearMap.toMatrix (aBasis K L A) (Pi.basisFun A (Fin (Module.finrank K L))) (psiLinear K L A σ ι) =
      ι.toRingHom.mapMatrix (dedekindMatrix K L σ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, aBasis_apply, psiLinear_apply, Pi.basisFun_repr, psi_tmul, mul_one]
  rfl

variable {K L} in
theorem isUnit_det_toMatrix_psiLinear (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    IsUnit (LinearMap.toMatrix (aBasis K L A) (Pi.basisFun A (Fin (Module.finrank K L)))
      (psiLinear K L A σ ι)).det := by
  rw [toMatrix_psiLinear, ← RingHom.map_det]
  exact (isUnit_iff_ne_zero.2 (det_dedekindMatrix_ne_zero σ hdeg hσ)).map _

variable {K L} in

noncomputable def psiLinearEquiv (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (L ⊗[K] A) ≃ₗ[A] (Fin (Module.finrank K L) → A) :=
  LinearEquiv.ofIsUnitDet (isUnit_det_toMatrix_psiLinear A σ ι hdeg hσ)

variable {K L} in
@[scoped simp] theorem psiLinearEquiv_apply (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (z : L ⊗[K] A) :
    psiLinearEquiv A σ ι hdeg hσ z = psi K L A σ ι z := by
  have h : ((psiLinearEquiv A σ ι hdeg hσ).toLinearMap) = psiLinear K L A σ ι :=
    LinearEquiv.coe_ofIsUnitDet _
  exact LinearMap.congr_fun h z

variable {K L} in
theorem psi_bijective (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    Function.Bijective (psi K L A σ ι) := by
  have h := (psiLinearEquiv A σ ι hdeg hσ).bijective
  have hf : ((psiLinearEquiv A σ ι hdeg hσ) : L ⊗[K] A → _) = psi K L A σ ι := by
    funext z; exact psiLinearEquiv_apply A σ ι hdeg hσ z
  rwa [hf] at h

variable {K L} in

noncomputable def psiEquiv (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (L ⊗[K] A) ≃ₐ[K] (Fin (Module.finrank K L) → A) :=
  AlgEquiv.ofBijective (psi K L A σ ι) (psi_bijective A σ ι hdeg hσ)

variable {K L} in
@[scoped simp] theorem psiEquiv_apply (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (z : L ⊗[K] A) :
    psiEquiv A σ ι hdeg hσ z = psi K L A σ ι z := rfl

variable {K L} in

theorem psiEquiv_symm_smul (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (a : A)
    (t : Fin (Module.finrank K L) → A) :
    (psiEquiv A σ ι hdeg hσ).symm (a • t) = a • (psiEquiv A σ ι hdeg hσ).symm t := by
  apply (psiEquiv A σ ι hdeg hσ).injective
  rw [AlgEquiv.apply_symm_apply, psiEquiv_apply, psi_smul, ← psiEquiv_apply A σ ι hdeg hσ,
    AlgEquiv.apply_symm_apply]

variable {K L} in
theorem psiEquiv_symm_const (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (a : A) :
    (psiEquiv A σ ι hdeg hσ).symm (fun _ => a) = 1 ⊗ₜ a := by
  apply (psiEquiv A σ ι hdeg hσ).injective
  rw [AlgEquiv.apply_symm_apply, psiEquiv_apply, psi_one_tmul]

end Bijective

section Shift

variable {G : Type*} [Group G] {n : ℕ}

def shift (n : ℕ) : (Fin n → G) ≃* (Fin n → G) where
  toEquiv := Equiv.arrowCongr (finRotate n) (Equiv.refl G) |>.symm
  map_mul' _ _ := rfl

@[scoped simp] theorem shift_apply (t : Fin n → G) (i : Fin n) : shift n t i = t (finRotate n i) := rfl

theorem shift_iterate_apply (m : ℕ) (t : Fin n → G) (i : Fin n) :
    ((shift n : (Fin n → G) → Fin n → G)^[m]) t i = t (((finRotate n : Fin n → Fin n)^[m]) i) := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, shift_apply, Function.iterate_succ_apply' (finRotate n)]

theorem val_finRotate_iterate (m : ℕ) (i : Fin n) :
    ((((finRotate n : Fin n → Fin n)^[m]) i : Fin n) : ℕ) = ((i : ℕ) + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.2]
  | succ m ih =>
      rw [Function.iterate_succ_apply', val_finRotate, ih, Nat.mod_add_mod, Nat.add_assoc]

def headString (n : ℕ) (g : G) : Fin n → G := fun k => if (k : ℕ) = 0 then g else 1

@[scoped simp] theorem headString_apply (g : G) (k : Fin n) :
    headString n g k = if (k : ℕ) = 0 then g else 1 := rfl

theorem prod_map_ite_mod_eq (g : G) (k : ℕ) (hk : k < n) :
    ((List.range n).map fun i => if (k + i) % n = 0 then g else (1 : G)).prod = g := by

  set j : ℕ := if k = 0 then 0 else n - k with hj
  have hjn : j < n := by rw [hj]; split_ifs <;> omega
  have hval : ∀ i, i < n → ((k + i) % n = 0 ↔ i = j) := by
    intro i hi
    rw [hj]
    constructor
    · intro h
      have hlt : k + i < 2 * n := by omega
      rcases Nat.eq_zero_or_pos (k + i) with h0 | hpos
      · split_ifs <;> omega
      ·
        have hdvd : n ∣ k + i := Nat.dvd_of_mod_eq_zero h
        obtain ⟨q, hq⟩ := hdvd
        have hq1 : q = 1 := by
          rcases q with _ | _ | q
          · omega
          · rfl
          · nlinarith
        subst hq1
        split_ifs <;> omega
    · intro h
      subst h
      split_ifs with h0
      · subst h0; simp
      · have : k + (n - k) = n := by omega
        rw [this, Nat.mod_self]

  have hlist : ((List.range n).map fun i => if (k + i) % n = 0 then g else (1 : G)) =
      (List.range n).map fun i => if i = j then g else 1 := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    by_cases h : i = j
    · rw [if_pos h, if_pos ((hval i hi).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hval i hi).1 h'))]
  rw [hlist]

  have hsplit : List.range n = List.range j ++ [j] ++ (List.range (n - (j + 1))).map (fun i => j + 1 + i) := by
    have : n = j + 1 + (n - (j + 1)) := by omega
    conv_lhs => rw [this]
    rw [List.range_add, List.range_succ]
  rw [hsplit, List.map_append, List.map_append, List.prod_append, List.prod_append]
  have h1 : ((List.range j).map fun i => if i = j then g else (1 : G)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    rw [if_neg (by omega)]
  have h3 : (((List.range (n - (j + 1))).map (fun i => j + 1 + i)).map
      fun i => if i = j then g else (1 : G)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rw [List.map_map, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp only [Function.comp_apply]
    rw [if_neg (by omega)]
  rw [h1, h3]
  simp

theorem prod_shift_iterate_headString (g : G) :
    ((List.range n).map fun m => ((shift n : (Fin n → G) → Fin n → G)^[m]) (headString n g)).prod =
      fun _ => g := by
  funext k
  have heval : ((List.range n).map fun m =>
      ((shift n : (Fin n → G) → Fin n → G)^[m]) (headString n g)).prod k =
      Pi.evalMonoidHom (fun _ : Fin n => G) k (((List.range n).map fun m =>
        ((shift n : (Fin n → G) → Fin n → G)^[m]) (headString n g)).prod) := rfl
  rw [heval, map_list_prod, List.map_map]
  have hf : ((Pi.evalMonoidHom (fun _ : Fin n => G) k) ∘ fun m =>
      ((shift n : (Fin n → G) → Fin n → G)^[m]) (headString n g)) =
      fun i => if ((k : ℕ) + i) % n = 0 then g else (1 : G) := by
    funext i
    simp only [Function.comp_apply, Pi.evalMonoidHom_apply, shift_iterate_apply, headString_apply,
      val_finRotate_iterate]
  rw [hf]
  exact prod_map_ite_mod_eq g k k.2

@[scoped simp] theorem shift_const (g : G) : shift n (fun _ => g) = fun _ => g := rfl

end Shift

section GLTransport

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

noncomputable def psiGL : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (Module.finrank K L) → GL (Fin 2) A) :=
  (Units.mapEquiv (psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix.toMulEquiv).trans
    ((Units.mapEquiv (Matrix.piRingEquiv (β := fun _ : Fin (Module.finrank K L) => A)
      (n := Fin 2)).toMulEquiv).trans MulEquiv.piUnits)

@[scoped simp] theorem psiGL_apply_val (g : GL (Fin 2) (L ⊗[K] A)) (i : Fin (Module.finrank K L)) (p q : Fin 2) :
    ((psiGL A σ ι hdeg hσ g i : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) p q =
      psi K L A σ ι ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) p q) i := rfl

theorem psiGL_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (AutomorphicForm.sigmaGL K L A σ g) =
      shift (Module.finrank K L) (psiGL A σ ι hdeg hσ g) := by
  funext i
  ext p q
  rw [psiGL_apply_val, shift_apply, psiGL_apply_val]
  exact psi_sigmaTensor K L A σ ι (pow_finrank_eq_one hdeg σ hσ) _ i

theorem psiGL_toTensorGL (γ : GL (Fin 2) A) :
    psiGL A σ ι hdeg hσ (AutomorphicForm.toTensorGL K L A γ) = fun _ => γ := by
  funext i
  ext p q
  rw [psiGL_apply_val]
  change psi K L A σ ι ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) p q)) i = _
  rw [psi_tmul, map_one, map_one, one_mul]

theorem psiGL_sigmaGL_iterate (m : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (((AutomorphicForm.sigmaGL K L A σ : _ → _))^[m] g) =
      ((shift (Module.finrank K L) : (Fin (Module.finrank K L) → GL (Fin 2) A) → _)^[m])
        (psiGL A σ ι hdeg hσ g) :=
  Function.Semiconj.iterate_right (f := psiGL A σ ι hdeg hσ) (fun x => psiGL_sigmaGL A σ ι hdeg hσ x) m g

theorem psiGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) =
      ((List.range (Module.finrank K L)).map fun m =>
        ((shift (Module.finrank K L) : (Fin (Module.finrank K L) → GL (Fin 2) A) → _)^[m])
          (psiGL A σ ι hdeg hσ δ)).prod := by
  unfold AutomorphicForm.normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  exact psiGL_sigmaGL_iterate A σ ι hdeg hσ m δ

noncomputable def normPreimage (γ : GL (Fin 2) A) : GL (Fin 2) (L ⊗[K] A) :=
  (psiGL A σ ι hdeg hσ).symm (headString (Module.finrank K L) γ)

theorem normString_normPreimage (γ : GL (Fin 2) A) :
    AutomorphicForm.normString K L A σ (normPreimage A σ ι hdeg hσ γ) =
      AutomorphicForm.toTensorGL K L A γ := by
  apply (psiGL A σ ι hdeg hσ).injective
  rw [psiGL_normString, psiGL_toTensorGL, normPreimage, MulEquiv.apply_symm_apply,
    prod_shift_iterate_headString]

theorem isNormConjugator_normPreimage_one (γ : GL (Fin 2) A) :
    AutomorphicForm.IsNormConjugator K L A σ γ (normPreimage A σ ι hdeg hσ γ) 1 := by
  unfold AutomorphicForm.IsNormConjugator
  rw [normString_normPreimage, inv_one, one_mul, mul_one]

theorem isNormOf_normPreimage (γ : GL (Fin 2) A) :
    AutomorphicForm.IsNormOf K L A σ γ (normPreimage A σ ι hdeg hσ γ) :=
  ⟨1, isNormConjugator_normPreimage_one A σ ι hdeg hσ γ⟩

include ι hdeg hσ in
theorem exists_isNormOf (γ : GL (Fin 2) A) : ∃ δ, AutomorphicForm.IsNormOf K L A σ γ δ :=
  ⟨_, isNormOf_normPreimage A σ ι hdeg hσ γ⟩

end GLTransport

end P2mArchSplitBrick
p2m_reactivate "P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.P2mArchSplitBrick"

namespace NormPairAux

open AutomorphicForm

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K

theorem mem_integers_iff_norm (y : Kv) : y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem coe_integers_eq_closedBall :
    (v.adicCompletionIntegers K : Set Kv) = Metric.closedBall (0 : Kv) 1 := by
  ext y
  rw [SetLike.mem_coe, mem_integers_iff_norm, Metric.mem_closedBall, dist_zero_right]

theorem norm_coe_integer_le_one (x : v.adicCompletionIntegers K) : ‖(x : Kv)‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 x.2

theorem uniformiser_ne_zero {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : (ϖ : Kv) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  exact_mod_cast h

theorem exists_valued_eq_exp_and_norm_eq {x : Kv} (hx : x ≠ 0) :
    ∃ j : ℤ, Valued.v x = WithZero.exp j ∧ ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ j := by
  have hvx : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation Kv (WithZero (Multiplicative ℤ)))).2 hx
  refine ⟨WithZero.log (Valued.v x), (WithZero.exp_log hvx).symm, ?_⟩
  rw [NumberField.FinitePlace.norm_def v x]
  conv_lhs => rw [← WithZero.exp_log hvx]
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  congr 1

theorem valued_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : Kv) = WithZero.exp (-1 : ℤ) := by

  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer v
  have hpv : Valued.v ((p : 𝓞 K) : Kv) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]

  set p' : v.adicCompletionIntegers K := algebraMap (𝓞 K) (v.adicCompletionIntegers K) p with hp'
  have hp'v : Valued.v (p' : Kv) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Kv) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : Kv) * Valued.v (ϖ : Kv) ≤ 1 * Valued.v (ϖ : Kv) :=
          mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v (ϖ : Kv) := one_mul _

  have hlt : Valued.v (ϖ : Kv) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v (ϖ : Kv) ≠ 0 := (Valuation.ne_zero_iff _).2 (uniformiser_ne_zero K v hϖ)
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v (ϖ : Kv)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem norm_uniformiser {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    ‖(ϖ : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def v, valued_uniformiser K v hϖ,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  rw [← zpow_neg_one]
  congr 1

private theorem _root_.NormPairAux.one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

p2m_export "NormPairAux" "one_lt_absNorm"
theorem norm_uniformiser_pos {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : 0 < ‖(ϖ : Kv)‖ :=
  norm_pos_iff.2 (uniformiser_ne_zero K v hϖ)

theorem norm_uniformiser_lt_one {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : ‖(ϖ : Kv)‖ < 1 := by
  rw [norm_uniformiser K v hϖ]
  exact inv_lt_one_of_one_lt₀ (one_lt_absNorm K v)

theorem exists_norm_eq_one_pow_ne_one {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ u : Kv, ‖u‖ = 1 ∧ u ^ ℓ ≠ 1 := by
  classical
  haveI : CharZero Kv := charZero_of_injective_algebraMap (algebraMap K Kv).injective
  by_contra hcon
  push_neg at hcon
  have hπ1 := norm_uniformiser_lt_one K v hϖ
  set c : Fin (ℓ + 1) → Kv := fun n => 1 + (n : ℕ) * (ϖ : Kv) with hc
  have hcnorm : ∀ n, ‖c n‖ = 1 := by
    intro n
    have hsmall : ‖((n : ℕ) : Kv) * (ϖ : Kv)‖ < 1 := by
      rw [norm_mul]
      have hn : ‖((n : ℕ) : Kv)‖ ≤ 1 := (mem_integers_iff_norm K v _).1 (natCast_mem _ n)
      calc ‖((n : ℕ) : Kv)‖ * ‖(ϖ : Kv)‖ ≤ 1 * ‖(ϖ : Kv)‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hπ1
    simp only [hc]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hsmall.ne'), norm_one,
      max_eq_left hsmall.le]
  have hcinj : Function.Injective c := by
    intro n m h
    simp only [hc, add_right_inj] at h
    have := mul_right_cancel₀ (uniformiser_ne_zero K v hϖ) h
    exact Fin.ext (by exact_mod_cast this)
  set P : Polynomial Kv := Polynomial.X ^ ℓ - Polynomial.C 1 with hP
  have hP0 : P ≠ 0 := by
    rw [hP]; exact Polynomial.X_pow_sub_C_ne_zero hℓ 1
  have hdeg : P.natDegree = ℓ := by rw [hP, Polynomial.natDegree_X_pow_sub_C]
  have hroots : (Finset.univ.image c).val ⊆ P.roots := by
    intro x hx
    rw [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map] at hx
    obtain ⟨n, -, rfl⟩ := hx
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, hP, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hcon (c n) (hcnorm n), sub_self]
  have hcard := Polynomial.card_le_degree_of_subset_roots hroots
  rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_fin, hdeg] at hcard
  omega

end Local
p2m_reactivate "P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.P2mArchSplitBrick"

section Diag

open LanglandsTunnell.CubicInduction

theorem diagUnits2_mul {A : Type*} [CommRing A] (a b a' b' : Aˣ) :
    (diagUnits2 a b : GL (Fin 2) A) * diagUnits2 a' b' = diagUnits2 (a * a') (b * b') := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_pow {A : Type*} [CommRing A] (a b : Aˣ) (n : ℕ) :
    (diagUnits2 a b : GL (Fin 2) A) ^ n = diagUnits2 (a ^ n) (b ^ n) := by
  induction n with
  | zero =>
    apply Units.ext
    rw [pow_zero, Units.val_one, coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [pow_succ, ih, diagUnits2_mul, ← pow_succ, ← pow_succ]

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    AutomorphicForm.toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom : A →* L ⊗[K] A) a)
        (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom : A →* L ⊗[K] A) b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, coe_diagUnits2]

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A γ) = AutomorphicForm.toTensorGL K L A γ := by
  apply Units.ext
  ext i j
  change AutomorphicForm.sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j)) =
    (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j)
  have hs : AutomorphicForm.sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j)) =
      σ 1 ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) := rfl
  rw [hs, map_one]

theorem normString_toTensorGL (γ : GL (Fin 2) A) :
    AutomorphicForm.normString K L A σ (AutomorphicForm.toTensorGL K L A γ) =
      AutomorphicForm.toTensorGL K L A (γ ^ Module.finrank K L) := by
  unfold AutomorphicForm.normString
  have hfix : ∀ i : ℕ, ((AutomorphicForm.sigmaGL K L A σ : _ → _)^[i]) (AutomorphicForm.toTensorGL K L A γ) =
      AutomorphicForm.toTensorGL K L A γ :=
    fun i => Function.iterate_fixed (sigmaGL_toTensorGL K L A σ γ) i
  rw [List.map_congr_left (fun i _ => hfix i), List.map_const', List.prod_replicate, List.length_range, map_pow]

variable {K L}

theorem exists_diagUnits2_eq_normPreimage (ι : L →ₐ[K] A) (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (a b : Aˣ) :
    ∃ α β : (L ⊗[K] A)ˣ, diagUnits2 α β = P2mArchSplitBrick.normPreimage A σ ι hdeg hσ (diagUnits2 a b) := by
  set δ := P2mArchSplitBrick.normPreimage A σ ι hdeg hσ (diagUnits2 a b) with hδ
  have hψ : P2mArchSplitBrick.psiGL A σ ι hdeg hσ δ =
      P2mArchSplitBrick.headString (Module.finrank K L) (diagUnits2 a b) := by
    rw [hδ, P2mArchSplitBrick.normPreimage, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective (P2mArchSplitBrick.psi K L A σ ι) :=
    (P2mArchSplitBrick.psi_bijective A σ ι hdeg hσ).1
  have hoff : ∀ p q : Fin 2, p ≠ q → (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) p q = 0 := by
    intro p q hpq
    apply hinj
    rw [map_zero]
    funext i
    have h := P2mArchSplitBrick.psiGL_apply_val A σ ι hdeg hσ δ i p q
    rw [hψ] at h
    rw [← h, P2mArchSplitBrick.headString_apply, Pi.zero_apply]
    split_ifs
    · rw [coe_diagUnits2]
      fin_cases p <;> fin_cases q <;> simp_all
    · rw [Units.val_one]
      exact Matrix.one_apply_ne hpq
  have hdet : IsUnit ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
    have h := (Matrix.GeneralLinearGroup.det δ).isUnit
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hoff 0 1 (by decide), hoff 1 0 (by decide),
      mul_zero, sub_zero] at h
    exact h
  obtain ⟨hα, hβ⟩ := IsUnit.mul_iff.mp hdet
  refine ⟨hα.unit, hβ.unit, Units.ext ?_⟩
  rw [coe_diagUnits2]
  ext p q
  fin_cases p <;> fin_cases q
  · simp [IsUnit.unit_spec]
  · simp [hoff 0 1 (by decide)]
  · simp [hoff 1 0 (by decide)]
  · simp [IsUnit.unit_spec]

end Diag
p2m_reactivate "P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.P2mArchSplitBrick"

section Inert

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem inertiaDeg_eq_finrank_of_forall_eq (w : v.Extension (𝓞 L)) (hone : ∀ w' : v.Extension (𝓞 L), w' = w)
    (hw : Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1) :
    v.asIdeal.inertiaDeg' w.1.asIdeal = Module.finrank K L := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  rw [Finset.sum_eq_single w (fun w' _ hw' => absurd (hone w') hw') (fun h => absurd (Finset.mem_univ w) h),
    hw, one_mul] at hsum
  exact hsum

end Inert
p2m_reactivate "P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.P2mArchSplitBrick"

end NormPairAux
p2m_reactivate "P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.P2mArchSplitBrick"

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (w : v.Extension (𝓞 L))
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (e₁ e₂ : ℕ) :
    ∃ (a b : (v.adicCompletion K)ˣ) (α β : (L ⊗[K] v.adicCompletion K)ˣ),
      a ≠ b ∧
      normString K L (v.adicCompletion K) σ (diagUnits2 α β) = toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) ∧
      ‖((a : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ (v.asIdeal.inertiaDeg' w.1.asIdeal * e₁) ∧
      ‖((b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ (v.asIdeal.inertiaDeg' w.1.asIdeal * e₂) := by
  classical
  obtain ⟨hGal, _, _⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hdeg σ hσ
  haveI := hGal
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  set ℓ := Module.finrank K L with hℓ
  have hℓpos : 0 < ℓ := hdeg.pos
  set f := v.asIdeal.inertiaDeg' w.1.asIdeal with hf
  have hπ0 : ((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := NormPairAux.uniformiser_ne_zero K v hϖK
  have hπpos := NormPairAux.norm_uniformiser_pos K v hϖK
  have hπ1 := NormPairAux.norm_uniformiser_lt_one K v hϖK
  obtain ⟨u, hu1, huℓ⟩ := NormPairAux.exists_norm_eq_one_pow_ne_one K v hϖK ℓ hℓpos
  have hu0 : u ≠ 0 := by rw [← norm_pos_iff, hu1]; exact one_pos
  have hune : u ≠ 1 := fun h => huℓ (by rw [h, one_pow])
  have hexp : ∀ m n : ℕ, ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ m =
      ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ n → m = n := by
    intro m n h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (pow_lt_pow_right_of_lt_one₀ hπpos hπ1 hlt).ne' h
    · exact (pow_lt_pow_right_of_lt_one₀ hπpos hπ1 hlt).ne h
  by_cases hnt : Nontrivial (v.Extension (𝓞 L))
  ·
    obtain ⟨ι⟩ := NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime K L hdeg σ hσ v hv hnt
    set a : (v.adicCompletion K)ˣ :=
      Units.mk0 (((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (f * e₁)) (pow_ne_zero _ hπ0) with ha
    set b : (v.adicCompletion K)ˣ :=
      Units.mk0 (u * ((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K) ^ (f * e₂))
        (mul_ne_zero hu0 (pow_ne_zero _ hπ0)) with hb
    obtain ⟨α, β, hαβ⟩ := NormPairAux.exists_diagUnits2_eq_normPreimage (v.adicCompletion K) σ ι hdeg hσ a b
    refine ⟨a, b, α, β, ?_, ?_, ?_, ?_⟩
    · intro hab
      have hval : ((a : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (b : v.adicCompletion K) := by rw [hab]
      simp only [ha, hb, Units.val_mk0] at hval
      have hn := congrArg (fun x : v.adicCompletion K => ‖x‖) hval
      simp only [norm_mul, norm_pow, hu1, one_mul] at hn
      have he := hexp _ _ hn
      rw [he] at hval
      exact hune ((mul_eq_right₀ (pow_ne_zero _ hπ0)).mp hval.symm)
    · rw [hαβ]
      exact P2mArchSplitBrick.normString_normPreimage (v.adicCompletion K) σ ι hdeg hσ (diagUnits2 a b)
    · simp only [ha, Units.val_mk0, norm_pow]
    · simp only [hb, Units.val_mk0, norm_mul, norm_pow, hu1, one_mul]
  ·
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hone : ∀ w' : v.Extension (𝓞 L), w' = w := fun w' => @Subsingleton.elim _ hnt w' w
    have hw1 : Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1 := by
      have h := hv w.1 w.2
      rwa [w.2] at h
    have hfℓ : f = ℓ := NormPairAux.inertiaDeg_eq_finrank_of_forall_eq K L v w hone hw1
    set a₀ : (v.adicCompletion K)ˣ :=
      Units.mk0 (((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K) ^ e₁) (pow_ne_zero _ hπ0) with ha₀
    set b₀ : (v.adicCompletion K)ˣ :=
      Units.mk0 (u * ((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K) ^ e₂)
        (mul_ne_zero hu0 (pow_ne_zero _ hπ0)) with hb₀
    set ιK : v.adicCompletion K →* L ⊗[K] v.adicCompletion K :=
      ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom :
        v.adicCompletion K →* L ⊗[K] v.adicCompletion K) with hιK
    refine ⟨a₀ ^ ℓ, b₀ ^ ℓ, Units.map ιK a₀, Units.map ιK b₀, ?_, ?_, ?_, ?_⟩
    · intro hab
      have hval : (((a₀ ^ ℓ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) =
          ((b₀ ^ ℓ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
        rw [hab]
      simp only [Units.val_pow_eq_pow_val, ha₀, hb₀, Units.val_mk0] at hval
      have hn := congrArg (fun x : v.adicCompletion K => ‖x‖) hval
      simp only [norm_pow, norm_mul, hu1, one_mul, ← pow_mul] at hn
      have he : e₁ = e₂ := by
        have := hexp _ _ hn
        exact Nat.eq_of_mul_eq_mul_right hℓpos this
      rw [he, mul_pow] at hval
      exact huℓ ((mul_eq_right₀ (pow_ne_zero _ (pow_ne_zero _ hπ0))).mp hval.symm)
    · rw [← NormPairAux.toTensorGL_diagUnits2 K L (v.adicCompletion K), NormPairAux.normString_toTensorGL,
        NormPairAux.diagUnits2_pow]
    · simp only [Units.val_pow_eq_pow_val, ha₀, Units.val_mk0, norm_pow, ← pow_mul, hfℓ, mul_comm]
    · simp only [Units.val_pow_eq_pow_val, hb₀, Units.val_mk0, norm_pow, norm_mul, hu1, one_mul, ← pow_mul, hfℓ,
        mul_comm]

end S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime (solution)
