-- Prove2me | Definitions.Def_GroundTheory_Brauer_CrossedProductIso
-- name    : GroundTheory_Brauer_CrossedProductIso
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:27.963119+00:00
-- url     : https://prove2.me/theorems/70a99ac4-6043-566d-83c6-05fbbc53c600
-- title:
--   Crossed Product Iso
-- statement:
--   Definitions and structural lemmas for Crossed Product Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Theorems.Thm_GroundTheory_Brauer_AlgEquiv_exists_unit_conj
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mk_mem_relBrauer_iff
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_u
import Theorems.Thm_GroundTheory_Brauer_H2mul_coe_toRelBrauer
import Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauerHom_apply
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_injective
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_centralizer_centralizer
import Theorems.Thm_GroundTheory_Brauer_degree_baseChangeCSA
import Theorems.Thm_GroundTheory_Brauer_degree_matrixCSA
import Theorems.Thm_GroundTheory_Brauer_degree_tensorCSA
import Theorems.Thm_GroundTheory_Brauer_exists_unit_conj
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_of_algEquiv_matrix
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.BrauerGroup.baseChange_mk
attribute [local simp] GroundTheory.Brauer.CrossedProduct.basis_apply
attribute [local simp] GroundTheory.Brauer.CrossedProduct.toMatrix_incl
attribute [local simp] GroundTheory.Brauer.CrossedProduct.toMatrix_u
attribute [local simp] GroundTheory.Brauer.H2mul.coe_toRelBrauer
attribute [local simp] GroundTheory.Brauer.H2mul.mulEquivH2_mk
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauerHom_apply
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauer_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.degree_baseChangeCSA
attribute [local simp] GroundTheory.Brauer.degree_matrixCSA
attribute [local simp] GroundTheory.Brauer.degree_tensorCSA
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier
attribute [local simp] GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open TensorProduct Module groupCohomology
universe u
section Symbols
variable {K L B : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B] [FiniteDimensional K B]
namespace MaximalEmbedding
variable (ι : L →ₐ[K] B)
theorem centralizer_range_eq (h : finrank K B = finrank K L ^ 2) :
    Subalgebra.centralizer K (ι.range : Set B) = ι.range := by
  have hinj : Function.Injective ι := RingHom.injective ι.toRingHom
  let e := AlgEquiv.ofInjective ι hinj
  have : IsSimpleRing ι.range := IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  have hr : finrank K ι.range = finrank K L := e.toLinearEquiv.finrank_eq.symm
  have hmul := finrank_mul_finrank_centralizer ι.range
  have hL : 0 < finrank K L := Module.finrank_pos
  have hle : ι.range ≤ Subalgebra.centralizer K (ι.range : Set B) := by
    intro x hx
    obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).1 hx
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, rfl⟩ := (AlgHom.mem_range _).1 hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hdim : finrank K ι.range = finrank K (Subalgebra.centralizer K (ι.range : Set B)) := by
    rw [hr, h, sq] at hmul
    rw [hr]
    exact (Nat.eq_of_mul_eq_mul_left hL hmul).symm
  exact (Subalgebra.toSubmodule_injective (Submodule.eq_of_le_of_finrank_eq
    (Subalgebra.toSubmodule.monotone hle) hdim)).symm
theorem exists_unit_mul_eq (σ : L ≃ₐ[K] L) : ∃ a : Bˣ, ∀ x, (a : B) * ι x = ι (σ x) * a := by
  obtain ⟨a, ha⟩ := exists_unit_conj ι (ι.comp σ.toAlgHom)
  refine ⟨a, fun x => ?_⟩
  have hx : ι (σ x) = a * ι x * ↑a⁻¹ := ha x
  rw [hx, Units.inv_mul_cancel_right]
def symbol (σ : L ≃ₐ[K] L) : Bˣ := (exists_unit_mul_eq ι σ).choose
theorem symbol_mul (σ : L ≃ₐ[K] L) (x : L) :
    (symbol ι σ : B) * ι x = ι (σ x) * symbol ι σ :=
  (exists_unit_mul_eq ι σ).choose_spec x
theorem symbol_inv_mul (σ : L ≃ₐ[K] L) (x : L) :
    (↑(symbol ι σ)⁻¹ : B) * ι (σ x) = ι x * ↑(symbol ι σ)⁻¹ := by
  rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, symbol_mul, Units.mul_inv_cancel_right]
theorem commute_symbols (σ τ : L ≃ₐ[K] L) (x : L) :
    ι x * ((symbol ι σ : B) * symbol ι τ * ↑(symbol ι (σ * τ))⁻¹) =
      ((symbol ι σ : B) * symbol ι τ * ↑(symbol ι (σ * τ))⁻¹) * ι x := by
  obtain ⟨y, rfl⟩ : ∃ y, (σ * τ) y = x := ⟨(σ * τ).symm x, (σ * τ).apply_symm_apply x⟩
  calc ι ((σ * τ) y) * ((symbol ι σ : B) * symbol ι τ * ↑(symbol ι (σ * τ))⁻¹)
      = (ι (σ (τ y)) * symbol ι σ) * symbol ι τ * ↑(symbol ι (σ * τ))⁻¹ := by
        rw [AlgEquiv.mul_apply]; simp only [mul_assoc]
    _ = symbol ι σ * (ι (τ y) * symbol ι τ) * ↑(symbol ι (σ * τ))⁻¹ := by
        rw [← symbol_mul]; simp only [mul_assoc]
    _ = symbol ι σ * symbol ι τ * (ι y * ↑(symbol ι (σ * τ))⁻¹) := by
        rw [← symbol_mul]; simp only [mul_assoc]
    _ = _ := by rw [← symbol_inv_mul]; simp only [mul_assoc]
variable (h : finrank K B = finrank K L ^ 2)
include h
theorem exists_eq_symbols (σ τ : L ≃ₐ[K] L) :
    ∃ a : L, ι a = (symbol ι σ : B) * symbol ι τ * ↑(symbol ι (σ * τ))⁻¹ := by
  have hc : (symbol ι σ : B) * symbol ι τ * ↑(symbol ι (σ * τ))⁻¹ ∈
      Subalgebra.centralizer K (ι.range : Set B) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).1 hg
    exact commute_symbols ι σ τ x
  rw [centralizer_range_eq ι h] at hc
  exact (AlgHom.mem_range _).1 hc
def cocycleVal (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) : L := (exists_eq_symbols ι h p.1 p.2).choose
theorem map_cocycleVal (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) :
    ι (cocycleVal ι h p) = (symbol ι p.1 : B) * symbol ι p.2 * ↑(symbol ι (p.1 * p.2))⁻¹ :=
  (exists_eq_symbols ι h p.1 p.2).choose_spec
theorem cocycleVal_ne_zero (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) : cocycleVal ι h p ≠ 0 := by
  intro h0
  have hp := map_cocycleVal ι h p
  rw [h0, map_zero] at hp
  exact (symbol ι p.1 * symbol ι p.2 * (symbol ι (p.1 * p.2))⁻¹).ne_zero
    (by rw [Units.val_mul, Units.val_mul]; exact hp.symm)
def cocycle (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) : Lˣ :=
  Units.mk0 (cocycleVal ι h p) (cocycleVal_ne_zero ι h p)
theorem symbol_mul_symbol (σ τ : L ≃ₐ[K] L) :
    (symbol ι σ : B) * symbol ι τ = ι (cocycle ι h (σ, τ) : L) * symbol ι (σ * τ) := by
  rw [cocycle, Units.val_mk0, map_cocycleVal, Units.inv_mul_cancel_right]
theorem symbol_one : (symbol ι 1 : B) = ι (cocycle ι h (1, 1) : L) := by
  have h1 := symbol_mul_symbol ι h 1 1
  rw [mul_one] at h1
  exact (Units.mul_left_inj (symbol ι 1)).1 h1
theorem isMulCocycle₂_cocycle : IsMulCocycle₂ (cocycle ι h) := by
  intro g k j
  have hinj : Function.Injective ι := RingHom.injective ι.toRingHom
  have key : ι (↑(cocycle ι h (g * k, j) * cocycle ι h (g, k))) * ↑(symbol ι (g * k * j)) =
      ι (↑(g • cocycle ι h (k, j) * cocycle ι h (g, k * j))) * ↑(symbol ι (g * k * j)) := by
    calc _ = ι ↑(cocycle ι h (g, k)) * (ι ↑(cocycle ι h (g * k, j)) * ↑(symbol ι (g * k * j))) := by
          rw [mul_comm (cocycle ι h (g * k, j)), Units.val_mul, map_mul, mul_assoc]
      _ = ↑(symbol ι g) * ↑(symbol ι k) * ↑(symbol ι j) := by
          rw [← symbol_mul_symbol, ← mul_assoc, ← symbol_mul_symbol]
      _ = ↑(symbol ι g) * (ι ↑(cocycle ι h (k, j)) * ↑(symbol ι (k * j))) := by
          rw [← symbol_mul_symbol, mul_assoc]
      _ = ι (g ↑(cocycle ι h (k, j))) * (↑(symbol ι g) * ↑(symbol ι (k * j))) := by
          rw [← mul_assoc, symbol_mul, mul_assoc]
      _ = _ := by
          rw [symbol_mul_symbol, ← mul_assoc, ← map_mul, mul_assoc g k j, Units.val_mul,
            CrossedProduct.val_smul_units]
  exact Units.ext (hinj ((Units.mul_left_inj (symbol ι (g * k * j))).1 key))
def toAlgHom : CrossedProduct (isMulCocycle₂_cocycle ι h) →ₐ[K] B :=
  CrossedProduct.lift ι (fun σ => (symbol ι σ : B)) (symbol_mul ι)
    (fun σ τ => symbol_mul_symbol ι h σ τ) (symbol_one ι h)
theorem toAlgHom_bijective [IsGalois K L] : Function.Bijective (toAlgHom ι h) := by
  have hinj := RingHom.injective (toAlgHom ι h).toRingHom
  refine ⟨hinj, ?_⟩
  have hd : finrank K (CrossedProduct (isMulCocycle₂_cocycle ι h)) = finrank K B := by
    rw [CrossedProduct.finrank_eq_sq, h]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (toAlgHom ι h).toLinearMap) hd).mp hinj
end MaximalEmbedding
open MaximalEmbedding in

theorem exists_algEquiv_crossedProduct [IsGalois K L] (ι : L →ₐ[K] B)
    (h : finrank K B = finrank K L ^ 2) :
    ∃ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (hf : IsMulCocycle₂ f),
      Nonempty (CrossedProduct hf ≃ₐ[K] B) :=
  ⟨cocycle ι h, isMulCocycle₂_cocycle ι h,
    ⟨AlgEquiv.ofBijective (toAlgHom ι h) (toAlgHom_bijective ι h)⟩⟩
end Symbols
section Representative
variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
theorem exists_isBrauerEquivalent_finrank_eq_of_mem_relBrauer (A : CSA.{u, u} K)
    (hA : (⟦A⟧ : BrauerGroup.{u, u} K) ∈ BrauerGroup.relBrauer K L) :
    ∃ B : CSA.{u, u} K, IsBrauerEquivalent A B ∧ finrank K B = finrank K L ^ 2 ∧
      Nonempty (L →ₐ[K] B) := by
  classical
  obtain ⟨s, ⟨e⟩⟩ := (BrauerGroup.mk_mem_relBrauer_iff A).1 hA
  have hs : s ≠ 0 := by
    rintro rfl
    exact one_ne_zero (e.injective (Subsingleton.elim _ _) : (1 : L ⊗[K] A) = 0)
  have : NeZero s := ⟨hs⟩
  set n := finrank K L with hn
  have hn0 : 0 < n := Module.finrank_pos
  have : NeZero n := ⟨hn0.ne'⟩

  let lm : L →ₐ[K] Matrix (Fin n) (Fin n) K := Algebra.leftMulMatrix (Module.finBasis K L)
  let R := A ⊗[K] Matrix (Fin n) (Fin n) K
  let j : L ⊗[K] A →ₐ[K] R :=
    (Algebra.TensorProduct.map (AlgHom.id K A) lm).comp
      (Algebra.TensorProduct.comm K L A).toAlgHom
  let ι : L →ₐ[K] R := Algebra.TensorProduct.includeRight.comp lm
  have hcomm : ∀ (x : L ⊗[K] A) (l : L), j x * ι l = ι l * j x := by
    intro x l
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l' a =>
      simp only [j, ι, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.includeRight_apply]
      change (a ⊗ₜ[K] lm l' : A ⊗[K] Matrix (Fin n) (Fin n) K) * (1 ⊗ₜ lm l) =
        (1 ⊗ₜ lm l) * (a ⊗ₜ[K] lm l')
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, ← map_mul, ← map_mul, mul_comm l' l]
    | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]

  let eK : L ⊗[K] A ≃ₐ[K] Matrix (Fin s) (Fin s) L := e.restrictScalars K
  let ψ : Matrix (Fin s) (Fin s) K →ₐ[K] R :=
    j.comp (eK.symm.toAlgHom.comp (Algebra.ofId K L).mapMatrix)
  have hψ : Function.Injective ψ := RingHom.injective ψ.toRingHom
  let S := ψ.range
  let eS : Matrix (Fin s) (Fin s) K ≃ₐ[K] S := AlgEquiv.ofInjective ψ hψ
  have : IsSimpleRing S := IsSimpleRing.of_ringEquiv eS.toRingEquiv inferInstance
  have : Algebra.IsCentral K S := Algebra.IsCentral.of_algEquiv K _ _ eS
  let C := Subalgebra.centralizer K (S : Set R)
  have : IsSimpleRing C := isSimpleRing_centralizer S

  have hιC : ∀ l, ι l ∈ C := by
    intro l
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    obtain ⟨M, rfl⟩ := (AlgHom.mem_range _).1 hg
    exact hcomm (eK.symm ((Algebra.ofId K L).mapMatrix M)) l

  have : Algebra.IsCentral K C := by
    refine ⟨fun z hz => ?_⟩
    rw [Subalgebra.mem_center_iff] at hz
    have hzC : (z : R) ∈ Subalgebra.centralizer K (C : Set R) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (hz ⟨g, hg⟩)
    have hzS : (z : R) ∈ S := by
      rw [← centralizer_centralizer S]
      exact hzC
    obtain ⟨M, hM⟩ := (AlgHom.mem_range _).1 hzS
    have hMc : M ∈ Subalgebra.center K (Matrix (Fin s) (Fin s) K) := by
      rw [Subalgebra.mem_center_iff]
      intro N
      apply hψ
      rw [map_mul, map_mul, hM]
      exact (Subalgebra.mem_centralizer_iff K).mp z.2 (ψ N) (AlgHom.mem_range_self _ N)
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hMc)
    refine Algebra.mem_bot.mpr ⟨k, Subtype.ext ?_⟩
    rw [← hM, ← hk, AlgHom.commutes]
    rfl

  have hAs : finrank K A = s ^ 2 := by
    have h1 := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
      mul_one] at h1
    rw [h1, sq]
  have hR : finrank K R = finrank K A * n ^ 2 := by
    rw [Module.finrank_tensorProduct, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
      mul_one, sq]
  have hS : finrank K S = s ^ 2 := by
    rw [← eS.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one, sq]
  have hC : finrank K C = n ^ 2 := by
    have h := finrank_mul_finrank_centralizer S
    rw [hS, hR, hAs] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hs) 2) h

  have hRA : IsBrauerEquivalent (csaOf K R) A :=
    isBrauerEquivalent_of_algEquiv_matrix (C := A)
      (matrixEquivTensor (Fin n) K A).symm (matrixFinOneAlgEquiv (K := K) A).symm
  have hRC : IsBrauerEquivalent (csaOf K R) (csaOf K C) :=
    isBrauerEquivalent_of_algEquiv_matrix (C := C)
      ((tensorCentralizerAlgEquiv S).symm.trans <|
        (Algebra.TensorProduct.congr eS.symm AlgEquiv.refl).trans <|
        (Algebra.TensorProduct.comm K _ _).trans (matrixEquivTensor (Fin s) K C).symm)
      (matrixFinOneAlgEquiv (K := K) C).symm
  exact ⟨csaOf K C, hRA.symm.trans hRC, hC, ⟨ι.codRestrict C hιC⟩⟩
end Representative
namespace H2mul
end H2mul
section Iso
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
namespace H2mul
theorem exists_toBrauer_eq (x : BrauerGroup.{u, u} K) (hx : x ∈ BrauerGroup.relBrauer K L) :
    ∃ y : H2mul (L ≃ₐ[K] L) Lˣ, toBrauer K L y = x := by
  induction x using Quotient.inductionOn with
  | h A =>
  obtain ⟨B, hAB, hdim, ⟨ι⟩⟩ := exists_isBrauerEquivalent_finrank_eq_of_mem_relBrauer A hx
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_algEquiv_crossedProduct ι hdim
  refine ⟨mk _ _ ⟨f, (mem_mulCocycles₂_iff f).2 hf⟩, ?_⟩
  rw [toBrauer_mk]
  exact Quotient.sound ((isBrauerEquivalent_of_algEquiv
    (A := csaOf K (CrossedProduct hf)) (B := B) e).trans hAB.symm)
theorem toRelBrauer_surjective : Function.Surjective (toRelBrauer K L) := fun x => by
  obtain ⟨y, hy⟩ := exists_toBrauer_eq (x : BrauerGroup.{u, u} K) x.2
  exact ⟨y, Subtype.ext hy⟩
theorem toRelBrauer_bijective : Function.Bijective (toRelBrauer K L) :=
  ⟨fun _ _ hxy => toBrauer_injective (congrArg Subtype.val hxy), toRelBrauer_surjective⟩
variable (K L) in

def relBrauerEquiv : H2mul (L ≃ₐ[K] L) Lˣ ≃* BrauerGroup.relBrauer K L :=
  MulEquiv.ofBijective (toRelBrauer K L) toRelBrauer_bijective
end H2mul
end Iso
end GroundTheory.Brauer
end


