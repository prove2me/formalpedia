-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DescEquivLiftEquiv
-- name    : Formalism_LogSumExpBounds_CharacterSumPhase_DescEquivLiftEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:32.400356+00:00
-- url     : https://prove2.me/theorems/3966ca80-00af-4ee4-b691-8bda131c0f51
-- title:
--   Desc Equiv Lift Equiv
-- statement:
--   Definitions and structural lemmas for Desc Equiv Lift Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DescEquivLiftEquiv.lean

import Definitions.Def_Formalism_LogSumExpBounds_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.P
open Matrix Formalism.NuclearRankWeightBounds.C
structure Pres (RR K M A : Type*) [CommRing RR] [CommRing K] [Algebra RR K]
    [AddCommGroup M] [Module RR M] [AddCommGroup A] [Module RR A] where
  π : M →ₗ[RR] A
  g : M →ₗ[RR] K
  ℓ : A →ₗ[RR] KmodR RR K
  p : M
  surj : Function.Surjective π
  ker : ∀ x, π x = 0 ↔ ∃ r : RR, x = r • p
  gp : g p = 1
  hℓ : ∀ x, ℓ (π x) = Submodule.Quotient.mk (g x)
namespace Pres
variable {RR K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]
variable {M₁ M₂ A₁ A₂ : Type*} [AddCommGroup M₁] [Module RR M₁] [AddCommGroup M₂] [Module RR M₂]
  [AddCommGroup A₁] [Module RR A₁] [AddCommGroup A₂] [Module RR A₂]
theorem π_p (P : Pres RR K M₁ A₁) : P.π P.p = 0 := (P.ker _).2 ⟨1, (one_smul _ _).symm⟩
theorem uniq (P : Pres RR K M₁ A₁) (hinj : Function.Injective (algebraMap RR K)) {y y' : M₁}
    (h1 : P.π y = P.π y') (h2 : P.g y = P.g y') : y = y' := by
  have h3 : P.π (y - y') = 0 := by rw [map_sub, h1, sub_self]
  obtain ⟨r, hr⟩ := (P.ker _).1 h3
  have h4 : P.g (y - y') = 0 := by rw [map_sub, h2, sub_self]
  rw [hr, map_smul, P.gp, Algebra.smul_def, mul_one] at h4
  have hr0 : r = 0 := hinj (by rw [h4, map_zero])
  rw [hr0, zero_smul, sub_eq_zero] at hr
  exact hr
theorem exists_lift (P : Pres RR K M₁ A₁) (a : A₁) (k : K)
    (h : P.ℓ a = Submodule.Quotient.mk k) : ∃ y, P.π y = a ∧ P.g y = k := by
  obtain ⟨y₀, rfl⟩ := P.surj a
  rw [P.hℓ, Submodule.Quotient.eq] at h
  obtain ⟨r, hr⟩ := h
  rw [Algebra.linearMap_apply] at hr
  refine ⟨y₀ - r • P.p, ?_, ?_⟩
  · rw [map_sub, map_smul, π_p, smul_zero, sub_zero]
  · rw [map_sub, map_smul, P.gp, Algebra.smul_def, mul_one, hr]; ring
variable (P₁ : Pres RR K M₁ A₁) (P₂ : Pres RR K M₂ A₂)
noncomputable def liftFun (T : A₁ →ₗ[RR] A₂) (hT : ∀ a, P₂.ℓ (T a) = P₁.ℓ a) (x : M₁) : M₂ :=
  Classical.choose (P₂.exists_lift (T (P₁.π x)) (P₁.g x) (by rw [hT, P₁.hℓ]))
theorem liftFun_spec (T : A₁ →ₗ[RR] A₂) (hT : ∀ a, P₂.ℓ (T a) = P₁.ℓ a) (x : M₁) :
    P₂.π (liftFun P₁ P₂ T hT x) = T (P₁.π x) ∧ P₂.g (liftFun P₁ P₂ T hT x) = P₁.g x :=
  Classical.choose_spec (P₂.exists_lift (T (P₁.π x)) (P₁.g x) (by rw [hT, P₁.hℓ]))
noncomputable def liftMap (hinj : Function.Injective (algebraMap RR K)) (T : A₁ →ₗ[RR] A₂)
    (hT : ∀ a, P₂.ℓ (T a) = P₁.ℓ a) : M₁ →ₗ[RR] M₂ where
  toFun := liftFun P₁ P₂ T hT
  map_add' x y := P₂.uniq hinj
    (by rw [map_add, (liftFun_spec P₁ P₂ T hT _).1, (liftFun_spec P₁ P₂ T hT _).1,
      (liftFun_spec P₁ P₂ T hT _).1, map_add, map_add])
    (by rw [map_add, (liftFun_spec P₁ P₂ T hT _).2, (liftFun_spec P₁ P₂ T hT _).2,
      (liftFun_spec P₁ P₂ T hT _).2, map_add])
  map_smul' r x := P₂.uniq hinj
    (by rw [RingHom.id_apply, map_smul, (liftFun_spec P₁ P₂ T hT _).1,
      (liftFun_spec P₁ P₂ T hT _).1, map_smul, map_smul])
    (by rw [RingHom.id_apply, map_smul, (liftFun_spec P₁ P₂ T hT _).2,
      (liftFun_spec P₁ P₂ T hT _).2, map_smul])
theorem liftMap_spec (hinj : Function.Injective (algebraMap RR K)) (T : A₁ →ₗ[RR] A₂)
    (hT : ∀ a, P₂.ℓ (T a) = P₁.ℓ a) (x : M₁) :
    P₂.π (liftMap P₁ P₂ hinj T hT x) = T (P₁.π x) ∧ P₂.g (liftMap P₁ P₂ hinj T hT x) = P₁.g x :=
  liftFun_spec P₁ P₂ T hT x
theorem descend_wd (S : M₁ →ₗ[RR] M₂) (hS : S P₁.p = P₂.p) {x x' : M₁}
    (h : P₁.π x = P₁.π x') : P₂.π (S x) = P₂.π (S x') := by
  have h3 : P₁.π (x - x') = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨r, hr⟩ := (P₁.ker _).1 h3
  have h4 : P₂.π (S (x - x')) = 0 := by
    rw [hr, map_smul, hS]; exact (P₂.ker _).2 ⟨r, rfl⟩
  rwa [map_sub, map_sub, sub_eq_zero] at h4
noncomputable def descMap (S : M₁ →ₗ[RR] M₂) (hS : S P₁.p = P₂.p) : A₁ →ₗ[RR] A₂ where
  toFun a := P₂.π (S (Function.surjInv P₁.surj a))
  map_add' a b := by
    rw [← map_add P₂.π, ← map_add S]
    exact descend_wd P₁ P₂ S hS (by
      rw [map_add, Function.surjInv_eq P₁.surj, Function.surjInv_eq P₁.surj,
        Function.surjInv_eq P₁.surj])
  map_smul' r a := by
    rw [RingHom.id_apply, ← map_smul P₂.π, ← map_smul S]
    exact descend_wd P₁ P₂ S hS (by
      rw [map_smul, Function.surjInv_eq P₁.surj, Function.surjInv_eq P₁.surj])
theorem descMap_π (S : M₁ →ₗ[RR] M₂) (hS : S P₁.p = P₂.p) (x : M₁) :
    descMap P₁ P₂ S hS (P₁.π x) = P₂.π (S x) :=
  descend_wd P₁ P₂ S hS (Function.surjInv_eq P₁.surj _)
noncomputable def liftEquiv (hinj : Function.Injective (algebraMap RR K)) (θ : A₁ ≃ₗ[RR] A₂)
    (hθ : P₂.ℓ.comp θ.toLinearMap = P₁.ℓ) : M₁ ≃ₗ[RR] M₂ :=
  have hT : ∀ a, P₂.ℓ (θ.toLinearMap a) = P₁.ℓ a := fun a => LinearMap.congr_fun hθ a
  have hT' : ∀ a, P₁.ℓ (θ.symm.toLinearMap a) = P₂.ℓ a := fun a => by
    rw [← hT, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (liftMap P₁ P₂ hinj θ.toLinearMap hT)
    (liftMap P₂ P₁ hinj θ.symm.toLinearMap hT')
    (LinearMap.ext fun y => P₂.uniq hinj
      (by
        rw [LinearMap.comp_apply, LinearMap.id_apply, (liftMap_spec _ _ _ _ _ _).1,
          (liftMap_spec _ _ _ _ _ _).1]
        simp)
      (by
        rw [LinearMap.comp_apply, LinearMap.id_apply, (liftMap_spec _ _ _ _ _ _).2,
          (liftMap_spec _ _ _ _ _ _).2]))
    (LinearMap.ext fun y => P₁.uniq hinj
      (by
        rw [LinearMap.comp_apply, LinearMap.id_apply, (liftMap_spec _ _ _ _ _ _).1,
          (liftMap_spec _ _ _ _ _ _).1]
        simp)
      (by
        rw [LinearMap.comp_apply, LinearMap.id_apply, (liftMap_spec _ _ _ _ _ _).2,
          (liftMap_spec _ _ _ _ _ _).2]))
theorem liftEquiv_spec (hinj : Function.Injective (algebraMap RR K)) (θ : A₁ ≃ₗ[RR] A₂)
    (hθ : P₂.ℓ.comp θ.toLinearMap = P₁.ℓ) (x : M₁) :
    P₂.π (liftEquiv P₁ P₂ hinj θ hθ x) = θ (P₁.π x) ∧
      P₂.g (liftEquiv P₁ P₂ hinj θ hθ x) = P₁.g x :=
  liftMap_spec P₁ P₂ hinj θ.toLinearMap _ x
noncomputable def descEquiv (φ : M₁ ≃ₗ[RR] M₂) (hφ : φ P₁.p = P₂.p) : A₁ ≃ₗ[RR] A₂ :=
  have hφ' : φ.symm.toLinearMap P₂.p = P₁.p := by
    rw [LinearEquiv.coe_coe, ← hφ, LinearEquiv.symm_apply_apply]
  LinearEquiv.ofLinearMap (descMap P₁ P₂ φ.toLinearMap hφ) (descMap P₂ P₁ φ.symm.toLinearMap hφ')
    (LinearMap.ext fun a => by
      obtain ⟨y, rfl⟩ := P₂.surj a
      rw [LinearMap.comp_apply, LinearMap.id_apply, descMap_π, descMap_π]
      simp)
    (LinearMap.ext fun a => by
      obtain ⟨y, rfl⟩ := P₁.surj a
      rw [LinearMap.comp_apply, LinearMap.id_apply, descMap_π, descMap_π]
      simp)
theorem descEquiv_π (φ : M₁ ≃ₗ[RR] M₂) (hφ : φ P₁.p = P₂.p) (x : M₁) :
    descEquiv P₁ P₂ φ hφ (P₁.π x) = P₂.π (φ x) :=
  descMap_π P₁ P₂ φ.toLinearMap hφ x
theorem descEquiv_ℓ (φ : M₁ ≃ₗ[RR] M₂) (hφ : φ P₁.p = P₂.p)
    (hg : P₂.g.comp φ.toLinearMap = P₁.g) :
    P₂.ℓ.comp (descEquiv P₁ P₂ φ hφ).toLinearMap = P₁.ℓ :=
  LinearMap.ext fun a => by
    obtain ⟨x, rfl⟩ := P₁.surj a
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, descEquiv_π, P₂.hℓ, P₁.hℓ,
      ← LinearMap.congr_fun hg x]
    rfl
theorem liftEquiv_descEquiv (hinj : Function.Injective (algebraMap RR K)) (φ : M₁ ≃ₗ[RR] M₂)
    (hφ : φ P₁.p = P₂.p) (hθ : P₂.ℓ.comp (descEquiv P₁ P₂ φ hφ).toLinearMap = P₁.ℓ)
    (hg : P₂.g.comp φ.toLinearMap = P₁.g) :
    liftEquiv P₁ P₂ hinj (descEquiv P₁ P₂ φ hφ) hθ = φ :=
  LinearEquiv.ext fun x => P₂.uniq hinj
    ((liftEquiv_spec P₁ P₂ hinj _ hθ x).1.trans (descEquiv_π P₁ P₂ φ hφ x))
    ((liftEquiv_spec P₁ P₂ hinj _ hθ x).2.trans (LinearMap.congr_fun hg x).symm)
theorem descEquiv_liftEquiv (hinj : Function.Injective (algebraMap RR K)) (θ : A₁ ≃ₗ[RR] A₂)
    (hθ : P₂.ℓ.comp θ.toLinearMap = P₁.ℓ) (hφ : liftEquiv P₁ P₂ hinj θ hθ P₁.p = P₂.p) :
    descEquiv P₁ P₂ (liftEquiv P₁ P₂ hinj θ hθ) hφ = θ :=
  LinearEquiv.ext fun a => by
    obtain ⟨x, rfl⟩ := P₁.surj a
    exact (descEquiv_π P₁ P₂ _ hφ x).trans (liftEquiv_spec P₁ P₂ hinj θ hθ x).1
noncomputable def isoEquiv (hinj : Function.Injective (algebraMap RR K)) (q₁ : M₁) (q₂ : M₂)
    (hq : P₁.g q₁ = P₂.g q₂) :
    {θ : A₁ ≃ₗ[RR] A₂ // θ (P₁.π q₁) = P₂.π q₂ ∧ P₂.ℓ.comp θ.toLinearMap = P₁.ℓ} ≃
      {φ : M₁ ≃ₗ[RR] M₂ // P₂.g.comp φ.toLinearMap = P₁.g ∧ φ P₁.p = P₂.p ∧ φ q₁ = q₂} where
  toFun θ := ⟨liftEquiv P₁ P₂ hinj θ.1 θ.2.2,
    LinearMap.ext fun x => (liftEquiv_spec P₁ P₂ hinj θ.1 θ.2.2 x).2,
    P₂.uniq hinj (by rw [(liftEquiv_spec P₁ P₂ hinj θ.1 θ.2.2 _).1, π_p, map_zero, π_p])
      (by rw [(liftEquiv_spec P₁ P₂ hinj θ.1 θ.2.2 _).2, P₁.gp, P₂.gp]),
    P₂.uniq hinj (by rw [(liftEquiv_spec P₁ P₂ hinj θ.1 θ.2.2 _).1, θ.2.1])
      (by rw [(liftEquiv_spec P₁ P₂ hinj θ.1 θ.2.2 _).2, hq])⟩
  invFun φ := ⟨descEquiv P₁ P₂ φ.1 φ.2.2.1, by rw [descEquiv_π, φ.2.2.2],
    descEquiv_ℓ P₁ P₂ φ.1 φ.2.2.1 φ.2.1⟩
  left_inv θ := Subtype.ext (descEquiv_liftEquiv P₁ P₂ hinj θ.1 θ.2.2 _)
  right_inv φ := Subtype.ext (liftEquiv_descEquiv P₁ P₂ hinj φ.1 φ.2.2.1
    (descEquiv_ℓ P₁ P₂ φ.1 φ.2.2.1 φ.2.1) φ.2.1)
end Pres
section Conc
variable {RR K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]
def vk {k : ℕ} (v : Fin k → RR) : Fin k → K := fun j => algebraMap RR K (v j)
theorem vk_add {k : ℕ} (v w : Fin k → RR) : vk (K := K) (v + w) = vk v + vk w :=
  funext fun j => map_add (algebraMap RR K) (v j) (w j)
theorem vk_smul {k : ℕ} (r : RR) (v : Fin k → RR) :
    vk (K := K) (r • v) = algebraMap RR K r • vk v :=
  funext fun j => map_mul (algebraMap RR K) r (v j)
theorem vk_mulVec {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (y : Fin k → RR) :
    vk (K := K) (Z *ᵥ y) = toK K Z *ᵥ vk y :=
  funext fun i => RingHom.map_mulVec (algebraMap RR K) Z y i
theorem mulVec_castSucc {α : Type*} [CommRing α] {m : ℕ} (W : Matrix (Fin (m+1)) (Fin (m+1)) α)
    (y : Fin (m+1) → α) (i : Fin m) :
    (W *ᵥ y) (Fin.castSucc i) = (W.submatrix Fin.castSucc Fin.castSucc *ᵥ
      (fun j => y (Fin.castSucc j))) i + W (Fin.castSucc i) (Fin.last m) * y (Fin.last m) := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc]
theorem mulVec_last {α : Type*} [CommRing α] {m : ℕ} (W : Matrix (Fin (m+1)) (Fin (m+1)) α)
    (y : Fin (m+1) → α) :
    (W *ᵥ y) (Fin.last m) = (fun j => W (Fin.last m) (Fin.castSucc j)) ⬝ᵥ
      (fun j => y (Fin.castSucc j)) + W (Fin.last m) (Fin.last m) * y (Fin.last m) := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc]
theorem key {α : Type*} [CommRing α] {m : ℕ} (W : Matrix (Fin (m+1)) (Fin (m+1)) α)
    (hW : IsUnit (W.submatrix Fin.castSucc Fin.castSucc).det) (y : Fin (m+1) → α) :
    (W *ᵥ y) (Fin.last m) - (fun j => W (Fin.last m) (Fin.castSucc j)) ⬝ᵥ
        ((W.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ (fun i => (W *ᵥ y) (Fin.castSucc i))) =
      (W (Fin.last m) (Fin.last m) - ∑ i, ∑ j, W (Fin.last m) (Fin.castSucc i) *
        (W.submatrix Fin.castSucc Fin.castSucc)⁻¹ i j * W (Fin.castSucc j) (Fin.last m)) *
        y (Fin.last m) := by
  set W' := W.submatrix Fin.castSucc Fin.castSucc
  set a : Fin m → α := fun j => W (Fin.last m) (Fin.castSucc j)
  set b : Fin m → α := fun j => W (Fin.castSucc j) (Fin.last m)
  set y' : Fin m → α := fun j => y (Fin.castSucc j)
  have h1 : (fun i => (W *ᵥ y) (Fin.castSucc i)) = W' *ᵥ y' + y (Fin.last m) • b := by
    funext i; rw [mulVec_castSucc]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, b, mul_comm]; rfl
  have h2 : W'⁻¹ *ᵥ (W' *ᵥ y' + y (Fin.last m) • b) = y' + y (Fin.last m) • (W'⁻¹ *ᵥ b) := by
    rw [mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hW, one_mulVec, mulVec_smul]
  have h3 : ∑ i, ∑ j, W (Fin.last m) (Fin.castSucc i) * W'⁻¹ i j * W (Fin.castSucc j) (Fin.last m)
      = a ⬝ᵥ (W'⁻¹ *ᵥ b) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, a, b]
  rw [h1, h2, mulVec_last, h3, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring
variable {m : ℕ}
noncomputable def fV (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : (Fin (m+1) → RR) →ₗ[RR] K where
  toFun v := ((toK K Z)⁻¹ *ᵥ vk v) (Fin.last m)
  map_add' v w := by rw [vk_add, mulVec_add]; rfl
  map_smul' r v := by
    rw [vk_smul, mulVec_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Algebra.smul_def]
theorem fV_apply (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (v : Fin (m+1) → RR) :
    fV (K := K) Z v = ((toK K Z)⁻¹ *ᵥ vk v) (Fin.last m) := rfl
theorem fV_mulVec (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (y : Fin (m+1) → RR) : fV (K := K) Z (Z *ᵥ y) = algebraMap RR K (y (Fin.last m)) := by
  rw [fV_apply, vk_mulVec, mulVec_mulVec, nonsing_inv_mul _ hZ, one_mulVec]; rfl
theorem vk_single {k : ℕ} (i : Fin k) :
    vk (K := K) (Pi.single i (1 : RR)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [vk]
  · simp [vk, h]
theorem fV_single (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) :
    fV (K := K) Z (Pi.single (Fin.last m) 1) = kappa K Z := by
  rw [fV_apply, vk_single, mulVec_single_one]; rfl
theorem rowInvMod_apply {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) (v : Fin k → RR) :
    rowInvMod K Z r v = Submodule.Quotient.mk (r ⬝ᵥ ((toK K Z)⁻¹ *ᵥ vk v)) := by
  simp only [rowInvMod, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.mkQ_apply, dotProduct, mulVec, Finset.mul_sum, mul_assoc, vk]
theorem mem_range_alg (x : RR) :
    algebraMap RR K x ∈ LinearMap.range (Algebra.linearMap RR K) := ⟨x, rfl⟩
theorem lam_mk (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (v : Fin (m+1) → RR) : lam K Z (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fV Z v) := by
  have hle : LinearMap.range Z.mulVecLin ≤
      LinearMap.ker (rowInvMod K Z (Pi.single (Fin.last m) 1)) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, rowInvMod_apply, single_dotProduct, one_mul,
      ← fV_apply, fV_mulVec Z hZ, Submodule.Quotient.mk_eq_zero]
    exact mem_range_alg _
  unfold lam descend
  rw [dif_pos hle, Submodule.liftQ_apply, rowInvMod_apply, single_dotProduct, one_mul]
  rfl
def aK (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : Fin m → K :=
  fun j => algebraMap RR K (Z (Fin.last m) (Fin.castSucc j))
theorem alpha_mk (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K (blk Z)).det)
    (v : Fin m → RR) : alpha K Z (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (aK Z ⬝ᵥ ((toK K (blk Z))⁻¹ *ᵥ vk v)) := by
  have hle : LinearMap.range (blk Z).mulVecLin ≤ LinearMap.ker (rowInvMod K (blk Z) (aK Z)) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, rowInvMod_apply, vk_mulVec, mulVec_mulVec,
      nonsing_inv_mul _ hZ, one_mulVec, Submodule.Quotient.mk_eq_zero]
    refine ⟨(fun j => Z (Fin.last m) (Fin.castSucc j)) ⬝ᵥ y, ?_⟩
    rw [Algebra.linearMap_apply, RingHom.map_dotProduct]; rfl
  unfold alpha descend
  split_ifs with h
  · rw [Submodule.liftQ_apply, rowInvMod_apply]; rfl
  · exact absurd hle h
def eN : Fin (m+1) → RR := Pi.single (Fin.last m) 1
theorem key_cval (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (hZ' : IsUnit (toK K (blk Z)).det) (v : Fin (m+1) → RR) :
    algebraMap RR K (v (Fin.last m)) - aK Z ⬝ᵥ ((toK K (blk Z))⁻¹ *ᵥ vk (fun i => v (Fin.castSucc i)))
      = cval K Z * fV Z v := by
  have h := key (toK K Z) hZ' ((toK K Z)⁻¹ *ᵥ vk v)
  rw [mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec] at h
  exact h
theorem cval_mul_kappa (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (hZ' : IsUnit (toK K (blk Z)).det) : cval K Z * kappa K Z = 1 := by
  have h := key_cval Z hZ hZ' eN
  have h0 : (fun i : Fin m => (eN : Fin (m+1) → RR) (Fin.castSucc i)) = 0 := by
    funext i; simp [eN, Fin.castSucc_ne_last]
  rw [h0, show fV (K := K) Z eN = kappa K Z from fV_single Z] at h
  have hv : vk (K := K) (0 : Fin m → RR) = 0 := funext fun _ => map_zero _
  rw [← h, hv, mulVec_zero, dotProduct_zero, sub_zero]
  simp [eN]
def Nsub (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : Submodule RR (Fin (m+1) → RR) :=
  (LinearMap.ker (LinearMap.proj (R := RR) (φ := fun _ : Fin (m+1) => RR) (Fin.last m))).map
    Z.mulVecLin
theorem mem_Nsub {Z : Matrix (Fin (m+1)) (Fin (m+1)) RR} {x : Fin (m+1) → RR} :
    x ∈ Nsub Z ↔ ∃ y : Fin (m+1) → RR, y (Fin.last m) = 0 ∧ Z *ᵥ y = x := by
  simp [Nsub]
abbrev MM (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : Type _ := (Fin (m+1) → RR) ⧸ Nsub Z
theorem Nsub_le_range (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) :
    Nsub Z ≤ LinearMap.ker (LinearMap.range Z.mulVecLin).mkQ := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := mem_Nsub.1 hx
  rw [Submodule.ker_mkQ]
  exact ⟨y, rfl⟩
theorem Nsub_le_fV (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det) :
    Nsub Z ≤ LinearMap.ker (fV (K := K) Z) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_Nsub.1 hx
  rw [LinearMap.mem_ker, fV_mulVec Z hZ, hy, map_zero]
noncomputable def πA (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : MM Z →ₗ[RR] coker Z :=
  (Nsub Z).liftQ _ (Nsub_le_range Z)
noncomputable def gA (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det) :
    MM Z →ₗ[RR] K :=
  (Nsub Z).liftQ _ (Nsub_le_fV Z hZ)
noncomputable def PA (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det) :
    Pres RR K (MM Z) (coker Z) where
  π := πA Z
  g := gA Z hZ
  ℓ := lam K Z
  p := Submodule.Quotient.mk (Z *ᵥ eN)
  surj := by
    intro a
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  ker := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.Quotient.mk v : coker Z) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y (Fin.last m), ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, mem_Nsub]
      refine ⟨y - y (Fin.last m) • eN, by simp [eN], ?_⟩
      rw [mulVec_sub, mulVec_smul]; rfl
    · rintro ⟨r, hr⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hr
      have h1 := Nsub_le_range Z hr
      rw [Submodule.ker_mkQ] at h1
      have h2 : r • (Z *ᵥ eN) ∈ LinearMap.range Z.mulVecLin :=
        ⟨r • eN, by rw [mulVecLin_apply, mulVec_smul]⟩
      simpa using add_mem h1 h2
  gp := by
    change fV Z (Z *ᵥ eN) = 1
    rw [fV_mulVec Z hZ]; simp [eN]
  hℓ := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact lam_mk Z hZ v
def Pcs : (Fin (m+1) → RR) →ₗ[RR] (Fin m → RR) := LinearMap.funLeft RR RR Fin.castSucc
theorem Nsub_le_B (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) :
    Nsub Z ≤ LinearMap.ker ((LinearMap.range (blk Z).mulVecLin).mkQ ∘ₗ Pcs) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_Nsub.1 hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨fun j => y (Fin.castSucc j), ?_⟩
  funext i
  rw [mulVecLin_apply, Pcs, LinearMap.funLeft_apply, mulVec_castSucc, hy, mul_zero, add_zero]
  rfl
noncomputable def πB (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : MM Z →ₗ[RR] coker (blk Z) :=
  (Nsub Z).liftQ _ (Nsub_le_B Z)
noncomputable def PB (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) (hZ : IsUnit (toK K Z).det)
    (hZ' : IsUnit (toK K (blk Z)).det) : Pres RR K (MM Z) (coker (blk Z)) where
  π := πB Z
  g := (LinearMap.mulLeft RR (-(cval K Z))).comp (gA Z hZ)
  ℓ := alpha K Z
  p := Submodule.Quotient.mk (-eN)
  surj := by
    intro a
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨w, hw⟩ := LinearMap.funLeft_surjective_of_injective RR RR Fin.castSucc
      (Fin.castSucc_injective m) v
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    change (Submodule.Quotient.mk (Pcs w) : coker (blk Z)) = _
    rw [Pcs, hw]
  ker := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (Submodule.Quotient.mk (Pcs v) : coker (blk Z)) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y', hy'⟩
      rw [mulVecLin_apply] at hy'
      let y : Fin (m+1) → RR := Fin.snoc y' 0
      refine ⟨-(v (Fin.last m) - (Z *ᵥ y) (Fin.last m)), ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, mem_Nsub]
      refine ⟨y, by simp [y], ?_⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [eN]
      · have hj := congrFun hy' j
        rw [Pcs, LinearMap.funLeft_apply] at hj
        rw [mulVec_castSucc]
        simp [y, eN, Fin.castSucc_ne_last]
        exact hj
    · rintro ⟨r, hr⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hr
      have h1 := Nsub_le_B Z hr
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_sub] at h1
      have h2 : Pcs (r • -(eN : Fin (m+1) → RR)) = 0 := by
        funext j; simp [Pcs, eN, Fin.castSucc_ne_last]
      rwa [h2, sub_zero] at h1
  gp := by
    change -(cval K Z) * fV Z (-eN) = 1
    rw [map_neg, eN, fV_single, neg_mul_neg, cval_mul_kappa Z hZ hZ']
  hℓ := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change alpha K Z (Submodule.Quotient.mk (Pcs v)) =
      Submodule.Quotient.mk (-(cval K Z) * fV Z v)
    rw [alpha_mk Z hZ', Submodule.Quotient.eq]
    refine ⟨v (Fin.last m), ?_⟩
    rw [Algebra.linearMap_apply]
    have h := key_cval Z hZ hZ' v
    change algebraMap RR K (v (Fin.last m)) - aK Z ⬝ᵥ ((toK K (blk Z))⁻¹ *ᵥ vk (Pcs v))
      = cval K Z * fV Z v at h
    linear_combination h
noncomputable def midEquiv {m₁ m₂ : ℕ} (Z₁ : Matrix (Fin (m₁+1)) (Fin (m₁+1)) RR)
    (Z₂ : Matrix (Fin (m₂+1)) (Fin (m₂+1)) RR) (h1 : IsUnit (toK K Z₁).det)
    (h2 : IsUnit (toK K Z₂).det) (h1' : IsUnit (toK K (blk Z₁)).det)
    (h2' : IsUnit (toK K (blk Z₂)).det) (hc : cval K Z₁ = cval K Z₂) :
    {φ : MM Z₁ ≃ₗ[RR] MM Z₂ // (PA Z₂ h2).g.comp φ.toLinearMap = (PA Z₁ h1).g ∧
        φ (PA Z₁ h1).p = (PA Z₂ h2).p ∧
        φ (Submodule.Quotient.mk eN) = Submodule.Quotient.mk eN} ≃
      {φ : MM Z₁ ≃ₗ[RR] MM Z₂ // (PB Z₂ h2 h2').g.comp φ.toLinearMap = (PB Z₁ h1 h1').g ∧
        φ (PB Z₁ h1 h1').p = (PB Z₂ h2 h2').p ∧
        φ (Submodule.Quotient.mk (Z₁ *ᵥ eN)) = Submodule.Quotient.mk (Z₂ *ᵥ eN)} :=
  Equiv.subtypeEquivRight fun φ => by
    have hu : cval K Z₁ * kappa K Z₁ = 1 := cval_mul_kappa Z₁ h1 h1'
    constructor
    · rintro ⟨hg, hp, hq⟩
      refine ⟨LinearMap.ext fun x => ?_, ?_, hp⟩
      · have h := LinearMap.congr_fun hg x
        change gA Z₂ h2 (φ x) = gA Z₁ h1 x at h
        change -(cval K Z₂) * gA Z₂ h2 (φ x) = -(cval K Z₁) * gA Z₁ h1 x
        rw [h, hc]
      · change φ (Submodule.Quotient.mk (-eN)) = Submodule.Quotient.mk (-eN)
        rw [Submodule.Quotient.mk_neg, map_neg, hq, Submodule.Quotient.mk_neg]
    · rintro ⟨hg, hp, hq⟩
      refine ⟨LinearMap.ext fun x => ?_, hq, ?_⟩
      · have h := LinearMap.congr_fun hg x
        change -(cval K Z₂) * gA Z₂ h2 (φ x) = -(cval K Z₁) * gA Z₁ h1 x at h
        change gA Z₂ h2 (φ x) = gA Z₁ h1 x
        rw [← hc] at h
        linear_combination (-(kappa K Z₁)) * h - (gA Z₂ h2 (φ x) - gA Z₁ h1 x) * hu
      · change φ (Submodule.Quotient.mk (-eN)) = Submodule.Quotient.mk (-eN) at hp
        rw [Submodule.Quotient.mk_neg, map_neg, Submodule.Quotient.mk_neg, neg_inj] at hp
        exact hp
end Conc
end Formalism.NuclearRankWeightBounds.P


