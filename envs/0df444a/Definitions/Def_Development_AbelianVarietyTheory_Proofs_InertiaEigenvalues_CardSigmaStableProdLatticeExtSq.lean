-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:49.991805+00:00
-- url     : https://prove2.me/theorems/51c3b1b3-0601-4a88-810f-9ee5e2904922
-- title:
--   Card Sigma Stable Prod Lattice Ext Sq
-- statement:
--   Definitions and structural lemmas for Card Sigma Stable Prod Lattice Ext Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
namespace GlobalTheory.SigmaExtCount
section
variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (τ : Q →+ Q)
    (hττ : ∀ f : Q, τ (τ f) = f) (θ θ' u : R) (hθ : ∀ f : Q, τ (θ • f) = θ' • τ f)
    (hu : ∀ f : Q, τ (u • f) = -(u • τ f)) (hinv : ∀ f : Q, u • ((θ - θ') • f) = f)
include hττ hθ hu hinv
theorem half_snd (f : Q) : τ (u • (f - τ f)) = u • (f - τ f) := by
  rw [hu, map_sub, hττ, ← smul_neg, neg_sub]
theorem half_fst (f : Q) : τ (f - θ • (u • (f - τ f))) = f - θ • (u • (f - τ f)) := by
  have h2 : (θ - θ') • (u • (f - τ f)) = f - τ f := by rw [smul_comm, hinv]
  rw [map_sub, hθ, half_snd τ hττ θ θ' u hθ hu hinv f]
  rw [sub_smul] at h2
  generalize u • (f - τ f) = b at h2 ⊢
  rw [← sub_eq_zero]
  have : τ f - θ' • b - (f - θ • b) = (θ • b - θ' • b) - (f - τ f) := by abel
  rw [this, h2, sub_self]
theorem half_left (a b : Q) (ha : τ a = a) (hb : τ b = b) :
    u • ((a + θ • b) - τ (a + θ • b)) = b := by
  rw [map_add, hθ, ha, hb]
  have : a + θ • b - (a + θ' • b) = (θ - θ') • b := by rw [sub_smul]; abel
  rw [this, hinv]
def halfEquiv : {f : Q // τ f = f} × {f : Q // τ f = f} ≃ Q where
  toFun p := p.1.1 + θ • p.2.1
  invFun f := (⟨f - θ • (u • (f - τ f)), half_fst τ hττ θ θ' u hθ hu hinv f⟩,
    ⟨u • (f - τ f), half_snd τ hττ θ θ' u hθ hu hinv f⟩)
  left_inv p := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
    have h := half_left τ hττ θ θ' u hθ hu hinv a b ha hb
    ext <;> simp only [h] <;> abel
  right_inv f := by simp
end
section Torsor
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁] [AddCommGroup A₂]
  [Module O A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂)
def Ext (M : Submodule O (A₁ × A₂)) : Prop :=
  M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂
variable {M₁ M₂}
theorem Ext.exists {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (b : M₂) : ∃ x, (x, (b : A₂)) ∈ M := by
  obtain ⟨b, hb⟩ := b
  rw [← hM.2, Submodule.mem_map] at hb
  obtain ⟨y, hy, e⟩ := hb
  exact ⟨y.1, by simpa [← e] using hy⟩
theorem Ext.sub_mem {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x x' : A₁} {b : A₂}
    (h : (x, b) ∈ M) (h' : (x', b) ∈ M) : x - x' ∈ M₁ := by
  rw [← hM.1, Submodule.mem_comap]
  have := M.sub_mem h h'
  simpa using this
def Ext.fn {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (b : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (Classical.choose (hM.exists b))
theorem Ext.fn_eq {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x : A₁} (b : M₂)
    (h : (x, (b : A₂)) ∈ M) : hM.fn b = Submodule.Quotient.mk x := by
  unfold Ext.fn
  rw [Submodule.Quotient.eq]
  exact hM.sub_mem (Classical.choose_spec (hM.exists b)) h
def Ext.lin {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := hM.fn
  map_add' b b' := by
    obtain ⟨x, hx⟩ := hM.exists b
    obtain ⟨x', hx'⟩ := hM.exists b'
    rw [hM.fn_eq b hx, hM.fn_eq b' hx', hM.fn_eq (b + b') (x := x + x') (by simpa using M.add_mem hx hx')]
    simp
  map_smul' o b := by
    obtain ⟨x, hx⟩ := hM.exists b
    rw [hM.fn_eq b hx, hM.fn_eq (o • b) (x := o • x) (by simpa using M.smul_mem o hx)]
    simp
theorem Ext.lin_eq {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x : A₁} (b : M₂)
    (h : (x, (b : A₂)) ∈ M) : hM.lin b = Submodule.Quotient.mk x := hM.fn_eq b h
theorem Ext.mem_iff {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (y : A₁ × A₂) :
    y ∈ M ↔ ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = hM.lin ⟨y.2, h⟩ := by
  constructor
  · intro hy
    have h2 : y.2 ∈ M₂ := by rw [← hM.2]; exact ⟨y, hy, rfl⟩
    exact ⟨h2, (hM.lin_eq ⟨y.2, h2⟩ hy).symm⟩
  · rintro ⟨h2, e⟩
    obtain ⟨x, hx⟩ := hM.exists ⟨y.2, h2⟩
    rw [hM.lin_eq _ hx, Submodule.Quotient.eq] at e
    have h0 : (y.1 - x, (0 : A₂)) ∈ M := by
      have : LinearMap.inl O A₁ A₂ (y.1 - x) ∈ M := by
        rw [← Submodule.mem_comap, hM.1]; exact e
      simpa using this
    have := M.add_mem hx h0
    simpa using this
def graphSub (f : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {y | ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = f ⟨y.2, h⟩}
  add_mem' := by
    rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
    refine ⟨M₂.add_mem ha hb, ?_⟩
    show _ = f (⟨a.2, ha⟩ + ⟨b.2, hb⟩)
    rw [map_add, ← ea, ← eb]; simp
  zero_mem' := ⟨M₂.zero_mem, by
    show _ = f 0
    simp⟩
  smul_mem' := by
    rintro o a ⟨ha, ea⟩
    refine ⟨M₂.smul_mem o ha, ?_⟩
    show _ = f (o • ⟨a.2, ha⟩)
    rw [map_smul, ← ea]; simp
theorem mem_graphSub (f : M₂ →ₗ[O] A₁ ⧸ M₁) (y : A₁ × A₂) :
    y ∈ graphSub f ↔ ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = f ⟨y.2, h⟩ := Iff.rfl
theorem graphSub_ext (f : M₂ →ₗ[O] A₁ ⧸ M₁) : Ext M₁ M₂ (graphSub f) := by
  constructor
  · ext x
    simp only [Submodule.mem_comap, LinearMap.inl_apply, mem_graphSub]
    constructor
    · rintro ⟨h, e⟩
      have : f ⟨0, h⟩ = 0 := by
        have : (⟨0, h⟩ : M₂) = 0 := rfl
        rw [this, map_zero]
      rw [this, Submodule.Quotient.mk_eq_zero] at e; exact e
    · intro hx
      refine ⟨M₂.zero_mem, ?_⟩
      rw [(Submodule.Quotient.mk_eq_zero M₁).2 hx]
      have : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [this, map_zero]
  · ext b
    simp only [Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨y, ⟨h, _⟩, rfl⟩; exact h
    · intro hb
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f ⟨b, hb⟩)
      exact ⟨(x, b), ⟨hb, hx⟩, rfl⟩
def extEquiv : {M : Submodule O (A₁ × A₂) // Ext M₁ M₂ M} ≃ (M₂ →ₗ[O] A₁ ⧸ M₁) where
  toFun M := M.2.lin
  invFun f := ⟨graphSub f, graphSub_ext f⟩
  left_inv M := by
    apply Subtype.ext
    ext y
    rw [mem_graphSub, M.2.mem_iff]
  right_inv f := by
    ext b
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f b)
    have hm : (x, (b : A₂)) ∈ graphSub f := ⟨b.2, hx⟩
    exact ((graphSub_ext f).lin_eq b hm).trans hx
end Torsor
section Twist
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}
def compat (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) :
    Submodule O (M₂ →ₗ[O] A₁ ⧸ M₁) where
  carrier := {f | ∀ b : M₂, f ⟨g₂ b, hg₂ b.2⟩ = M₁.mapQ M₁ g₁ hg₁ (f b)}
  add_mem' := by
    intro f f' hf hf' b
    simp only [LinearMap.add_apply, hf b, hf' b, map_add]
  zero_mem' := by intro b; simp
  smul_mem' := by
    intro o f hf b
    simp only [LinearMap.smul_apply, hf b, map_smul]
variable (hcc : ∀ o, cO (cO o) = o) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
  (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)
def twist (f : M₂ →ₗ[O] A₁ ⧸ M₁) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun b := M₁.mapQ M₁ σ₁ hs₁ (f ⟨σ₂ b, hs₂ b.2⟩)
  map_add' b b' := by
    have : (⟨σ₂ (b + b' : M₂), hs₂ (b + b').2⟩ : M₂) = ⟨σ₂ b, hs₂ b.2⟩ + ⟨σ₂ b', hs₂ b'.2⟩ :=
      Subtype.ext (by simp)
    rw [this, map_add, map_add]
  map_smul' o b := by
    have : (⟨σ₂ (o • b : M₂), hs₂ (o • b).2⟩ : M₂) = cO o • ⟨σ₂ b, hs₂ b.2⟩ :=
      Subtype.ext (by simp)
    rw [this, map_smul, LinearMap.map_smulₛₗ, hcc]
    rfl
theorem twist_apply (f : M₂ →ₗ[O] A₁ ⧸ M₁) (b : M₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f b = M₁.mapQ M₁ σ₁ hs₁ (f ⟨σ₂ b, hs₂ b.2⟩) := rfl
def twistHom : (M₂ →ₗ[O] A₁ ⧸ M₁) →+ (M₂ →ₗ[O] A₁ ⧸ M₁) where
  toFun := twist hcc σ₁ σ₂ hs₁ hs₂
  map_zero' := by ext b; simp [twist_apply]
  map_add' f f' := by ext b; simp [twist_apply]
end Twist
section Count
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}
end Count
section Special
open GlobalTheory.UnitLemma
def conjFun (K : UQ) (o : K.O) : K.O := Classical.choose (K.c_int o)
theorem algebraMap_conjFun (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjFun K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm
def conjO (K : UQ) : K.O →+* K.O where
  toFun := conjFun K
  map_one' := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_one])
  map_mul' a b := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_mul])
  map_zero' := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_zero])
  map_add' a b := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_add])
theorem algebraMap_conjO (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) := algebraMap_conjFun K o
def sigmaSL {K : UQ} (B : InvAlg K) : B.A →ₛₗ[conjO K] B.A where
  toFun := B.σ
  map_add' := map_add B.σ
  map_smul' o a := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply K.O K.E B.A,
      IsScalarTower.algebraMap_apply K.O K.E B.A (conjO K o), B.σ_alg, algebraMap_conjO]
end Special
end GlobalTheory.SigmaExtCount


