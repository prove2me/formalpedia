-- Prove2me | solution 1 for Algebra.TensorProduct.cocycle_trans_symm_of_comparison_identities
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/000016dc-dca1-53af-8516-bdd34bc02b93

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

section K6Helpers

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S']
  {R' : Type u} [CommRing R'] [Algebra S R']
  {R'' : Type u} [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R'']
  [IsScalarTower S (S' ⊗[S] S') R'']
  {R''' : Type u} [CommRing R'''] [Algebra (S' ⊗[S] (S' ⊗[S] S')) R''']
  [Algebra S R'''] [IsScalarTower S (S' ⊗[S] (S' ⊗[S] S')) R''']

namespace K6

variable (S') in

noncomputable def bT (ρ : R' →ₐ[S] R''') (w : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')) :
    (R' ⊗[S] S') →ₐ[S] R''' :=
  Algebra.TensorProduct.lift ρ ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp w) fun _ _ => Commute.all _ _

variable (S') in

noncomputable def bS (w : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')) (ρ : R' →ₐ[S] R''') :
    (S' ⊗[S] R') →ₐ[S] R''' :=
  Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp w) ρ fun _ _ => Commute.all _ _

variable (S') in

noncomputable def outL {B : Type u} [CommRing B] [Algebra S B] (g : B →ₐ[S] R''') :
    (S' ⊗[S] B) →ₐ[S] R''' :=
  Algebra.TensorProduct.lift
    ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp (includeLeft : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')))
    g fun _ _ => Commute.all _ _

variable (S') in

noncomputable def outR {B : Type u} [CommRing B] [Algebra S B] (g : B →ₐ[S] R''')
    (w : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')) : (B ⊗[S] S') →ₐ[S] R''' :=
  Algebra.TensorProduct.lift g ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp w) fun _ _ => Commute.all _ _

lemma bT_tmul (ρ : R' →ₐ[S] R''') (w : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S'))
    (r : R') (t : S') :
    bT S' ρ w (r ⊗ₜ t) = ρ r * (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') (w t) := by
  simp [bT]

lemma bS_tmul (w : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')) (ρ : R' →ₐ[S] R''')
    (s : S') (r : R') :
    bS S' w ρ (s ⊗ₜ r) = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') (w s) * ρ r := by
  simp [bS]

lemma outL_tmul {B : Type u} [CommRing B] [Algebra S B] (g : B →ₐ[S] R''')
    (s : S') (y : B) :
    outL S' g (s ⊗ₜ y) = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') (s ⊗ₜ (1 : S' ⊗[S] S')) * g y := by
  simp [outL]

lemma outR_tmul {B : Type u} [CommRing B] [Algebra S B] (g : B →ₐ[S] R''')
    (w : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')) (y : B) (u : S') :
    outR S' g w (y ⊗ₜ u) = g y * (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') (w u) := by
  simp [outR]

lemma outL_map_assoc (D : (S' ⊗[S] R') →ₐ[S] R''') (ψ : (R' ⊗[S] S') →ₐ[S] S' ⊗[S] R') :
    (outL S' D).comp ((Algebra.TensorProduct.map (AlgHom.id S S') ψ).comp
      (Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom) =
    Algebra.TensorProduct.lift
      (outL S' (D.comp (ψ.comp (includeLeft : R' →ₐ[S] R' ⊗[S] S'))))
      (D.comp (ψ.comp (includeRight : S' →ₐ[S] R' ⊗[S] S')))
      (fun _ _ => Commute.all _ _) := by
  refine AlgHom.toLinearMap_injective (TensorProduct.ext_threefold fun s r u => ?_)
  simp [Algebra.TensorProduct.assoc_tmul, outL_tmul, Algebra.TensorProduct.lift_tmul]
  rw [mul_assoc, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma sig_beta1 (σ : R'' →ₐ[S] R''') (ϑ₁ : R' →ₐ[S] R'') (ρ : R' →ₐ[S] R''')
    (hρ : ∀ x, σ (ϑ₁ x) = ρ x)
    (c : (S' ⊗[S] S') →ₐ[S] S' ⊗[S] (S' ⊗[S] S'))
    (hσ : σ.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp c)
    (β₁ : (R' ⊗[S] S') ≃ₐ[S] R'')
    (hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' ((1:S') ⊗ₜ t))
    (y : R' ⊗[S] S') :
    σ (β₁ y) = bT S' ρ (c.comp (includeRight : S' →ₐ[S] S' ⊗[S] S')) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r t =>
    rw [hβ₁, map_mul, hρ, bT_tmul]
    congr 1
    have h := AlgHom.congr_fun hσ ((1:S') ⊗ₜ t)
    simpa using h
  | add a b ha hb => simp only [map_add, ha, hb]

lemma sig_beta2 (σ : R'' →ₐ[S] R''') (ϑ₂ : R' →ₐ[S] R'') (ρ : R' →ₐ[S] R''')
    (hρ : ∀ x, σ (ϑ₂ x) = ρ x)
    (c : (S' ⊗[S] S') →ₐ[S] S' ⊗[S] (S' ⊗[S] S'))
    (hσ : σ.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp c)
    (β₂ : (S' ⊗[S] R') ≃ₐ[S] R'')
    (hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ (1:S')) * ϑ₂ r)
    (z : S' ⊗[S] R') :
    σ (β₂ z) = bS S' (c.comp (includeLeft : S' →ₐ[S] S' ⊗[S] S')) ρ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s r =>
    rw [hβ₂, map_mul, hρ, bS_tmul]
    congr 1
    have h := AlgHom.congr_fun hσ (s ⊗ₜ (1:S'))
    simpa using h
  | add a b ha hb => simp only [map_add, ha, hb]

end K6

end K6Helpers

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R' : Type u) [CommRing R'] [Algebra S R']
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (R''' : Type u) [CommRing R'''] [Algebra (S' ⊗[S] (S' ⊗[S] S')) R'''] [Algebra S R'''] [IsScalarTower S (S' ⊗[S] (S' ⊗[S] S')) R''']
    (ϑ₁ ϑ₂ : R' →ₐ[S] R'')
    (β₁ : R' ⊗[S] S' ≃ₐ[S] R'')
    (hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] R' ≃ₐ[S] R'')
    (hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₂ r)
    (σ₁₂ σ₁₃ σ₂₃ : R'' →ₐ[S] R''')
    (hσ₁₂ : σ₁₂.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S'))))
    (hσ₁₃ : σ₁₃.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))))
    (hσ₂₃ : σ₂₃.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S'))))
    (hA : ∀ x : R', σ₁₃ (ϑ₁ x) = σ₁₂ (ϑ₁ x)) (hB : ∀ x : R', σ₂₃ (ϑ₁ x) = σ₁₂ (ϑ₂ x))
    (hC : ∀ x : R', σ₂₃ (ϑ₂ x) = σ₁₃ (ϑ₂ x))
    (hbij : Function.Bijective
      (Algebra.TensorProduct.lift (σ₁₂.comp ϑ₁)
        ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
          (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')))
        (fun _ _ => Commute.all _ _) : R' ⊗[S] (S' ⊗[S] S') →ₐ[S] R''')) :
    let φ : R' ⊗[S] S' ≃ₐ[S] S' ⊗[S] R' := β₁.trans β₂.symm
    (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom)))) := by
  intro φ
  have hφ : ∀ y : R' ⊗[S] S', φ y = β₂.symm (β₁ y) := fun _ => rfl
  have h23b1 := K6.sig_beta1 σ₂₃ ϑ₁ (σ₁₂.comp ϑ₂) hB _ hσ₂₃ β₁ hβ₁
  have h23b2 := K6.sig_beta2 σ₂₃ ϑ₂ (σ₁₃.comp ϑ₂) hC _ hσ₂₃ β₂ hβ₂
  have h13b1 := K6.sig_beta1 σ₁₃ ϑ₁ (σ₁₂.comp ϑ₁) hA _ hσ₁₃ β₁ hβ₁
  have h13b2 := K6.sig_beta2 σ₁₃ ϑ₂ (σ₁₃.comp ϑ₂) (fun _ => rfl) _ hσ₁₃ β₂ hβ₂
  have h12b1 := K6.sig_beta1 σ₁₂ ϑ₁ (σ₁₂.comp ϑ₁) (fun _ => rfl) _ hσ₁₂ β₁ hβ₁
  have h12b2 := K6.sig_beta2 σ₁₂ ϑ₂ (σ₁₂.comp ϑ₂) (fun _ => rfl) _ hσ₁₂ β₂ hβ₂
  have hβφ : ∀ y : R' ⊗[S] S', β₂ (φ.toAlgHom y) = β₁ y := fun y => by
    show β₂ (φ y) = β₁ y
    rw [hφ y, AlgEquiv.apply_symm_apply]
  have hβφ' : ∀ y : R' ⊗[S] S', β₂ (φ y) = β₁ y := fun y => by
    rw [hφ y, AlgEquiv.apply_symm_apply]
  have hL : ∀ (r : R') (t u : S'),
      K6.outL S' (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂))
        (((Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
          ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
            (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')))) ((r ⊗ₜ t) ⊗ₜ u)) =
      σ₁₂ (ϑ₁ r) *
        (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') ((1:S') ⊗ₜ (t ⊗ₜ u)) := by
    intro r t u
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hpipe := AlgHom.congr_fun (K6.outL_map_assoc (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)) φ.toAlgHom)
      ((φ.toAlgHom (r ⊗ₜ t)) ⊗ₜ u)
    simp only [AlgHom.comp_apply] at hpipe
    rw [hpipe, Algebra.TensorProduct.lift_tmul]
    have hf2 : ((K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)).comp (φ.toAlgHom.comp
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] R' ⊗[S] S'))) u =
        (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') ((1:S') ⊗ₜ ((1:S') ⊗ₜ u)) := by
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]
      rw [← h23b2, hβφ, h23b1, K6.bT_tmul]
      simp
    have hg : ∀ z : S' ⊗[S] R', K6.outL S' ((K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)).comp (φ.toAlgHom.comp
        (Algebra.TensorProduct.includeLeft : R' →ₐ[S] R' ⊗[S] S'))) z
        = K6.bS S' ((Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S'))
            (σ₁₂.comp ϑ₂) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s r' =>
        have hr' : (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)) (φ.toAlgHom ((Algebra.TensorProduct.includeLeft :
            R' →ₐ[S] R' ⊗[S] S') r')) = σ₁₂ (ϑ₂ r') := by
          simp only [Algebra.TensorProduct.includeLeft_apply]
          rw [← h23b2, hβφ, h23b1, K6.bT_tmul]
          simp [← Algebra.TensorProduct.one_def]
        rw [K6.outL_tmul, K6.bS_tmul, AlgHom.comp_apply, AlgHom.comp_apply, hr']
        simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [hf2, hg, ← h12b2, hβφ, h12b1, K6.bT_tmul]
    rw [mul_assoc, ← map_mul]
    congr 1
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hR : ∀ (r : R') (t u : S'),
      K6.outL S' (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂))
        (((Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp
          ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
            ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
              ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp
                ((Algebra.TensorProduct.map (AlgHom.id S R')
                    (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                  (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom)))))
          ((r ⊗ₜ t) ⊗ₜ u)) =
      σ₁₂ (ϑ₁ r) * (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') ((1:S') ⊗ₜ (t ⊗ₜ u)) := by
    intro r t u
    simp only [AlgHom.comp_apply]
    simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.assoc_symm_tmul,
      AlgHom.id_apply, AlgEquiv.coe_algHom]
    have hpipe2 := AlgHom.congr_fun (K6.outL_map_assoc (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)) (Algebra.TensorProduct.comm S R' S').toAlgHom)
      ((φ.toAlgHom (r ⊗ₜ u)) ⊗ₜ t)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom] at hpipe2
    rw [hpipe2, Algebra.TensorProduct.lift_tmul]
    have hf2 : ((K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)).comp ((Algebra.TensorProduct.comm S R' S').toAlgHom.comp
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] R' ⊗[S] S'))) t =
        (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''') ((1:S') ⊗ₜ (t ⊗ₜ (1:S'))) := by
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]
      simp only [AlgEquiv.coe_algHom, Algebra.TensorProduct.comm_tmul, K6.bS_tmul, AlgHom.coe_comp,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        IsScalarTower.coe_toAlgHom', map_one, mul_one]
    have hg2 : ∀ z : S' ⊗[S] R', K6.outL S' ((K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)).comp ((Algebra.TensorProduct.comm S R' S').toAlgHom.comp
        (Algebra.TensorProduct.includeLeft : R' →ₐ[S] R' ⊗[S] S'))) z
        = K6.bS S' ((Algebra.TensorProduct.map (AlgHom.id S S')
            (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).comp
            (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s r' =>
        have hr2 : (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂)) ((Algebra.TensorProduct.comm S R' S').toAlgHom ((Algebra.TensorProduct.includeLeft :
            R' →ₐ[S] R' ⊗[S] S') r')) = σ₁₃ (ϑ₂ r') := by
          simp only [Algebra.TensorProduct.includeLeft_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.comm_tmul,
            K6.bS_tmul, AlgHom.coe_comp, Function.comp_apply, map_one, one_mul]
        rw [K6.outL_tmul, K6.bS_tmul, AlgHom.comp_apply, AlgHom.comp_apply, hr2]
        simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [hf2, hg2, ← h13b2, hβφ', h13b1, K6.bT_tmul]
    rw [mul_assoc, ← map_mul]
    congr 1
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hcomp : (K6.outL S' (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂))).comp ((Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom))))) =
      (Algebra.TensorProduct.lift (σ₁₂.comp ϑ₁) ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S'))) (fun _ _ => Commute.all _ _)).comp (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom := by
    refine AlgHom.toLinearMap_injective (TensorProduct.ext_threefold fun r t u => ?_)
    simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply]
    have h := hR r t u
    simp only [AlgHom.comp_apply] at h
    rw [h]
    simp [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.lift_tmul]
  have hbijGA : Function.Bijective ⇑((Algebra.TensorProduct.lift (σ₁₂.comp ϑ₁) ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S'))) (fun _ _ => Commute.all _ _)).comp (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom) := by
    simp only [AlgHom.coe_comp, AlgEquiv.coe_algHom]
    exact hbij.comp (Algebra.TensorProduct.assoc S S S R' S' S').bijective
  have hsurjR : Function.Surjective ⇑((Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom))))) := by
    simp only [AlgHom.coe_comp, AlgEquiv.coe_algHom]
    refine Function.Surjective.comp ?_ (Function.Surjective.comp ?_
      (Function.Surjective.comp ?_ (Function.Surjective.comp ?_
        (Function.Surjective.comp ?_ ?_))))
    · exact (Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm S R' S')).surjective
    · exact (Algebra.TensorProduct.assoc S S S S' R' S').surjective
    · exact (Algebra.TensorProduct.congr φ AlgEquiv.refl).surjective
    · exact (Algebra.TensorProduct.assoc S S S R' S' S').symm.surjective
    · exact (Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm S S' S')).surjective
    · exact (Algebra.TensorProduct.assoc S S S R' S' S').surjective
  have hinjg : Function.Injective ⇑(K6.outL S' (K6.bS S' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')).comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) (σ₁₃.comp ϑ₂))) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := hsurjR a
    obtain ⟨b', rfl⟩ := hsurjR b
    have h3 := ((AlgHom.congr_fun hcomp a').symm.trans hab).trans (AlgHom.congr_fun hcomp b')
    exact congrArg _ (hbijGA.injective h3)
  refine AlgHom.toLinearMap_injective (TensorProduct.ext_threefold fun r t u => ?_)
  simp only [AlgHom.toLinearMap_apply]
  exact hinjg ((hL r t u).trans ((hR r t u).symm))

end S_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities
end P2MW
export P2MW.S_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities (solution)
