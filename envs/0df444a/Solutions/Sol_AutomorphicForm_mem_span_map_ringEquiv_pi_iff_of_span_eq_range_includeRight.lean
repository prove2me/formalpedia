-- Prove2me | solution 1 for AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e9d2b31a-b419-57df-80a8-62393c632b78

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mXiSpan

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev F : Type := InfiniteAdeleRing K

abbrev EK : Type := L ⊗[K] InfiniteAdeleRing K

abbrev EP : Type := (w : InfinitePlace K) → L ⊗[K] w.Completion

abbrev algRF : Algebra ℝ (F K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

attribute [local instance] algRF

abbrev algRE : Algebra ℝ (EK K L) :=
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

attribute [local instance] algRE

theorem algebraMap_RE (r : ℝ) : algebraMap ℝ (EK K L) r = (1 : L) ⊗ₜ[K] algebraMap ℝ (F K) r := rfl

theorem smul_EK (r : ℝ) (z : EK K L) : r • z = ((1 : L) ⊗ₜ[K] algebraMap ℝ (F K) r) * z :=
  Algebra.smul_def r z

section Xi

variable (Ξ : EK K L ≃+* EP K L)
  (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace K), Ξ (x ⊗ₜ a) w = x ⊗ₜ (a w))
  [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
  (hΞr : ∀ (r : ℝ) (z : EK K L), Ξ (r • z) = r • Ξ z)

include hΞr in

def ΦL : Matrix (Fin 2) (Fin 2) (EK K L) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) (EP K L) where
  toFun X := X.map Ξ
  invFun Y := Y.map Ξ.symm
  map_add' X Y := by ext a b; simp only [Matrix.map_apply, Matrix.add_apply, map_add]
  map_smul' r X := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, RingHom.id_apply, hΞr]
  left_inv X := by ext a b; simp
  right_inv Y := by ext a b; simp

theorem ΦL_apply (X : Matrix (Fin 2) (Fin 2) (EK K L)) : ΦL K L Ξ hΞr X = X.map Ξ := rfl

include hΞr in
theorem linearIndependent_map {n : ℕ} (e : Fin n → Matrix (Fin 2) (Fin 2) (EK K L)) (h : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun a => (e a).map Ξ) :=
  h.map' (ΦL K L Ξ hΞr).toLinearMap (LinearEquiv.ker _)

include hΞr in
theorem mem_span_map_iff {n : ℕ} (e : Fin n → Matrix (Fin 2) (Fin 2) (EK K L))
    (X : Matrix (Fin 2) (Fin 2) (EP K L)) :
    X ∈ Submodule.span ℝ (Set.range fun a => (e a).map Ξ) ↔
      X.map Ξ.symm ∈ (Submodule.span ℝ (Set.range e) : Set (Matrix (Fin 2) (Fin 2) (EK K L))) := by
  have hrange : (Set.range fun a => (e a).map Ξ) = (ΦL K L Ξ hΞr).toLinearMap '' Set.range e := by
    rw [← Set.range_comp]; rfl
  rw [hrange, ← Submodule.map_span, SetLike.mem_coe]
  constructor
  · intro hX
    obtain ⟨Z, hZ, hZX⟩ := Submodule.mem_map.mp hX
    have : X.map Ξ.symm = Z := by
      rw [← hZX]; exact (ΦL K L Ξ hΞr).left_inv Z
    rwa [this]
  · intro hX
    refine Submodule.mem_map.mpr ⟨X.map Ξ.symm, hX, ?_⟩
    exact (ΦL K L Ξ hΞr).right_inv X

include hΞt hΞr in

theorem smul_one_tmul (w : InfinitePlace K) (r : ℝ) (a : F K) :
    r • ((1 : L) ⊗ₜ[K] a w : L ⊗[K] w.Completion) = (1 : L) ⊗ₜ[K] ((algebraMap ℝ (F K) r * a) w) := by
  have h := hΞr r ((1 : L) ⊗ₜ[K] a)
  rw [smul_EK, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
  have hw := congrFun h w
  rw [hΞt, Pi.smul_apply, hΞt] at hw
  exact hw.symm

end Xi

section KSpan

variable (Ξ : EK K L ≃+* EP K L)
  (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace K), Ξ (x ⊗ₜ a) w = x ⊗ₜ (a w))
  [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
  (hΞr : ∀ (r : ℝ) (z : EK K L), Ξ (r • z) = r • Ξ z)

include hΞt hΞr in

theorem exists_of_mem_span_range (w : InfinitePlace K) (Z : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))
    (hZ : Z ∈ Submodule.span ℝ (Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
      Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x)))) :
    ∃ Y : Matrix (Fin 2) (Fin 2) w.Completion, Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x) = Z := by
  classical
  let R : Submodule ℝ (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) :=
    { carrier := Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
        Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x))
      add_mem' := by
        rintro _ _ ⟨Y₁, rfl⟩ ⟨Y₂, rfl⟩
        exact ⟨Y₁ + Y₂, by ext a b; simp [Matrix.map_apply, TensorProduct.tmul_add]⟩
      zero_mem' := ⟨0, by ext a b; simp [Matrix.map_apply]⟩
      smul_mem' := by
        rintro r _ ⟨Y, rfl⟩
        refine ⟨Matrix.of fun a b => ((algebraMap ℝ (F K) r * (@id (F K) (Pi.single w (Y a b)))) w), ?_⟩
        ext a b
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply]
        rw [← smul_one_tmul K L Ξ hΞt hΞr w r (@id (F K) (Pi.single w (Y a b)))]
        congr 2
        exact Pi.single_eq_same w (Y a b) }
  have hR : Z ∈ R := by
    have h := hZ
    rw [show Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
        Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x)) = (R : Set _) from rfl, Submodule.span_eq] at h
    exact h
  exact hR

include hΞt hΞr in
theorem kspan {n₁ : ℕ} (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (EK K L))
    (hK : LinearIndependent ℝ e₁ ∧
      (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (EK K L))) =
        Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
          Y.map (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K))) :
    LinearIndependent ℝ (fun a => (e₁ a).map Ξ) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) (EP K L),
        X ∈ Submodule.span ℝ (Set.range (fun a => (e₁ a).map Ξ)) ↔
          ∀ w : InfinitePlace K, X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) w) ∈
            Submodule.span ℝ (Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
              Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x))) := by
  refine ⟨linearIndependent_map K L Ξ hΞr e₁ hK.1, fun X => ?_⟩
  rw [mem_span_map_iff K L Ξ hΞr, hK.2]
  constructor
  · rintro ⟨Y, hY⟩ w
    apply Submodule.subset_span
    refine ⟨Y.map (fun y : F K => y w), ?_⟩
    ext a b
    have h1 := congrFun (congrFun hY a) b
    simp only [Matrix.map_apply, Algebra.TensorProduct.includeRight_apply] at h1
    have h2 := congrArg (fun z : EK K L => Ξ z w) h1
    simp only [RingEquiv.apply_symm_apply, hΞt] at h2
    simp only [Matrix.map_apply] at h2 ⊢
    exact h2
  · intro hX
    have hY := fun w => exists_of_mem_span_range K L Ξ hΞt hΞr w _ (hX w)
    choose Yw hYw using hY
    refine ⟨Matrix.of fun a b => (fun w => Yw w a b : F K), ?_⟩
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, Algebra.TensorProduct.includeRight_apply]
    apply Ξ.injective
    rw [RingEquiv.apply_symm_apply]
    funext w
    rw [hΞt]
    have := congrFun (congrFun (hYw w) a) b
    simp only [Matrix.map_apply] at this
    exact this

end KSpan

end P2mXiSpan

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((w : InfinitePlace K) → L ⊗[K] w.Completion))
    (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace K), Ξ (x ⊗ₜ a) w = x ⊗ₜ (a w))
    [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
    (hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      Ξ (r • z) = r • Ξ z)
    (n₁ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hK :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      LinearIndependent ℝ e₁ ∧
        (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
            Y.map (Algebra.TensorProduct.includeRight :
              InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K))) :
    LinearIndependent ℝ (fun a => (e₁ a).map Ξ) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion),
        X ∈ Submodule.span ℝ (Set.range (fun a => (e₁ a).map Ξ)) ↔
          ∀ w : InfinitePlace K, X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) w) ∈
            Submodule.span ℝ (Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
              Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x))) := by
  exact P2mXiSpan.kspan K L Ξ hΞt hΞr e₁ hK

end S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight
end P2MW
export P2MW.S_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight (solution)
