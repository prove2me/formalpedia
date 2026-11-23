-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_BasicForm
-- name    : Development_AbelianVarietyTheory_Definitions_GlobalTwisting_BasicForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:27.937991+00:00
-- url     : https://prove2.me/theorems/b727624d-2584-48a2-b342-60922d60cbd4
-- title:
--   Basic Form
-- statement:
--   Definitions and structural lemmas for Basic Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/BasicForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix
namespace GlobalTheory.BorelCoh
section Complex
variable {C : ℕ → Type} [∀ q, AddCommGroup (C q)] [∀ q, Module ℂ (C q)]
def IsBd (d : ∀ q, C q → C (q + 1)) (T : ∀ q, Set (C q)) : (q : ℕ) → C q → Prop
  | 0, c => c = 0
  | q + 1, c => ∃ η ∈ T q, d q η = c
def CohGE (d : ∀ q, C q → C (q + 1)) (T : ∀ q, Set (C q)) (q n : ℕ) : Prop :=
  ∃ w : Fin n → C q, (∀ i, w i ∈ T q ∧ d q (w i) = 0) ∧ ∀ c : Fin n → ℂ, IsBd d T q (∑ i, c i • w i) → c = 0
end Complex
section Rel
variable {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
def gd (L : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) : P [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L X).restrictScalars ℝ).compAlternatingMap f
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L X Y) (f v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c X) (f v) }
def relCo {K : Type} (ad : K → P → P) (κ : K → Module.End ℂ M) (S : Submodule ℂ M) (q : ℕ) :
    Set (P [⋀^Fin q]→ₗ[ℝ] M) :=
  {f | (∀ k X, f (fun i => ad k (X i)) = κ k (f X)) ∧ ∀ X, f X ∈ S}
def basicCo {K : Type} (ad : K → P → P) (κ : K → Module.End ℂ M) (S : Submodule ℂ M) (L : P →ₗ[ℝ] Module.End ℂ M)
    (Z : P) (q : ℕ) : Set (P [⋀^Fin q]→ₗ[ℝ] M) :=
  {f | f ∈ relCo ad κ S q ∧ (∀ X i, X i = Z → f X = 0) ∧ ∀ X, L Z (f X) = 0}
end Rel
section Forms
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Type} {d : ℕ}
abbrev Form (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d q : ℕ) : Type :=
  Y → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)
def formD (O : Set V) {q : ℕ} (α : Form V Y d q) : Form V Y d (q + 1) :=
  fun y => O.indicator (extDeriv (α y))
def invForm (O : Set V) {Γ : Type} [Group Γ] [MulAction Γ Y] (σ : Γ → V →L[ℝ] V) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (q : ℕ) : Set (Form V Y d q) :=
  {α | (∀ y, ∀ x ∉ O, α y x = 0) ∧ (∀ y, ContDiffOn ℝ ∞ (α y) O) ∧
    ∀ γ y x (X : Fin q → V), α (γ • y) (σ γ x) (fun i => σ γ (X i)) = ξ γ *ᵥ α y x X}
def basicForm (O : Set V) {Γ : Type} [Group Γ] [MulAction Γ Y] (σ : Γ → V →L[ℝ] V) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (q : ℕ) : Set (Form V Y d q) :=
  {α | α ∈ invForm O σ ξ q ∧ (∀ y x (X : Fin q → V) i, X i = x → α y x X = 0) ∧
    ∀ y x (X : Fin q → V) (s : ℝ), 0 < s → α y (s • x) (fun i => s • X i) = α y x X}
end Forms
section Group
variable (𝕜 ι : Type) [RCLike 𝕜] [Fintype ι] (a : ℕ)
abbrev Mat : Type := Fin a → Fin a → ι → 𝕜
def hermV : Submodule ℝ (Mat 𝕜 ι a) where
  carrier := {x | ∀ i j, x j i = star (x i j)}
  add_mem' {x y} hx hy i j := by simp [hx i j, hy i j]
  zero_mem' i j := by simp
  smul_mem' c x hx i j := by
    funext t
    have h := congrFun (hx i j) t
    simp only [Pi.smul_apply, Pi.star_apply] at h ⊢
    rw [h, RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, star_mul', RCLike.star_def, RCLike.conj_ofReal]
def posSet : Set (hermV 𝕜 ι a) := {p | ∃ g : GL (Fin a) (ι → 𝕜), (p : Mat 𝕜 ι a) = Matrix.of.symm (g.val * g.valᴴ)}
variable {𝕜 ι a}
def invSet : Set (Mat 𝕜 ι a) := {x | IsUnit (Matrix.of x)}
def lmulH (x : Mat 𝕜 ι a) : hermV 𝕜 ι a →L[ℝ] Mat 𝕜 ι a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.mulLeft ℝ (Matrix.of x) : Matrix (Fin a) (Fin a) (ι → 𝕜) →ₗ[ℝ] _) ∘ₗ (hermV 𝕜 ι a).subtype)
variable (𝕜 ι a) in

abbrev GCo (Y : Type) (d q : ℕ) : Type := Y → Mat 𝕜 ι a → hermV 𝕜 ι a [⋀^Fin q]→L[ℝ] (Fin d → ℂ)
def gDiff {Y : Type} {d q : ℕ} (w : GCo 𝕜 ι a Y d q) : GCo 𝕜 ι a Y d (q + 1) :=
  fun y => invSet.indicator fun x => ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ (w y) x).comp (lmulH x))
def gCo {Y H : Type} [Group H] [MulAction H Y] (ρ : H →* GL (Fin a) (ι → 𝕜)) {d : ℕ} (ξ : H →* Matrix (Fin d) (Fin d) ℂ)
    (K₀ : Set (Matrix.unitaryGroup (Fin a) (ι → 𝕜))) (q : ℕ) : Set (GCo 𝕜 ι a Y d q) :=
  {w | (∀ y, ∀ x ∉ invSet, w y x = 0) ∧ (∀ y, ContDiffOn ℝ ∞ (w y) invSet) ∧
    (∀ k ∈ K₀, ∀ y x (X X' : Fin q → hermV 𝕜 ι a),
      (∀ i, (X' i : Mat 𝕜 ι a) = Matrix.of.symm (k.val * Matrix.of (X i : Mat 𝕜 ι a) * star k.val)) →
      w y (Matrix.of.symm (Matrix.of x * k.val)) X = w y x X') ∧
    (∀ h y x X, w (h • y) (Matrix.of.symm ((ρ h).val * Matrix.of x)) X = ξ h *ᵥ w y x X) ∧
    (∀ y x (X : Fin q → hermV 𝕜 ι a) i, (X i : Mat 𝕜 ι a) = Matrix.of.symm 1 → w y x X = 0) ∧
    ∀ y x X (s : ℝ), 0 < s → w y (s • x) X = w y x X}
def conjL (g : GL (Fin a) (ι → 𝕜)) : hermV 𝕜 ι a →L[ℝ] hermV 𝕜 ι a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => ⟨Matrix.of.symm (g.val * Matrix.of (p : Mat 𝕜 ι a) * g.valᴴ), fun i j => by
        have hp : (Matrix.of (p : Mat 𝕜 ι a))ᴴ = Matrix.of (p : Mat 𝕜 ι a) :=
          Matrix.ext fun k l => (p.2 l k).symm
        have h := congrArg (fun m : Matrix (Fin a) (Fin a) (ι → 𝕜) => m j i)
          (show (g.val * Matrix.of (p : Mat 𝕜 ι a) * g.valᴴ)ᴴ = g.val * Matrix.of (p : Mat 𝕜 ι a) * g.valᴴ by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hp, Matrix.mul_assoc])
        exact h.symm⟩
      map_add' := fun p p' => Subtype.ext (funext fun i => funext fun j => by
        change (g.val * (Matrix.of (p : Mat 𝕜 ι a) + Matrix.of (p' : Mat 𝕜 ι a)) * g.valᴴ) i j = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl)
      map_smul' := fun c p => Subtype.ext (funext fun i => funext fun j => by
        change (g.val * (c • Matrix.of (p : Mat 𝕜 ι a)) * g.valᴴ) i j = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl) }
def funRep {Γ : Type} [Group Γ] (Y : Type) [MulAction Γ Y] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ Γ (Y → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f y => ξ γ *ᵥ f (γ⁻¹ • y)
      map_add' := fun f g => funext fun y => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun y => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f y; simp
  map_mul' γ δ := by ext f y; simp [mul_smul]
end Group
end GlobalTheory.BorelCoh
end


