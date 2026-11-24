-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_BoundaryVanishingPullback
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_BoundaryVanishingPullback
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:58.676452+00:00
-- url     : https://prove2.me/theorems/4d2cc117-b832-4c01-a343-db501bf35074
-- title:
--   Boundary Vanishing Pullback
-- statement:
--   Definitions and structural lemmas for Boundary Vanishing Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/BoundaryVanishingPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_inSupport_detRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
namespace GlobalTheory.IndefiniteRowSideFullHecke.RankStratification
def pullRep {Γ X : Type} [Group Γ] [TopologicalSpace X] (τ : Γ → X → X)
    (hc : ∀ γ, Continuous (τ γ)) (h1 : ∀ x, τ 1 x = x) (hm : ∀ γ δ x, τ (γ * δ) x = τ δ (τ γ x)) :
    Representation ℂ Γ (SB X) where
  toFun γ :=
    { toFun := fun Φ => ⟨fun x => Φ.1 (τ γ x), Φ.2.1.comp_continuous (hc γ),
        Φ.2.2.comp_homeomorph
          { toFun := τ γ, invFun := τ γ⁻¹
            left_inv := fun x => by rw [← hm, mul_inv_cancel, h1]
            right_inv := fun x => by rw [← hm, inv_mul_cancel, h1]
            continuous_toFun := hc γ, continuous_invFun := hc γ⁻¹ }⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
    show Φ.1 (τ 1 x) = Φ.1 x
    rw [h1]
  map_mul' γ δ := by
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
    show Φ.1 (τ (γ * δ) x) = Φ.1 (τ δ (τ γ x))
    rw [hm]
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Model
variable {a b : ℕ}
def move (γ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    Matrix (Fin b) (Fin a) k :=
  (γ.2⁻¹ : GL (Fin b) k).val * x * γ.1.val
theorem continuous_move (γ : GL (Fin a) k × GL (Fin b) k) : Continuous (move γ) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem move_one (x : Matrix (Fin b) (Fin a) k) : move 1 x = x := by simp [move]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem move_mul (γ δ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    move (γ * δ) x = move δ (move γ x) := by
  simp [move, Matrix.mul_assoc]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem rank_move (γ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    (move γ x).rank = x.rank := by
  unfold move
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units γ.1),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units γ.2⁻¹)]
variable (k) in

abbrev Stratum (a b r : ℕ) : Type := {x : Matrix (Fin b) (Fin a) k // x.rank = r}
def omChar (a b : ℕ) (μ : kˣ →* ℂˣ) : GL (Fin a) k × GL (Fin b) k →* ℂˣ :=
  (detChar (Fin a) (μ⁻¹ * absPow k ((b : ℂ) / 2))).comp (MonoidHom.fst _ _) *
    (detChar (Fin b) (μ * absPow k (-(a : ℂ) / 2))).comp (MonoidHom.snd _ _)
def omRep (a b : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k × GL (Fin b) k) (SB (Matrix (Fin b) (Fin a) k)) :=
  twist (pullRep move continuous_move move_one move_mul) (omChar a b μ)
def omStratum (a b r : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k × GL (Fin b) k) (SB (Stratum k a b r)) :=
  twist (pullRep (fun γ x => ⟨move γ x.1, (rank_move γ x.1).trans x.2⟩)
      (fun γ => ((continuous_move γ).comp continuous_subtype_val).subtype_mk _)
      (fun x => Subtype.ext (move_one x.1)) (fun γ δ x => Subtype.ext (move_mul γ δ x.1)))
    (omChar a b μ)
def omStratumG (a b r : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k) (SB (Stratum k a b r)) :=
  (omStratum a b r μ).comp (MonoidHom.inl _ _)
end Model
def NoBoundaryMaps {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ r : ℕ, r < a → ∀ f : (omStratumG a (a + t) r μ).IntertwiningMap (contra π), f.toLinearMap = 0
def AvoidsExponents {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + (j : ℂ))))
def charProd {u a : ℕ} (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a) {V₀ : Type} [AddCommGroup V₀]
    [Module ℂ V₀] (π₀ : Representation ℂ (GL (Fin (d 0)) k) V₀) (χ : Fin u → kˣ →* ℂˣ) :=
  parInd (stdBlocks d hd)
    (twist (π₀.comp (Pi.evalMonoidHom (fun i => GL (Fin (d i)) k) 0))
      (∏ i : Fin u, (detChar (Fin (d i.succ)) (χ i)).comp
        (Pi.evalMonoidHom (fun i => GL (Fin (d i)) k) i.succ)))
def LiftConclusion {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin (a + t)) k) V'),
    IsSmooth π' → π'.IsIrreducible →
    (∃ q : (omRep a (a + t) μ).IntertwiningMap (extTensor (contra π) π'), q.toLinearMap ≠ 0) →
      Nonempty (π'.Equiv (prod₂ π (detRep (Fin t) μ))) ∧
      (prod₂ π (detRep (Fin t) μ)).IsIrreducible ∧ IsUnitarisable (prod₂ π (detRep (Fin t) μ)) ∧
      Module.finrank ℂ ((omRep a (a + t) μ).IntertwiningMap (extTensor (contra π) π')) = 1
def BoundaryVanishing : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → IsUnitaryChar μ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin a) k) V),
      IsSmooth π → π.IsIrreducible → IsUnitarisable π →
      (AvoidsExponents t μ π ∨ a ≤ t) → NoBoundaryMaps t μ π
def BoundaryVanishingVariant : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → IsUnitaryChar μ →
    ∀ (u : ℕ) (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a), d 0 ≤ t → (∀ i : Fin u, d i.succ ≤ t + 1) →
    ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℂ V₀] (π₀ : Representation ℂ (GL (Fin (d 0)) k) V₀),
      IsSmooth π₀ → π₀.IsIrreducible → IsUnitarisable π₀ →
    ∀ χ : Fin u → kˣ →* ℂˣ, (∀ i, IsSmoothChar (χ i)) → (∀ i, IsUnitaryChar (χ i)) →
      NoBoundaryMaps t μ (charProd d hd π₀ χ)
def LiftVariant : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → IsUnitaryChar μ →
    ∀ (u : ℕ) (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a), d 0 ≤ t → (∀ i : Fin u, d i.succ ≤ t + 1) →
    ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℂ V₀] (π₀ : Representation ℂ (GL (Fin (d 0)) k) V₀),
      IsSmooth π₀ → π₀.IsIrreducible → IsUnitarisable π₀ →
    ∀ χ : Fin u → kˣ →* ℂˣ, (∀ i, IsSmoothChar (χ i)) → (∀ i, IsUnitaryChar (χ i)) →
      LiftConclusion t μ (charProd d hd π₀ χ)
example (a b : ℕ) : ∃ φ : SB (Stratum k a b 0), φ ≠ 0 := by
  have hs : Subsingleton (Stratum k a b 0) := ⟨fun x y => Subtype.ext (by
    have key : ∀ z : Stratum k a b 0, z.1 = 0 := fun z => by
      have h0 : LinearMap.range z.1.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 z.2
      apply Matrix.toLin'.injective
      rw [map_zero]
      exact LinearMap.range_eq_bot.1 h0
    rw [key x, key y])⟩
  refine ⟨⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩, fun h => ?_⟩
  simpa using congrFun (congrArg Subtype.val h) ⟨0, Matrix.rank_zero⟩
example (μ : kˣ →* ℂˣ) : ¬ AvoidsExponents 1 μ (detRep (Fin 1) (μ * absPow k (-1))) := by
  intro h
  have := inSupport_detRep (N := 1) (μ * absPow k (-1)) 0
  apply h 0
  simpa using this
end GlobalTheory.IndefiniteRowSideFullHecke.RankStratification


