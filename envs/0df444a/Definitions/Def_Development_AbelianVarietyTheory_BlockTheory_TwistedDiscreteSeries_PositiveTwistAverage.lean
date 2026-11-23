-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:37.698167+00:00
-- url     : https://prove2.me/theorems/42fd06aa-45a3-4611-910c-2f3e6397c978
-- title:
--   Positive Twist Average
-- statement:
--   Definitions and structural lemmas for Positive Twist Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PositiveTwistAverage.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def IsUnramUnitary (η : kˣ →* ℂˣ) : Prop := IsUnram η ∧ ∀ x, ‖(η x : ℂ)‖ = 1
def omTw {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ η' η : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : Matrix b a k → ℂ := fun x =>
  (η' (Matrix.GeneralLinearGroup.det g) : ℂ) * ((η (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) * om μ g h Φ x
def perp {m : Type} [Fintype m] (ψ : AddChar k Circle) (U₀ : Submodule 𝒪[k] (m → k)) : AddSubgroup (m → k) where
  carrier := {β | ∀ u ∈ U₀, ψ (u ⬝ᵥ β) = 1}
  add_mem' := fun {x y} hx hy u hu => by
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx u hu, hy u hu, one_mul]
  zero_mem' := fun u _ => by simp
  neg_mem' := fun {x} hx u hu => by rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx u hu, inv_one]
def IsReps {V : Type} [AddCommGroup V] (D B : AddSubgroup V) (T : Finset V) : Prop :=
  (∀ t ∈ T, t ∈ D) ∧ ∀ β ∈ D, ∃! t, t ∈ T ∧ β - t ∈ B
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
def IsPosTw (ψ : AddChar k Circle) (η : kˣ →* ℂˣ) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ p σ (b φ)) ∧ ∀ (g : GL n k) φ v, b (π g φ) (σ (embX c g) v) =
    (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b φ v
def IsColLift (μ : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) P') (π : Representation ℂ (GL n k) P)
    (θ : P' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] P) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) φ, ∀ Ψ ∈ SB (Matrix n n' k), θ (π' g φ) (om μ g h Ψ) = π h (θ φ Ψ)
def IsRowLift (μ η' η : kˣ →* ℂˣ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A')
    (ϑ : A →ₗ[ℂ] (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) →ₗ[ℂ] A') : Prop :=
  ∀ (g : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) F,
    ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ϑ (σ h F) (omTw μ η' η g h Φ) = σ' g (ϑ F Φ)
variable [MeasurableSpace k] [BorelSpace k]
def avg (ν : Measure k) (μ η' η : kˣ →* ℂˣ) (p : ℕ) (C : Submodule 𝒪[k] (n' → k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun x =>
  ∫ u in (C : Set (n' → k)), omTw μ η' η (rowE (c + 1) p u) 1 Φ x ∂(Measure.pi fun _ => ν)
def RrIs (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (μ η' η : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (θ : P' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] P) (b : P → A → ℂ) (φ : P') (F : A)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∀ z', IsQuotInt ν μX μG p (fun h => b (θ φ (opE ψ ν p (omTw μ η' η 1 h Φ))) (σ h F)) z' ↔ z' = z
def TargetFormulas (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k))
    (μG : Measure (GL (n ⊕ Fin c) k)) (μ η' η : kˣ →* ℂˣ) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (U : Subgroup (GL (n ⊕ Fin c) k))
    (C₀ U₀ B₁ : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (P P' A : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P')
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (θ : P' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] P)
    (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A),
    IsSmoothRep π → IsSmoothRep π' → IsSmoothRep σ → IsColLift μ π' π θ → IsPosTw ψ η p π σ b →
    (∀ u ∈ U, σ u F = F) →
    (∀ C : Submodule 𝒪[k] (n' → k), C.IsLattice k → C₀ ≤ C → ∃ z,
      RrIs ψ ν μX μG μ η' η (p + 1) σ θ (fun φ₁ v => exUp ν p σ (b φ₁) v) φ F Φ z ∧
      RrIs ψ ν μX μG μ η' η p σ θ (fun φ₁ v => b φ₁ v) φ F (avg ν μ η' η p C Φ) z) ∧
    (∀ T : Finset (n' → k), IsReps (perp ψ U₀) B₁.toAddSubgroup T → ∃ w : (n' → k) → ℂ,
      (∀ β ∈ T, RrIs ψ ν μX μG μ η' η (p + 1) σ θ (fun φ₁ v => exUp ν p σ (b φ₁) v) φ F
        (omTw μ η' η (colE (c + 1) (p + 1) β) 1 Φ) (w β)) ∧
      RrIs ψ ν μX μG μ η' η p σ θ (fun φ₁ v => b φ₁ v) φ F Φ
        ((((Measure.pi fun _ : n' => ν).real (B₁ : Set (n' → k)) : ℝ) : ℂ) * ∑ β ∈ T, w β))
def SourceFormulas (ψ : AddChar k Circle) (ν : Measure k) (μ η' η : kˣ →* ℂˣ) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (U : Subgroup (GL (n ⊕ Fin c) k))
    (C₀ U₀ B₁ : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (P' A A' : Type) [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    (π' : Representation ℂ (GL n' k) P') (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A')
    (ϑ : A →ₗ[ℂ] (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) →ₗ[ℂ] A')
    (b' : P' →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (φ : P') (F : A),
    IsSmoothRep π' → IsSmoothRep σ → IsSmoothRep σ' → IsRowLift μ η' η σ σ' ϑ → IsPosTw ψ η' p π' σ' b' →
    (∀ u ∈ U, σ u F = F) →
    (∀ C : Submodule 𝒪[k] (n' → k), C.IsLattice k → C₀ ≤ C →
      exUp ν p σ' (b' φ) (ϑ F Φ) = b' φ (ϑ F (avg ν μ η' η p C Φ))) ∧
    (∀ T : Finset (n' → k), IsReps (perp ψ U₀) B₁.toAddSubgroup T →
      b' φ (ϑ F Φ) = (((Measure.pi fun _ : n' => ν).real (B₁ : Set (n' → k)) : ℝ) : ℂ) *
        ∑ β ∈ T, exUp ν p σ' (b' φ) (ϑ F (omTw μ η' η (colE (c + 1) (p + 1) β) 1 Φ)))
def UniformExchange : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p < c →
  ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
  ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)), μX.IsHaarMeasure → μG.IsHaarMeasure →
  ∀ (μ η' η : kˣ →* ℂˣ), Continuous μ → IsUnramUnitary η' → IsUnramUnitary η →
  ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
  ∀ U : Subgroup (GL (n ⊕ Fin c) k), IsOpen (U : Set (GL (n ⊕ Fin c) k)) →
  ∃ C₀ U₀ B₁ : Submodule 𝒪[k] (n' → k), C₀.IsLattice k ∧ U₀.IsLattice k ∧ B₁.IsLattice k ∧
    (∀ u ∈ U₀, omTw μ η' η (rowE (c + 1) p u) 1 Φ = Φ) ∧
    (∀ β ∈ B₁, omTw μ η' η (colE (c + 1) (p + 1) β) 1 Φ = Φ) ∧
    B₁.toAddSubgroup ≤ perp ψ U₀ ∧ (∃ T, IsReps (perp ψ U₀) B₁.toAddSubgroup T) ∧
    TargetFormulas ψ ν μX μG μ η' η p Φ U C₀ U₀ B₁ ∧ SourceFormulas ψ ν μ η' η p Φ U C₀ U₀ B₁
end GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage


