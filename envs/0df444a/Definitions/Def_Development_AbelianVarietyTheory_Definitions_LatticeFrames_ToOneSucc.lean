-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:38.29732+00:00
-- url     : https://prove2.me/theorems/2262faf0-7dfe-452f-a73b-de5e11922641
-- title:
--   To One Succ
-- statement:
--   Definitions and structural lemmas for To One Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/ToOneSucc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped ENNReal
noncomputable section
namespace GlobalTheory.PosOne
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]
def IsSrc {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (ρ' : Representation ℂ (GL a k) (SB (Matrix b a k))) : Prop :=
  ∀ g (Φ : SB (Matrix b a k)), ((ρ' g Φ : SB (Matrix b a k)) : Matrix b a k → ℂ) = om μ g 1 Φ.1
def BilPos (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ Ψ, IsNEquiv ψ p σ (B Ψ)) ∧ ∀ (g : GL n k) (Ψ Ψ₁ : SB (Matrix n n' k)) (v : A), Ψ₁.1 = om μ 1 g Ψ.1 →
    B Ψ₁ (σ (embX c g) v) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * B Ψ v
def comb {G : Type} (e : G →₀ ℂ) (f : G → ℂ) : ℂ := e.sum fun g a => a * f g
def Covers {V : Type} [Zero V] (p : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (T : Finset (GL (n ⊕ Fin c) k))
    (f : GL (n ⊕ Fin c) k → V) : Prop :=
  Set.InjOn (DoubleCoset.mk (R k n c p) J) (T : Set (GL (n ⊕ Fin c) k)) ∧
    ∀ h, f h ≠ 0 → ∃ t ∈ T, DoubleCoset.mk (R k n c p) J h = DoubleCoset.mk (R k n c p) J t
variable [MeasurableSpace k] [BorelSpace k]
def toOne (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ) : (A → ℂ) → A → ℂ :=
  Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
    (fun p rec l => rec (exDown ν (p + 1) σ l)) (P - 1)
def tInt (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h : GL (n ⊕ Fin c) k) : ℂ :=
  app B (opE ψ ν p (om μ 1 h Φ)) (σ h F)
def tIntOne (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (P : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h : GL (n ⊕ Fin c) k) : ℂ :=
  toOne ν σ P (fun v => app B (opE ψ ν 1 (om μ 1 h Φ)) v) (σ h F)
def volCell (ν : Measure k) (m : Measure (GL n k)) (p : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k))
    (h : GL (n ⊕ Fin c) k) : ℝ≥0∞ :=
  ∫⁻ g, volN ν n c p {u : N k n c p | h⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k)) * h ∈ J} ∂m
def SrcComb (ψ : AddChar k Circle) (ν : Measure k) (P : ℕ) {b : Type} [Fintype b] [DecidableEq b]
    (ρ' : Representation ℂ (GL (n ⊕ Fin c) k) (SB (Matrix b (n ⊕ Fin c) k))) (Φ : SB (Matrix b (n ⊕ Fin c) k))
    (e : GL (n ⊕ Fin c) k →₀ ℂ) : Prop :=
  ∀ L : SB (Matrix b (n ⊕ Fin c) k) →ₗ[ℂ] ℂ, IsNEquiv ψ P ρ' L → toOne ν ρ' P L Φ = comb e fun g => L (ρ' g Φ)
def FJInt (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (μ : kˣ →* ℂˣ) (ρ : ℕ) (w : GL (n ⊕ Fin c) k → SB (Matrix n n' k) → SB (n → k) → ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ f : GL (n ⊕ Fin c) k → ℂ,
    (∀ h, HasTensorVal (w h) (fl ψ ν μ ρ (om μ 1 h Φ)) (f h)) ∧ IsQuotIntFJ ν μX μG ρ f z
section Double
variable {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
omit [MeasurableSpace k] [BorelSpace k] in

def TriPos (ψ : AddChar k Circle) (μ₁ μ₂ : kˣ →* ℂˣ) (ρ : ℕ) (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A)
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ Ψ₁, BilPos ψ μ₂ ρ σ (T Ψ₁)) ∧ ∀ (g : GL n₁ k) (Ψ₁ Ψ₁' : SB (Matrix n₁ n₀ k)) (Ψ₂ Ψ₂' : SB (Matrix n₂ n₁ k)),
    Ψ₁'.1 = om μ₁ 1 g Ψ₁.1 → Ψ₂'.1 = om μ₂ g 1 Ψ₂.1 → T Ψ₁' Ψ₂' = T Ψ₁ Ψ₂
def SymDbl (ψ : AddChar k Circle) (ν : Measure k) (m₁ : Measure (GL n₁ k)) (μ₁G : Measure (GL (n₁ ⊕ Fin (c + 1)) k))
    (m₂ : Measure (GL n₂ k)) (μ₂G : Measure (GL (n₂ ⊕ Fin c) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (ρ : ℕ)
    (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A)
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A)
    (Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ w : GL (n₁ ⊕ Fin (c + 1)) k → SB (Matrix n₁ n₀ k) → SB (n₁ → k) → ℂ,
    (∀ h Ψ Φ₀, IsQuotInt ν m₂ μ₂G ρ
      (fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂)) (σ h' F)) (w h Ψ Φ₀)) ∧
    FJInt ψ ν m₁ μ₁G μ₁ ρ w Φ₁ z
def OneDbl (ψ : AddChar k Circle) (ν : Measure k) (m₁ : Measure (GL n₁ k)) (μ₁G : Measure (GL (n₁ ⊕ Fin (c + 1)) k))
    (m₂ : Measure (GL n₂ k)) (μ₂G : Measure (GL (n₂ ⊕ Fin c) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (ρ : ℕ)
    (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A)
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A)
    (Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ w : GL (n₁ ⊕ Fin (c + 1)) k → SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ,
    (∀ h Ψ, IsQuotInt ν m₂ μ₂G 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F (om μ₂ h 1 Φ₂)) (w h Ψ)) ∧
    IsQuotInt ν m₁ μ₁G 1 (fun h => app (w h) (opE ψ ν 1 (om μ₁ 1 h Φ₁))) z
end Double
end GlobalTheory.PosOne


