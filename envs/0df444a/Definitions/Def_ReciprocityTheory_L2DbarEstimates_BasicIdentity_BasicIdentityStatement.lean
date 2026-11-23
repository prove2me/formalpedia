-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
-- name    : ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:16.648412+00:00
-- url     : https://prove2.me/theorems/34174d07-5110-4847-a9b7-df81463cbe45
-- title:
--   Basic Identity Statement
-- statement:
--   Definitions and structural lemmas for Basic Identity Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/BasicIdentityStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
def IsTestForm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → V n) : Prop :=
  ∀ j : Fin n, Ck n z 2 (fun x => f x j) ∧ HasCompactSupport (fun x => f x j)
def dTw {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n)
    (u : M → ℂ) (x : M) : ℂ :=
  d n z j u x - u x * d n z j (fun y => ((ph y : ℝ) : ℂ)) x
def tstar {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph₁ ph₂ : M → ℝ)
    (f : M → V n) (x : M) : ℂ :=
  -((Real.exp (ph₁ x) : ℂ) * ∑ j, d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)
def sbar {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → V n) (x : M)
    (j k : Fin n) : ℂ :=
  db n z j (fun y => f y k) x - db n z k (fun y => f y j) x
def sq2 (n : ℕ) (σ : Fin n → Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2
def dSqR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ψ : M → ℝ) (x : M) : ℝ :=
  ∑ j, ‖d n z j (fun y => (ψ y : ℂ)) x‖ ^ 2
def WIbpStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph : M → ℝ) (k : Fin n) (a b : M → ℂ),
      CkR n z 1 ph → Ck n z 1 a → Ck n z 1 b → (HasCompactSupport a ∨ HasCompactSupport b) →
      (∫ x, db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
          -∫ x, a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z ∧
        (∫ x, dTw n z ph k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
          -∫ x, a x * conj (db n z k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z
def CommStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph : M → ℝ) (j k : Fin n) (u : M → ℂ) (x : M), CkR n z 2 ph → Ck n z 2 u →
      dTw n z ph k (db n z j u) x - db n z j (dTw n z ph k u) x =
        d n z k (db n z j (fun y => (ph y : ℂ))) x * u x
def BasicIdentityStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph : M → ℝ) (f : M → V n), CkR n z 2 ph → IsTestForm n z f →
      (∫ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) ∂vol n z) +
          ∫ x, sq2 n (sbar n z f x) * Real.exp (-ph x) ∂vol n z =
        (∫ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) ∂vol n z) +
          ∫ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) ∂vol n z
def TStarIbpStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph₁ ph₂ : M → ℝ) (g : M → ℂ) (f : M → V n), CkR n z 1 ph₁ → CkR n z 1 ph₂ →
      Ck n z 1 g → (∀ j, Ck n z 1 (fun x => f x j) ∧ HasCompactSupport (fun x => f x j)) →
      (∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z) =
        ∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z
def TStarPointStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph ψ : M → ℝ) (f : M → V n), CkR n z 1 ph → CkR n z 1 ψ →
      (∀ j, Ck n z 1 (fun x => f x j)) → ∀ x : M,
        (Real.exp (ψ x) : ℂ) * tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x =
          -∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)
def TStarMulStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph₁ ph₂ η : M → ℝ) (f : M → V n), CkR n z 1 ph₂ → CkR n z 1 η →
      (∀ j, Ck n z 1 (fun x => f x j)) → ∀ x : M,
        tstar n z ph₁ ph₂ (fun y => (η y : ℂ) • f y) x =
          (η x : ℂ) * tstar n z ph₁ ph₂ f x -
            (Real.exp (ph₁ x - ph₂ x) : ℂ) * ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j
def APStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (ph ψ : M → ℝ) (ε : ℝ) (f : M → V n), CkR n z 2 ph → CkR n z 1 ψ → 0 < ε →
      IsTestForm n z f →
      ∫ x, ((Levi n z ph x (fun j => f x j)).re - (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) *
          Real.exp (-ph x) ∂vol n z ≤
        (1 + ε) * (∫ x, ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
            Real.exp (-(ph x - 2 * ψ x)) ∂vol n z) +
          ∫ x, sq2 n (sbar n z f x) * Real.exp (-ph x) ∂vol n z
end
end ReciprocityTheory.L2DbarEstimates


