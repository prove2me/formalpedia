-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:35.130661+00:00
-- url     : https://prove2.me/theorems/1b0b8efb-62d0-4b0a-92ca-25f70b7f83cf
-- title:
--   Psi Exists Statement
-- statement:
--   Definitions and structural lemmas for Psi Exists Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PsiExistsStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)
def cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Z + Jm ε * Zᴴ * Jm ε)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def SmoothOnGV (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUJ ε g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g
def RdV (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
def EcV (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (cpart1 ε Z) f g + Complex.I • RdV (cpart2 ε Z) f g
def EabV (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  EcV ε (Matrix.single a b 1) f
def casimirV (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => ∑ a, ∑ b, EabV ε a b (EabV ε b a f) g
def q0 (ε : Fin n → Bool) : ℕ := min (pOf ε) (qOf ε)
def IsHCParam (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)
structure KType (ε : Fin n → Bool) (Λ : Fin n → ℝ) where
  V : Type
  [instNACG : NormedAddCommGroup V]
  [instIPS : InnerProductSpace ℂ V]
  [instFD : FiniteDimensional ℂ V]
  [instCS : CompleteSpace V]
  τ : KG ε →* unitary (V →L[ℂ] V)
  cont : Continuous τ
  irred : ∀ W : Submodule ℂ V,
    (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) → W = ⊥ ∨ W = ⊤
  dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)
  hasDeriv : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0
  w : V
  w_norm : ‖w‖ = 1
  w_wt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w
  w_hw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0
attribute [instance] KType.instNACG KType.instIPS KType.instFD KType.instCS
abbrev KType.op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V :=
  ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)
def PsiExistsStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ))
def trivialKType (ε : Fin n → Bool) : KType ε 0 where
  V := ℂ
  τ := 1
  cont := continuous_const
  irred := fun W _ => Ideal.eq_bot_or_top W
  dτ := 0
  hasDeriv := fun _ _ _ _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ →L[ℂ] ℂ)
  w := 1
  w_norm := by simp
  w_wt := fun a => by simp
  w_hw := fun _ _ _ _ => by simp
end ReciprocityTheory.ChartRestriction.DS.S7


