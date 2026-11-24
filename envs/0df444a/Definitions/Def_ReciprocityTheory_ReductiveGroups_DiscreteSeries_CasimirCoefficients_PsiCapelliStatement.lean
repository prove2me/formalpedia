-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:25.791734+00:00
-- url     : https://prove2.me/theorems/4b5ac942-ccf9-4118-9d18-a6c8e3bb3664
-- title:
--   Psi Capelli Statement
-- statement:
--   Definitions and structural lemmas for Psi Capelli Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PsiCapelliStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
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
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def negL (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => -Lhol (Matrix.single a b 1) F z
def PsiCapelliStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ), IsMu lam μ →
    ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (PsiM T μ) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • PsiM T μ g
def PsiAllCapStatement (n : ℕ) : Prop :=
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
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        opGelfand (rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        opGelfand (rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) ∧
      (∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
end ReciprocityTheory.ChartRestriction.DS.S7


