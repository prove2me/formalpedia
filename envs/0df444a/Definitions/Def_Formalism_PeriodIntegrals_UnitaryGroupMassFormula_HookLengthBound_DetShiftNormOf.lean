-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:30.298648+00:00
-- url     : https://prove2.me/theorems/b460ff4c-892b-49b1-a339-1732702a616f
-- title:
--   Det Shift Norm Of
-- statement:
--   Definitions and structural lemmas for Det Shift Norm Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DetShiftNormOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.HookSteps
open MvPolynomial Formalism.GradedWeylDivisibility
def detX (N : ℕ) : MvPolynomial (Fin N × Fin N) ℚ :=
  (Matrix.of fun a b : Fin N => (X (a, b) : MvPolynomial (Fin N × Fin N) ℚ)).det
def MulXAdj : Prop :=
  ∀ (σ : Type) (v : σ) (f g : MvPolynomial σ ℚ), fockQ (X v * f) g = fockQ f (pderiv v g)
def RenameIso : Prop :=
  ∀ (σ τ : Type) (φ : σ → τ), Function.Injective φ → ∀ f g : MvPolynomial σ ℚ,
    fockQ (rename φ f) (rename φ g) = fockQ f g
def HwDetMul : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    hw ℚ le_rfl (fun i => ν i + 1) = detX N * hw ℚ le_rfl ν
def HwLastZero : Prop :=
  ∀ (n : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = 0 →
    hw ℚ le_rfl ν =
      rename (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) (hw ℚ le_rfl (fun i : Fin n => ν (Fin.castSucc i)))
def polE (N : ℕ) (a b : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  ∑ s : Fin N, LinearMap.mulLeft ℚ (X (a, s)) ∘ₗ (pderiv (b, s) : Derivation ℚ _ _).toLinearMap
def detD (N : ℕ) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin N => ((pderiv (σ j, j) : Derivation ℚ _ _).toLinearMap :
      Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))).prod
def DetAdj : Prop :=
  ∀ (N : ℕ) (f g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (detX N * f) g = fockQ f (detD N g)
def PolRel : Prop := ∀ N : ℕ, Formalism.CohomologicalDescent.HeightDescentMinors.GlRel (polE N)
def DetDetId : Prop :=
  ∀ N : ℕ, LinearMap.mulLeft ℚ (detX N) * detD N =
    Formalism.CohomologicalDescent.HeightDescentMinors.capelli (polE N) (algebraMap ℚ _ ((N : ℚ) - 1))
def PolEqRowDiv : Prop :=
  ∀ (N : ℕ) (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ), polE N a b f = rowDiv ℚ a b 1 f
def DetShiftNorm : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    fockQ (detX N * hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν) =
      (∏ i : Fin N, ((ν i + N - i : ℕ) : ℚ)) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)
def HookNorm : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ) =
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ)
def DetShiftNormOf : Prop := DetAdj → DetDetId → PolEqRowDiv → HwDetMul → DetShiftNorm
def HookNormOf : Prop := RenameIso → HwDetMul → HwLastZero → DetShiftNorm → HookNorm
def HookBoundOf : Prop := HookNorm → PI.HookBound
end PI.HookSteps


