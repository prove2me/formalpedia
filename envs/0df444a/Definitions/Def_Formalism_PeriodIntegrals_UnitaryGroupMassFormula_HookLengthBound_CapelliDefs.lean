-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:44.574381+00:00
-- url     : https://prove2.me/theorems/ad385a89-6813-4879-8391-f1d19d3eb612
-- title:
--   Capelli Defs
-- statement:
--   Definitions and structural lemmas for Capelli Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
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
namespace PI.HookSteps.Cap
open MvPolynomial
section Abs
variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]
def xw (x : I → S → 𝒰) {k : ℕ} (r : Fin k → I) (s : Fin k → S) : 𝒰 :=
  (List.ofFn fun j => x (r j) (s j)).prod
def dw (d : I → S → 𝒰) {k : ℕ} (g : Fin k → I) (s : Fin k → S) : 𝒰 :=
  (List.ofFn fun j => d (g j) (s j)).prod
def Pn (x d : I → S → 𝒰) {k : ℕ} (r g : Fin k → I) : 𝒰 :=
  ∑ s : Fin k → S, xw x r s * dw d g s
def Eop (x d : I → S → 𝒰) (a b : I) : 𝒰 := ∑ t : S, x a t * d b t
def Lw (x d : I → S → 𝒰) {k : ℕ} (r g : Fin k → I) : 𝒰 :=
  (List.ofFn fun j : Fin k =>
    Eop x d (r j) (g j) + if r j = g j then ((k : 𝒰) - 1 - ((j : ℕ) : 𝒰)) else 0).prod
end Abs
def CapAbsMain : Prop :=
  ∀ (𝒰 : Type) [Ring 𝒰] (I S : Type) [DecidableEq I] [Fintype S] [DecidableEq S]
    (x d : I → S → 𝒰), (∀ a s b t, x a s * x b t = x b t * x a s) →
    (∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) →
    ∀ (k : ℕ) (r g : Fin k → I),
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (Lw x d (fun j => r (σ j)) g - Pn x d (fun j => r (σ j)) g) = 0
def xo (N : ℕ) (a s : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  LinearMap.mulLeft ℚ (X (a, s))
def dop (N : ℕ) (b s : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  (pderiv (b, s) : Derivation ℚ _ _).toLinearMap
def CapSquare : Prop :=
  ∀ N : ℕ, LinearMap.mulLeft ℚ (detX N) * detD N =
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • Pn (xo N) (dop N) (fun j => σ j) id
def CapLeft : Prop :=
  ∀ N : ℕ, Formalism.CohomologicalDescent.HeightDescentMinors.capelli (polE N) (algebraMap ℚ _ ((N : ℚ) - 1)) =
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • Lw (xo N) (dop N) (fun j => σ j) id
def CapRel : Prop :=
  ∀ N : ℕ, (∀ a s b t, xo N a s * xo N b t = xo N b t * xo N a s) ∧
    (∀ a s b t, dop N b t * xo N a s = xo N a s * dop N b t + if a = b ∧ s = t then 1 else 0)
end PI.HookSteps.Cap


