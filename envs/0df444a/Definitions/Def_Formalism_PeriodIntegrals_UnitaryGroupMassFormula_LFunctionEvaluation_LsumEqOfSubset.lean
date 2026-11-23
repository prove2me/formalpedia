-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:05.652311+00:00
-- url     : https://prove2.me/theorems/cd237eff-a167-4580-95cc-82938774604e
-- title:
--   Lsum Eq Of Subset
-- statement:
--   Definitions and structural lemmas for Lsum Eq Of Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WwEvalWork
open MvPolynomial
section Lsum
variable {σ K : Type*} [CommRing K]
def Lsum (w : (σ →₀ ℕ) → K) (Q : MvPolynomial σ K) : K :=
  ∑ α ∈ Q.support, coeff α Q * w α
end Lsum
section Peval
variable {σ1 σ2 K : Type*} [CommRing K]
def peval (x : σ1 → K) : MvPolynomial (σ1 ⊕ σ2) ℤ →+* MvPolynomial σ2 K :=
  eval₂Hom (C.comp (Int.castRingHom K)) (Sum.elim (fun v => C (x v)) X)
end Peval
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}
def wt (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (α : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    ℂ_[l] :=
  (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th
end PI.WwEvalWork


