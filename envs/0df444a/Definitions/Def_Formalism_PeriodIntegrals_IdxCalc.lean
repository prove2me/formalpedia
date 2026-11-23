-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
-- name    : Formalism_PeriodIntegrals_IdxCalc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:25.433649+00:00
-- url     : https://prove2.me/theorems/95ddba96-bd42-4b88-97f1-cfcdc825baa8
-- title:
--   Idx Calc
-- statement:
--   Definitions and structural lemmas for Idx Calc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/IdxCalc.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv
open Formalism.BasicNotions NumberField IsDedekindDomain
def IdxCalc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V),
    M.FG → N.FG → Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
    lenAt w M N ≠ ⊤ ∧
    (∀ P : Submodule (𝓞 K) V, P.FG → Submodule.span K (P : Set V) = Submodule.span K (N : Set V) →
      idxAt w M P = idxAt w M N + idxAt w N P) ∧
    (∀ (V' : Type) [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
      (φ : V →ₗ[K] V'),
      idxAt w M N =
        idxAt w (M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) (N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) +
        idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K)))) ∧
    (∀ F : ℕ, LocLe w F N M → (F : ℤ) * (Formalism.HN.rkK M : ℤ) ≤ idxAt w M N) ∧
    (∀ F : ℕ, idxAt w M ((w.asIdeal ^ F) • M) = (F : ℤ) * (Formalism.HN.rkK M : ℤ)) ∧
    (∀ n : ℕ, 0 < n → N ≤ M → (∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) →
      idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K))
end PI.Dv


