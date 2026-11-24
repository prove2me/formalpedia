-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
-- name    : Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:50.800156+00:00
-- url     : https://prove2.me/theorems/79be0b0d-c87d-40ae-abb0-3cb9aed90338
-- title:
--   First Row Minor Degree Le One
-- statement:
--   Definitions and structural lemmas for First Row Minor Degree Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open MvPolynomial
section Slices
variable {R : Type u} [CommRing R] {T σ ρ : Type}
def bSlice (e : T × σ → ρ) (he : Function.Injective e) (t : T) (κ : ρ →₀ ℕ) : σ →₀ ℕ :=
  κ.comapDomain (fun y => e (t, y)) (fun _ _ _ _ h => (Prod.mk.inj (he h)).2)
end Slices
section Rows
end Rows
section Jets
end Jets
section Sums
end Sums
section Frames
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}
def bM (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then ((x (false, τ.2))⁻¹).transpose else x (false, τ.2)
def bT (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then x τ * (x (false, τ.2)).transpose else 1
def bE (H : Type) (N0 N1 : ℕ) : (Bool × H) × (Fin N0 × Fin N1) → Bool × H × Fin N0 × Fin N1 :=
  fun w => (w.1.1, w.1.2, w.2)
def bA [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K) :
    (Bool × H × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → K :=
  fun y z => if z.1 = (y.1, y.2.1) ∧ z.2.2 = y.2.2.2 then bM x z.1 y.2.2.1 z.2.1 else 0
end Frames
section Norms
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}
end Norms
end Formalism.DworkPowerSeriesWeights


