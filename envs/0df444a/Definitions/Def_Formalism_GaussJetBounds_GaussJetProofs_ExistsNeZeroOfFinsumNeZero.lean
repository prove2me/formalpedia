-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
-- name    : Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:25.443483+00:00
-- url     : https://prove2.me/theorems/3ca2bedf-a0ae-4b19-b9d2-43baad0e2d59
-- title:
--   Exists Ne Zero Of Finsum Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Of Finsum Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ExistsNeZeroOfFinsumNeZero.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
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
universe u v w
namespace Formalism.DworkPowerSeriesWeights
namespace ExponentialDerivativeInverse
section Sub
variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}
def InSub (K0 : Subfield K) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ∈ K0
end Sub
section Wt
variable {K : Type u} [NormedField K] {ι : Type v}
def wsum (w : ι → ℤ) (n : ι →₀ ℕ) : ℤ := n.sum fun x k => (k : ℤ) * w x
def HomW (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → wsum w n = c
def CongW (N : ℤ) (w : ι → ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → N ∣ wsum w n
variable {w : ι → ℤ}
variable {N : ℤ}
end Wt
section Torus
variable {K : Type u} [NormedField K] {d : ℕ}
end Torus
section Diff
variable {K : Type u} [NormedField K] {d : ℕ}
def Good (K0 : Subfield K) (N : ℤ) (w : V2 d → ℤ) (f : MvPowerSeries (V2 d) K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ InSub K0 f ∧ CongW N w f
def Fam (K0 : Subfield K) (l : ℕ) (a : ZMod d → MvPowerSeries (V2 d) K) : Prop :=
  ∀ s, MvPowerSeries.constantCoeff (a s) = 0 ∧ InSub K0 (a s) ∧
    HomW (fun x : V2 d => lw l x.2) (lw l s) (a s)
variable {K0 : Subfield K} {l : ℕ}
end Diff
end ExponentialDerivativeInverse
end Formalism.DworkPowerSeriesWeights


