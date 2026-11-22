-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
-- name    : Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:20.287508+00:00
-- url     : https://prove2.me/theorems/94afd8da-4189-4439-93b7-eaefa6997b2d
-- title:
--   Swapped Parity Series Binomial Form
-- statement:
--   Definitions and structural lemmas for Swapped Parity Series Binomial Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
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
open MvPowerSeries Formalism.IncomingBounds
section Blocks
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
def bnxA (a b : ZMod d → K) (s : ZMod d) : MvPowerSeries (V2 d) K :=
  C (a s) * X (false, s) + C (b s) * X (true, s)
def bnxRes (m : V2 d →₀ ℕ) (s : ZMod d) : V2 d →₀ ℕ :=
  Finsupp.single (false, s) (m (false, s)) + Finsupp.single (true, s) (m (true, s))
end Blocks
section Subst
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
def bnxN (m : V2 d →₀ ℕ) : ZMod d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun s => m (false, s) + m (true, s)
def bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) : V2 d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => if x.1 then n x.2 - k x.2 else k x.2
end Subst
section De
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end De
section NormNat
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end NormNat
section Sides
variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]
end Sides
end Formalism.DworkPowerSeriesWeights


