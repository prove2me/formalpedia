-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
-- name    : Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:54.409248+00:00
-- url     : https://prove2.me/theorems/6dfb8f7e-465a-44e2-825a-08e043fd2b9e
-- title:
--   Constant Coeff Quad Ser
-- statement:
--   Definitions and structural lemmas for Constant Coeff Quad Ser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
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
section Analytic
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
def dirD (L : ι → K) : Derivation K (MvPowerSeries ι K) (MvPowerSeries ι K) :=
  ∑ x, L x • MvPowerSeries.pderiv K x
def linSer (c : ι → ι → K) (L : ι → K) : MvPowerSeries ι K :=
  ∑ x, ∑ y, MvPowerSeries.C (c x y) *
    (MvPowerSeries.C (L x) * MvPowerSeries.X y + MvPowerSeries.C (L y) * MvPowerSeries.X x)
end Analytic
section Exp
variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]
end Exp
section Comb
variable {n : ℕ}
def invOn (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i)
variable {R : Type u} [CommRing R]
def edgeW (w : Fin n → Fin n → R) (σ : Equiv.Perm (Fin n)) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)
end Comb
section Main
variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]
end Main
end Formalism.DworkPowerSeriesWeights


