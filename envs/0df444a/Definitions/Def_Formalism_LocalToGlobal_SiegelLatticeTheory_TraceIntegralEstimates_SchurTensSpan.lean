-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:20.810653+00:00
-- url     : https://prove2.me/theorems/ca661437-df32-4f8d-94bc-6286e290d1f8
-- title:
--   Schur Tens Span
-- statement:
--   Definitions and structural lemmas for Schur Tens Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
section Gen
variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
def SP (m : Measure K) (σs : K → (Hs →L[ℂ] Hs)) (D : ℝ) (a b a' b' : Hs) : Prop :=
  Integrable (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) m ∧
    ∫ x, ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ ∂m = ⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ)
variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
end Gen
section Pure
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}
end Pure
end Formalism.L2.S.Pv.SchurTens


