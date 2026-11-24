-- Prove2me | Definitions.Def_SourceProof_1aa8fa3c0942e35b7eee3422
-- name    : SourceProof_1aa8fa3c0942e35b7eee3422
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:44:46.287819+00:00
-- url     : https://prove2.me/theorems/d4e5c4af-038c-406b-b505-4618a7303e8b
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.exists_integrable_closing

import Definitions.Def_StochLean_Probability_Process_Filtration_Reindex_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_557b326145f3a25cf73cd318
import Definitions.Def_SourceProof_5a705a1f4d32da63ab0f4ee7
import Mathlib.Probability.Martingale.Convergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Closing a continuous-time uniformly integrable martingale

An integer-time restriction supplies an actual integrable terminal variable.
The tower property then closes every real-time coordinate. This implication
requires no path regularity; the almost-sure limit over the entire half-line
is a separate assertion, not confused with convergence along the integers.

Source: the closed/UI equivalence in Protter I.13 (martingale part).
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]


theorem _root_.Prove2MeSourceProof.h_1aa8fa3c0942e35b7eee3422 (hX : Martingale X F P) (hu : UniformIntegrable X 1 P) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ ∀ t, X t =ᵐ[P] P[Z | F t] := by
  let e : ℕ → ℝ≥0 := Nat.cast
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hm : Martingale (fun n ↦ X (e n)) G P := (_root_.Prove2MeSourceProof.h_557b326145f3a25cf73cd318 hX) e he
  have hui := (_root_.Prove2MeSourceProof.h_5a705a1f4d32da63ab0f4ee7 hu) e
  let Z := G.limitProcess (fun n ↦ X (e n)) P
  obtain ⟨C, hC⟩ := hui.2.2
  have hi : Integrable Z P := (hm.submartingale.memLp_limitProcess hC).integrable le_rfl
  refine ⟨Z, hi, fun t ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hmZ : X (e n) =ᵐ[P] P[Z | F (e n)] := hm.ae_eq_condExp_limitProcess hui n
  exact (hX.condExp_ae_eq hn).symm.trans ((condExp_congr_ae hmZ).trans
    (condExp_condExp_of_le (F.mono hn) (F.le (e n))))
end MeasureTheory.Martingale


