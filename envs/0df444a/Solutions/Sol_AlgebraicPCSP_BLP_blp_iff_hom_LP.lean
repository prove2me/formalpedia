-- Prove2me | solution 1 for AlgebraicPCSP.BLP.blp_iff_hom_LP
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:34:16.004372+00:00
-- url     : https://prove2.me/submissions/b33f271f-6bc0-46b0-9abd-9582503d1aef

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_BLP_LP

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.BLP in
theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (X : Instance τ ar) :
    (∃ w p, IsLPSol X 𝔸 w p) ↔ SatIn X (LP 𝔸) := by
  constructor
  · rintro ⟨w, p, h0, hp0, hpz, hw1, hp1, hmarg⟩
    refine ⟨fun i => ⟨w i, h0 i, hw1 i⟩, fun j => ?_⟩
    exact ⟨p j, hp0 j, hpz j, hp1 j, fun k a => hmarg j k a⟩
  · rintro ⟨σ, hσ⟩
    choose γ hγ0 hγz hγ1 hγm using hσ
    refine ⟨fun i => (σ i).val, γ, fun i a => (σ i).2.1 a, hγ0, hγz, fun i => (σ i).2.2, hγ1, ?_⟩
    intro j k a
    exact hγm j k a
