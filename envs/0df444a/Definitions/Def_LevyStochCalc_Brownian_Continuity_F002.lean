-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_Continuity_F002
-- name    : LevyStochCalc_Brownian_Continuity_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:14:37.01665+00:00
-- url     : https://prove2.me/theorems/01b6421c-9eb0-486a-a151-4788e767a3be
-- title:
--   Source declarations: LevyStochCalc.Brownian.Continuity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.Continuity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
import Definitions.Def_SourceProof_00d6535be52148842f88e973
import Definitions.Def_SourceProof_c5c83cf022c9fd5765bb05bb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `X̃` with continuous paths.*

The sub-lemmas of the proof live in two imported modules of the same namespace:
`LevyStochCalc.Brownian.ContinuityDyadicChaining` (Hölder extension from a dense
set, the dyadic rationals, dyadic truncation and the deterministic chaining
bound) and `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` (the Markov tail
bound, the per-level Borel-Cantelli estimates, almost-sure local Hölder
regularity and the modification identity). This module assembles them into
`kolmogorovChentsov_modification` and applies it to Brownian motion, whose
fourth increment moment is computed here from the Gaussian moment generating
function.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Continuous modification of a Brownian-increment process.** Any
real-valued process whose increments have the Brownian law
`(W_t − W_s) ~ 𝒩(0, t − s)` admits a continuous modification.

Proof structure:
* The Gaussian fourth moment identity (via `gaussianReal_fourth_moment`)
  gives `𝔼[(X_t − X_s)^4] = 3 (t − s)^2`, so the process satisfies
  `IsKolmogorovProcess` with `p = 4`, `q = 2`, `M = 3`.
* Apply `kolmogorovChentsov_modification` with `q = 2 > 1`.

The hypothesis `h_increment` is stated for **all** real `s < t` (no
nonnegativity constraint). This is consistent with a two-sided BM and is
required because the Kolmogorov bound must hold for all `s, t : ℝ`. -/
theorem brownian_continuous_modification
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have h_kolmogorov :
      ProbabilityTheory.IsKolmogorovProcess X P 4 2 3 :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
      h_meas
      (h_kol := ?_)
      (hp := by norm_num) (hq := by norm_num)
  · exact _root_.Prove2MeSourceProof.h_00d6535be52148842f88e973 P X h_kolmogorov (by norm_num)
  · -- Sub-goal: ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2.
    intro s t
    -- The Kolmogorov condition uses ENNReal rpow `^ (4 : ℝ)`, but our aux
    -- uses Nat pow `^ (4 : ℕ)`. Bridge via `ENNReal.rpow_natCast`.
    have h_rpow_nat : ∀ ω, edist (X s ω) (X t ω) ^ (4 : ℝ)
        = edist (X s ω) (X t ω) ^ (4 : ℕ) := fun ω => by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
    have h_int_eq :
        (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℝ) ∂P)
          = ∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℕ) ∂P := by
      apply lintegral_congr
      exact h_rpow_nat
    have h_rhs : edist s t ^ (2 : ℝ) = edist s t ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
    rw [h_int_eq, h_rhs]
    rcases lt_trichotomy s t with hst | hst | hst
    · -- Case s < t. Use brownian_increment_fourth_moment.
      exact _root_.Prove2MeSourceProof.h_c5c83cf022c9fd5765bb05bb X h_meas h_increment hst
    · -- Case s = t. Both sides = 0.
      subst hst
      simp
    · -- Case s > t. By symmetry of edist, reduce to t < s.
      have h_swap : (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℕ) ∂P)
          = ∫⁻ ω, edist (X t ω) (X s ω) ^ (4 : ℕ) ∂P := by
        apply lintegral_congr
        intro ω
        rw [edist_comm]
      rw [h_swap, edist_comm s t]
      exact _root_.Prove2MeSourceProof.h_c5c83cf022c9fd5765bb05bb X h_meas h_increment hst
end LevyStochCalc.Brownian.Continuity


