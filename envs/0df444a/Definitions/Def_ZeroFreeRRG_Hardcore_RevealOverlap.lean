-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_RevealOverlap
-- name    : ZeroFreeRRG_Hardcore_RevealOverlap
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:23:08.774368+00:00
-- url     : https://prove2.me/theorems/baa05a75-02d9-4267-aaed-acffb6d7d3be
-- title:
--   Revealed and full overlap deviations
-- statement:
--   The revealed-overlap event H compares each revealed pair-spin count with the product-prior mean at threshold sηn/2; the full-overlap event records entrywise deviation larger than η.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
open scoped Classical BigOperators
namespace ZeroFreeRRG.Hardcore

/-- Revealed deviation event H from the proof of Lemma 5.6. -/
noncomputable def revealedOverlapH (m : Model) (t s η : ℝ) {n : ℕ} (U : Finset (Fin n))
    (y y' : {v : Fin n // v ∈ U} → m.Spin) : Prop :=
  ∃ ab : m.Spin × m.Spin, s*η*n/2 ≤
    |∑ v : {v : Fin n // v ∈ U},
      ((if y v = ab.1 ∧ y' v = ab.2 then (1:ℝ) else 0) - m.pi t ab.1 * m.pi t ab.2)|

/-- Whether the full empirical overlap lies outside the eta box. -/
noncomputable def fullOverlapDeviation (m : Model) (t η : ℝ) {n : ℕ}
    (σ σ' : Fin n → m.Spin) : Prop :=
  ∃ ab : m.Spin × m.Spin, η < |overlap σ σ' ab - m.pi t ab.1 * m.pi t ab.2|

end ZeroFreeRRG.Hardcore


