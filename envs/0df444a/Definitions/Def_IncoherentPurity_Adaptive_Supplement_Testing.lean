-- Prove2me | Definitions.Def_IncoherentPurity_Adaptive_Supplement_Testing
-- name    : IncoherentPurity_Adaptive_Supplement_Testing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:42.286972+00:00
-- url     : https://prove2.me/theorems/d227d7c8-68e7-4c57-82d8-a79afae4a1cb
-- title:
--   Seeded Haar-mixture testing experiment
-- statement:
--   For $d\ge16$ and $0<\varepsilon\le1/576$, compute the two strengths
--
--   $$\theta_0=\frac1{\sqrt d},\qquad\theta_1=\frac{1+8\varepsilon}{\sqrt d}.$$
--
--   Given the published protocol $P$, a copy budget $N$, and the published normalized Haar law, define the testing law under hypothesis $b\in\{0,1\}$ by drawing a single unit direction $v$ and then drawing the entire Born transcript on $\rho_{\theta_b,v}$. The same protocol and its same state-independent seed law are used under either hypothesis. Thus
--
--   $$T_b=\mathbb E_v\,\operatorname{Law}_P(R,Y_1,\ldots,Y_N\mid\rho_{\theta_b,v}).$$
--
--   The seed $R$ is kept in the transcript. When $P$ is non-adaptive, conditioning on both the seed and the one shared direction yields independent outcomes of its preselected POVMs. The direction is not resampled for each copy. These are computed laws, not free transcript measures or KL certificates. This experiment is the testing model in the proof of Proposition 5.4.
--
--   **Formalization Note** Histories retain the published infinite tagged sequence with unused entries fixed. The spike-parameter constructor proves its range from the displayed dimension and precision bounds.
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), preprint, pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce; Section 5, PDF p.17 = printed p.17, Eqs. (5.11)–(5.17)

import Definitions.Def_IncoherentPurity_Adaptive_Supplement_Spike

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive.Supplement

/-- The two spike strengths used in Proposition 5.4. -/
def testStrength (d : ℕ) (ε : ℝ) (b : Bool) : ℝ :=
  (if b then 1 + 8*ε else 1) / Real.sqrt d

/-- A constructor check on the proof-supported range, not a promise about an unknown state. -/
def testParameter {d : ℕ} (hd : 16 ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ 1/576) (b : Bool) : Set.Icc (0 : ℝ) 1 := by
  have hd' : (16 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hs4 : 4 ≤ Real.sqrt (d : ℝ) := by nlinarith
  refine ⟨testStrength d ε b, ?_⟩
  cases b <;> simp only [testStrength, Bool.false_eq_true, ↓reduceIte]
  · constructor
    · positivity
    · apply (div_le_one (by linarith : 0 < Real.sqrt (d : ℝ))).2
      linarith
  · constructor
    · positivity
    · apply (div_le_one (by linarith : 0 < Real.sqrt (d : ℝ))).2
      linarith

/-- The experiment (5.13)--(5.16): draw ONE Haar direction, then the entire published
Born transcript with its independent classical seed. The seed remains in the transcript.
For `IsNonadaptive P`, all the measurement choices depend only on that seed; conditioning
on seed and direction therefore gives the product of the preselected single-copy laws. -/
def testingLaw {d : ℕ} (hd : 16 ≤ d) (H : HaarBasis d) (P : Protocol d)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ 1/576) (b : Bool) :
    Measure (P.Seed × (ℕ → (Unit ⊕ P.Outcome))) :=
  let hpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 16) hd
  (directionHaar hpos H).bind (fun v =>
    transcriptLaw P (spikeState hpos (testParameter hd ε hε hsmall b) v) N)

end IncoherentPurity.Adaptive.Supplement


