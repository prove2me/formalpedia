-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope
-- name    : ConsistentSubmodular_Deterministic_Certificates_Envelope
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:46.929337+00:00
-- url     : https://prove2.me/theorems/8cbbf3dc-4996-4d02-85d9-605119723470
-- title:
--   Raw envelope of an atomic profile: later active stages, raw numerator, raw ratio, ratio set and maximum
-- statement:
--   For an atomic profile $P$ with stages $0,\dots,m$ (baseline $L_t$, residuals $r_{i,t}$, designated mass $A_t=r_{t,t}$, benchmark $B_t=L_t+A_t$, and `Active` as in the actual constructor), fix a stage $h$. The file defines:
--
--   - `laterActive` $h$: the finite set of stages $t$ with $h<t$ and $t$ active.
--   - `rawNumerator` $h\,t$:
--   $$N_{h,t}=4(A_t-r_{h,t})-(B_t-A_h)-3(1-A_h).$$
--   - `rawRatio` $h\,t$: $N_{h,t}/(A_h-r_{h,t})$. This is Lean division, so it equals $0$ when the denominator is $0$.
--   - `ratioSet` $h$: the finite set $\{0\}\cup\{\text{rawRatio}\,h\,t : t\in\text{laterActive}\,h\}$, which always contains $0$ and is therefore nonempty.
--   - `rawEnvelope` $h$: the maximum of `ratioSet` $h$, so $\mathrm{rawEnvelope}(h)=\max\big(\{0\}\cup\{N_{h,t}/(A_h-r_{h,t})\}\big)$.
--
--   The file also proves that the envelope is nonnegative and bounds every raw ratio of a later active stage; that denominators $A_h-r_{h,t}$ are nonnegative for $h\le t$ and that rows with zero denominator have nonpositive numerator (canonical profiles); that the envelope satisfies the slack inequality $0\le\mathrm{envelopeSlack}\,h\,(\mathrm{rawEnvelope}\,h)\,t$ at every later active stage, including rows with zero denominator; and that raw ratios, hence the envelope, are strictly below $3$ under a strictness hypothesis.
--
--   The envelope is the smallest mass parameter making every later active row of the actual constructor safe. It supplies the parameter $q$ of the two-vertex mixture in the deterministic $3/4$ certificate construction (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Envelope.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualConstructor

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

def laterActive (h : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (fun t => h < t ∧ P.Active t)

def rawNumerator (h t : Fin (m + 1)) : ℝ :=
  4 * (P.designated t - P.residual h t) - (P.benchmark t - P.designated h) -
    3 * (1 - P.designated h)

def rawRatio (h t : Fin (m + 1)) : ℝ :=
  P.rawNumerator h t / (P.designated h - P.residual h t)

def ratioSet (h : Fin (m + 1)) : Finset ℝ := by
  classical
  exact insert 0 ((P.laterActive h).image (P.rawRatio h))

theorem ratioSet_nonempty (h : Fin (m + 1)) : (P.ratioSet h).Nonempty := by
  classical
  exact ⟨0, Finset.mem_insert_self _ _⟩

def rawEnvelope (h : Fin (m + 1)) : ℝ :=
  (P.ratioSet h).max' (P.ratioSet_nonempty h)

theorem rawEnvelope_nonnegative (h : Fin (m + 1)) : 0 ≤ P.rawEnvelope h := by
  classical
  exact Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem rawRatio_le_envelope (h t : Fin (m + 1)) (ht : t ∈ P.laterActive h) :
    P.rawRatio h t ≤ P.rawEnvelope h := by
  classical
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

theorem raw_denominator_nonnegative (h t : Fin (m + 1)) (hht : h ≤ t) :
    0 ≤ P.designated h - P.residual h t := by
  have hmono := P.residual_antitone h hht
  change P.residual h t ≤ P.designated h at hmono
  exact sub_nonneg.mpr hmono

theorem raw_zero_denominator (hP : P.Canonical) (h t : Fin (m + 1)) (hht : h ≤ t)
    (hz : P.designated h - P.residual h t = 0) : P.rawNumerator h t ≤ 0 := by
  have hgt := P.designated_antitone hP hht
  have hr := hP.2 t h
  have hA := P.designated_le_one hP h
  have hL := P.baseline_nonnegative t
  unfold rawNumerator benchmark
  linarith

/-- The envelope inequality includes rows with denominator zero. -/
theorem rawEnvelope_valid (hP : P.Canonical) (h t : Fin (m + 1))
    (ht : t ∈ P.laterActive h) : 0 ≤ P.envelopeSlack h (P.rawEnvelope h) t := by
  classical
  have hht : h ≤ t := le_of_lt ((Finset.mem_filter.mp ht).2.1)
  have hden := P.raw_denominator_nonnegative h t hht
  by_cases hz : P.designated h - P.residual h t = 0
  · have hnum := P.raw_zero_denominator hP h t hht hz
    have hmul := congrArg (fun x : ℝ => P.rawEnvelope h * x) hz
    unfold envelopeSlack rawNumerator at *
    nlinarith only [hnum, hmul]
  · have hd : 0 < P.designated h - P.residual h t := lt_of_le_of_ne hden (Ne.symm hz)
    have hr := P.rawRatio_le_envelope h t ht
    have hbound := (div_le_iff₀ hd).mp hr
    unfold rawNumerator at hbound
    unfold envelopeSlack
    nlinarith only [hbound]

theorem rawRatio_lt_three (hP : P.Canonical) (h t : Fin (m + 1)) (hht : h ≤ t)
    (hstrict : P.designated h < 1 ∨ P.designated t < P.designated h) :
    P.rawRatio h t < 3 := by
  have hd := P.raw_denominator_nonnegative h t hht
  by_cases hz : P.designated h - P.residual h t = 0
  · simp [rawRatio, hz]
  have hdpos := lt_of_le_of_ne hd (Ne.symm hz)
  apply (div_lt_iff₀ hdpos).mpr
  have hper := P.baseline_add_residual_monotone h hht
  change P.baseline h + P.designated h ≤ P.baseline t + P.residual h t at hper
  have hL := P.baseline_nonnegative h
  have hA := P.designated_le_one hP h
  have hgt := P.designated_antitone hP hht
  unfold rawNumerator benchmark
  rcases hstrict with h | h <;> linarith

theorem rawEnvelope_lt_three (hP : P.Canonical) (h : Fin (m + 1))
    (hstrict : ∀ t, t ∈ P.laterActive h →
      P.designated h < 1 ∨ P.designated t < P.designated h) :
    P.rawEnvelope h < 3 := by
  classical
  apply (Finset.max'_lt_iff _ _).mpr
  intro r hr
  rcases Finset.mem_insert.mp hr with hr | hr
  · rw [hr]
    norm_num
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    exact P.rawRatio_lt_three hP h t
      (le_of_lt (Finset.mem_filter.mp ht).2.1) (hstrict t ht)

end AtomicProfile

end ConsistentSubmodular

end


