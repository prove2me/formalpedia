-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedCandidates
-- name    : IsRandomnessNecessaryADA_Plain_Supplement_SeedCandidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:00.672214+00:00
-- url     : https://prove2.me/theorems/58dff007-e565-4b32-b291-b369f9564f8e
-- title:
--   Sample–seed consistency and common rows
-- statement:
--   Let $N,M,n,b$ be nonnegative integers, $m$ a private-seed mechanism on $[N]\times[M]$, and $r:[N]\to[M]$ the hidden support locations. For an ordered row-sample $s:[n]\to[N]$, its actual sample is $S_r(s)_t=(s_t,r_{s_t})$. For a real transcript $T$, define
--
--   $$H_T=\{(s,\sigma)\in[N]^n\times\{0,1\}^b:\operatorname{replay}(m_\sigma,S_r(s),\operatorname{queries}(T))=T\}.$$
--
--   After a query $q$ and answer $a$, retain exactly the pairs in $H_T$ with $m_\sigma(S_r(s),T,q)=a$. For any candidate set $H$, a common row appears in at least $8|H|/10$ candidate pairs. A pair counts once for each row present, even if its sample repeats that row. The common-threshold-path predicate equates the common set of the published threshold path with these computed common rows. These are computations only: no bound, separation property or reachability is assumed. At $H=\varnothing$ every row is common under the literal weak inequality; counting arguments apply to nonempty survivor sets.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, Is Randomness Necessary for Adaptive Data Analysis?, STOC 2027 submission #267 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf, §4.5, p.15 (PDF p.15); Definitions 2.1–2.2, pp.7–8; supporting conventions §§3–4.4, pp.8–14.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedProtocol
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Supplement

/-- Section 4.5, p.15: every ordered row-sample and private seed is replayed separately. -/
noncomputable def seededSurvivors {N M n b : ℕ}
    (m : SeedMechanism (Fin N × Fin M) n b) (r : Locations N M)
    (T : Transcript (StatisticalQuery (Fin N × Fin M))) :
    Finset ((Fin n → Fin N) × PrivateSeed b) := by
  classical
  exact Finset.univ.filter (fun c => Consistent (m c.2) (rowSample r c.1) T)

noncomputable def seededNextSurvivors {N M n b : ℕ}
    (m : SeedMechanism (Fin N × Fin M) n b) (r : Locations N M)
    (T : Transcript (StatisticalQuery (Fin N × Fin M)))
    (q : StatisticalQuery (Fin N × Fin M)) (a : ℝ) :
    Finset ((Fin n → Fin N) × PrivateSeed b) := by
  classical
  exact (seededSurvivors m r T).filter (fun c => m c.2 (rowSample r c.1) T q = a)

/-- A pair contributes once for a row, even when that row repeats in its sample. -/
noncomputable def seededCommonRows {N n b : ℕ}
    (H : Finset ((Fin n → Fin N) × PrivateSeed b)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i =>
    (8 / 10 : ℝ) * H.card ≤ (H.filter (fun c => ∃ t, c.1 t = i)).card)

/-- Reuses Definition 3.2's path without changing the published definition. -/
noncomputable def IsSeededCommonThresholdPath {N n b : ℕ}
    (H : Finset ((Fin n → Fin N) × PrivateSeed b)) (p : ThresholdPath N) : Prop :=
  p.common = seededCommonRows H

end IsRandomnessNecessaryADA.Plain.Supplement


