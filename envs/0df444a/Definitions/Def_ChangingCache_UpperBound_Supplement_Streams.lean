-- Prove2me | Definitions.Def_ChangingCache_UpperBound_Supplement_Streams
-- name    : ChangingCache_UpperBound_Supplement_Streams
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:44.019851+00:00
-- url     : https://prove2.me/theorems/ea7506da-917e-4c48-8d4e-a65b4993c83d
-- title:
--   Infinite prefixes, real-speed banks and unbounded makespan ratios
-- statement:
--   For an infinite request stream $\sigma:\mathbb N\to P$, let $\sigma_{<r}$ be its first $r$ requests. A single family $S_r$ of cache snapshots is legal on the stream if it is legal, in the published finite-cache model, on every prefix, with the same snapshots throughout.
--
--   For real speed $s$, profile $m$, and a designated policy $S$, the bank is
--   $$B_s(r)=sF_S(r)-F_{\mathrm{LRU}}(r).$$
--   The predicate for an unbounded makespan ratio means
--   $$\forall R>0\;\exists m,\sigma:\quad F_{\mathrm{OPT}}(\sigma)>0,\qquad
--   F_{\mathrm{LRU}}(\sigma)>R\,s\,F_{\mathrm{OPT}}(\sigma).$$
--   Here $m$ is a positive growth-limited memory profile and $\sigma$ is a nonempty finite list. LRU has memory factor two and the published capacity $2m(\lfloor k/s\rfloor)$ after $k$ misses. Natural page names permit arbitrarily many distinct pages. The ratio condition uses multiplication, so it does not depend on a convention for division by zero.
--
--   These definitions extend the published finite model and supply the common language of the two lower bounds; they impose no new restriction on a policy or profile.
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), pp. 2, 7 (Definition 3.2), 16–17 (Definition 6.1), 24 (Theorem B.1)

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound.Supplement

/-- The first `r` requests of one infinite stream; includes the empty prefix. -/
def streamPrefix {α : Type*} (σ : ℕ → α) (r : ℕ) : List α :=
  (List.range r).map σ

/-- One policy, with the same snapshots on every finite prefix. -/
def IsStreamLegal {α : Type*} [DecidableEq α] (m : ℕ → ℕ)
    (σ : ℕ → α) (S : ℕ → Finset α) : Prop :=
  ∀ r, IsLegal m (streamPrefix σ r) S

/-- Definition 3.2 (= Definition 6.1), with real speed and signed real subtraction. -/
noncomputable def bank {α : Type*} [DecidableEq α] (s : ℝ) (m : ℕ → ℕ)
    (σ : List α) (S : ℕ → Finset α) (r : ℕ) : ℝ :=
  s * (policyMisses σ S r : ℝ) - (lruMissCount (augCap 2 s m) σ r : ℝ)

/-- Unbounded multiplicative makespan ratio, not an additive gap. Natural page names impose
no finite bound on the universe. OPT's denominator is strictly positive. -/
def UnboundedMakespanRatio (s : ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ (m : ℕ → ℕ) (σ : List ℕ),
    IsMemoryProfile m ∧ σ ≠ [] ∧ 0 < optMisses m σ ∧
    R * s * (optMisses m σ : ℝ) < ((lruRun (augCap 2 s m) σ).misses : ℝ)

end ChangingCache.UpperBound.Supplement


