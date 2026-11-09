-- Prove2me | Definitions.Def_PaceSSSP517_Certified_Resources
-- name    : PaceSSSP517_Certified_Resources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:42.636423+00:00
-- url     : https://prove2.me/theorems/72806fae-eb5f-4fd2-b5f4-920fafae02c8
-- title:
--   One-pass spanner interface and retained and transient word banks
-- statement:
--   The external spanner primitive consumes an arbitrary edge stream by a single state fold. Its start state receives only $n,k,\varepsilon$; its feed receives one endpoint pair and its real weight. The interface requires the resulting $(2k-1+\varepsilon)$-spanner and both size and peak workspace bounded by
--
--   $$C_H\varepsilon^{-1}n^{1+1/k}\ln n,$$
--
--   where $C_H>0$ is fixed before every input. This is the one-pass construction invoked in §3.1, independently supplied by Assadi–Hoppenworth–Sundaresan, Proposition 3.2, citing FKM+05/JKMV24: https://arxiv.org/html/2507.17841v2#S3 . It is not a PACE success assumption. There is no invented numerical value for $C_H$.
--
--   The physical layout counts three words per stored edge (endpoints and weight), one per profile coordinate and four scalar metadata words per old round. Pass A additionally reserves the current sample, six words per retained edge for local adjacency, and eight words per vertex for the local calculation and output. Pass B releases the sample and adjacency workspace, retains the current tree/profile, allocates two arrays of length $r$ for suffix aggregation, and scans with a bounded violator buffer. Once its half-budget threshold is exceeded, that buffer is freed for the remainder of the pass. Both phases reserve sixteen scalar words. The peak is the maximum of these allocated banks over every executed round and the spanner pass. No bank stores all $m$ edge weights or old samples.
--
--   Let $V_R$ be the sum of cardinalities of the bulk violator sets actually committed before stopping, and let $f_e$ count executed rounds in which $e$ fails. Pass count is $2R+1$. These are measurements of the transition trace. No bound on them, and no successful stopping assertion, is a defining field.
--
--   **Formalization Note** Exact real weights, distances and arithmetic values each occupy one word in the paper's word model. Ghost trace samples are used solely to reconstruct transient allocations; they are never physically retained after Pass A. Subsequent pass orders are arbitrary lists containing each edge once.
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), pp. 5–6, §3.1 spanner primitive and §3.2 space/pass accounting; p. 18, Appendix A.5 resources

import Definitions.Def_PaceSSSP517_Certified_Law

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical

namespace PaceSSSP517.Certified

/-- A streaming primitive really folds one stream. No whole graph is supplied to
`start` or `feed`. The opaque Store and its word footprint belong to a fixed external
implementation, not to the PACE run. Interface: AHS26 Proposition 3.2 (FKM+05/JKMV24),
as invoked in §3.1 p.5. `SpannerInterface` below states only this upstream primitive. -/
structure SpannerRoutine where
  Store : ℕ → Type
  start : (n k : ℕ) → ℝ → Store n
  feed : {n : ℕ} → ℕ → ℝ → Store n → Edge n → ℝ → Store n
  output : {n : ℕ} → Store n → Finset (Edge n)
  words : {n : ℕ} → Store n → ℕ

/-- Every undirected edge once, in arbitrary order. -/
def StreamOf {n : ℕ} (G : WeightedGraph n) (σ : List (Edge n)) : Prop :=
  σ.Nodup ∧ σ.toFinset = G.edges

noncomputable def spannerState (A : SpannerRoutine) {n : ℕ} (G : WeightedGraph n)
    (k : ℕ) (ε : ℝ) (σ : List (Edge n)) : A.Store n :=
  σ.foldl (fun z e => A.feed k ε z e (G.weight e)) (A.start n k ε)

noncomputable def spannerOutput (A : SpannerRoutine) {n : ℕ} (G : WeightedGraph n)
    (k : ℕ) (ε : ℝ) (σ : List (Edge n)) : Finset (Edge n) :=
  A.output (spannerState A G k ε σ)

noncomputable def spannerPeak (A : SpannerRoutine) {n : ℕ} (G : WeightedGraph n)
    (k : ℕ) (ε : ℝ) (σ : List (Edge n)) : ℕ :=
  ((List.range (σ.length + 1)).map (fun i => A.words (spannerState A G k ε (σ.take i)))).foldl max 0

/-- Uniform, deterministic one-pass spanner construction, size AND peak workspace.
C_H is fixed before all instances. This is an external graph primitive, not an
assumption about PACE's sampling, failure count, stopping or resources. -/
noncomputable def SpannerInterface (A : SpannerRoutine) (C_H : ℝ) : Prop :=
  0 < C_H ∧ ∀ (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (σ : List (Edge n)),
    Parameters n k ε → Connected G.edges → StreamOf G σ →
      let H := spannerOutput A G k ε σ
      IsSpanner G H (2 * (k : ℝ) - 1 + ε) ∧
      (H.card : ℝ) ≤ C_H * (ε⁻¹ * (n : ℝ)^(1 + 1/(k : ℝ)) * Real.log n) ∧
      (spannerPeak A G k ε σ : ℝ) ≤
        C_H * (ε⁻¹ * (n : ℝ)^(1 + 1/(k : ℝ)) * Real.log n)

/-- Committed bulk pins. The stop is before update, so the terminal virtual pins
are not retained by the actual implementation. Sets B themselves are ghost expressions. -/
noncomputable def storedViolators {n : ℕ} (_G : WeightedGraph n) (t : Round n) : Finset (Edge n) :=
  if t.bulk && !t.stopping then t.bulkPins else ∅

noncomputable def Vcount {n : ℕ} (G : WeightedGraph n) (ts : List (Round n)) : ℕ :=
  (ts.map (fun t => (storedViolators G t).card)).sum

def treeCount {n : ℕ} (ts : List (Round n)) : ℕ := (ts.map (fun t => t.tree.card)).sum

/-- Maximum live buffer, including the just-read edge at threshold overflow. -/
noncomputable def bufferPeak {n : ℕ} (G : WeightedGraph n) (s : ℝ)
    (d : Fin n → ℝ) (σ : List (Edge n)) : ℕ :=
  ((List.range (σ.length + 1)).map (fun i =>
    ((σ.take i).foldl (bufferStep G s d) (some ∅)).elim 0 Finset.card)).foldl max 0 + 1

/-- Explicit word banks of the implementation in §3.2 p.6 / A.5 p.18.
An edge record has 3 words, a profile n, multiplier/round metadata 4.
For local shortest paths reserve adjacency entries (6 words per retained edge),
6n search/parent/distance words, and the current tree/profile in the 8n bank.
All older samples have been freed. Time for local exact shortest paths is uncharged.
The list gives allocated bank sizes, rather than a freely supplied space field. -/
noncomputable def passABanks {n : ℕ} (G : WeightedGraph n) (H : Finset (Edge n))
    (old : List (Round n)) (t : Round n) : List ℕ :=
  [3 * H.card, 3 * treeCount old, 3 * Vcount G old, n * old.length,
    4 * old.length, 3 * t.sample.card,
    6 * (H.card + treeCount old + Vcount G old + t.sample.card), 8 * n, 16]

/-- Pass B retains trees/profiles and only a bounded buffer. Suffix maxima and
backwards prefix sums use two arrays of length r; weights use a scalar product. -/
noncomputable def passBBanks {n : ℕ} (G : WeightedGraph n) (H : Finset (Edge n))
    (k : ℕ) (ε : ℝ) (old : List (Round n)) (t : Round n) (σ : List (Edge n)) : List ℕ :=
  [3 * H.card, 3 * (treeCount old + t.tree.card), 3 * Vcount G old,
    n * (old.length + 1), 4 * old.length,
    3 * bufferPeak G (budget n k ε) t.d σ, 2 * (old.length + 1), 16]

/-- Peak physical word banks, including the one-pass spanner's workspace and every
executed Pass A/B. The ghost trajectory and its past sample sets are not allocated.
Subsequent stream orders can be chosen arbitrarily, even adaptively. -/
noncomputable def peakWords {n : ℕ} (G : WeightedGraph n) (H : Finset (Edge n))
    (k : ℕ) (ε : ℝ) (initialPeak : ℕ) (orders : ℕ → List (Edge n))
    (ts : List (Round n)) : ℕ :=
  ((List.range ts.length).map (fun i =>
    match ts[i]? with
    | none => 0
    | some t => max (passABanks G H (ts.take i) t).sum
        (passBBanks G H k ε (ts.take i) t (orders (i + 1))).sum)).foldl max initialPeak

def passCount {n : ℕ} (ts : List (Round n)) : ℕ := 2 * ts.length + 1

noncomputable def failureCount {n : ℕ} (G : WeightedGraph n)
    (ts : List (Round n)) (e : Edge n) : ℕ := (ts.filter (fun t => fails G t.d e)).length

/-- The actual output tree, with failure to stop kept explicit. -/
def stopped {n : ℕ} (ts : List (Round n)) : Prop :=
  ∃ t, ts.getLast? = some t ∧ t.stopping = true

end PaceSSSP517.Certified


