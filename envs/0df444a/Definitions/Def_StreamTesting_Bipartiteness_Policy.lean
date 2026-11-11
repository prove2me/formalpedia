-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Policy
-- name    : StreamTesting_Bipartiteness_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:23.017757+00:00
-- url     : https://prove2.me/theorems/319898d4-3422-4b88-bd6d-f5fc2fdace14
-- title:
--   Unrestricted history-dependent randomized stream policies
-- statement:
--   For $n$ labels, an observed history records at each elapsed position the arriving label and either a skip or its returned neighbor set. Positions not yet elapsed are absent. A deterministic policy is an arbitrary function deciding query versus skip from the prior observed history and the current label, together with an arbitrary final accept decision from the completed history.
--
--   A randomized policy is any input-independent probability distribution over these deterministic tables. There are finitely many possible observed histories at each fixed $n$, so this includes the behavior induced by arbitrary private random tapes, memory, and computation; it puts no bound on those resources. An order is a permutation mapping positions to labels.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1, printed p.3 / PDF p.3.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Entries are absent before arrival, and after arrival record the label and either
skip (none) or the returned full neighborhood (some N). Slots are stream positions. -/
abbrev History (n : ℕ) := Fin n → Option (Fin n × Option (Finset (Fin n)))

/-- Index-to-label permutation, with zero-based positions. -/
abbrev Order (n : ℕ) := Equiv.Perm (Fin n)

/-- An unrestricted table of query decisions and a final accept decision.
The decision receives only the observed history and the current arriving label.
All these function types are finite for fixed n, with no computational restriction. -/
abbrev Policy (n : ℕ) := (History n → Fin n → Bool) × (History n → Bool)

/-- The entire decision-table space is finite; no bound on algorithms is added. -/
instance policyFintype (n : ℕ) : Fintype (Policy n) := Fintype.ofFinite _

/-- An arbitrary input-independent distribution over deterministic decision tables. -/
abbrev RandomPolicy (n : ℕ) := PMF (Policy n)

end StreamTesting.Bipartiteness


