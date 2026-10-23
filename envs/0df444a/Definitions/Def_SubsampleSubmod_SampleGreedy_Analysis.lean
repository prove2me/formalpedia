-- Prove2me | Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis
-- name    : SubsampleSubmod_SampleGreedy_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:04.900542+00:00
-- url     : https://prove2.me/theorems/ff1a9ce5-5a8d-4be4-b1d6-3d7b8151089e
-- title:
--   Algorithm 2, pp. 9, 11, 13, 15 — Equivalent-SampleGreedy with fixed coin flips, the sets O, O_u, S_u, the indicators X_u, Y_u, and expectation over the coins
-- statement:
--   This file encodes Algorithm 2 (Equivalent-SampleGreedy) of Harshaw, Kazemi, Feldman and Karbasi, the auxiliary algorithm used only in the analysis of SampleGreedy, together with its random variables.
--
--   Fix a comparison set $T$ (the paper's OPT) and the outcome of the coin flips, encoded as a set $B \subseteq \mathcal N$ ($u$'s coin shows 1 iff $u \in B$). The state consists of the solution $S$, the set $O$, the set $\mathcal N'$ of elements not yet considered, the considered elements, and for each $u$ the sets $O_u$ and $S_u$. Initially $S = \emptyset$, $O = T$, $\mathcal N' = \mathcal N$ and all $O_u, S_u$ are empty. One iteration:
--
--   1. If no $u \in \mathcal N'$ has $S \cup \{u\} \in \mathcal I$ and $f(u \mid S) > 0$, nothing changes. Otherwise let $u$ be the candidate maximizing $f(u \mid S)$ (ties broken by the fixed order of $\mathcal N$), mark $u$ considered and set $S_u = S$.
--   2. If $u \in B$: add $u$ to $S$ and to $O$, then let $O_u \subseteq O \setminus S$ be a set of minimum cardinality with $O \setminus O_u \in \mathcal I$ (one fixed choice).
--   3. If $u \notin B$: $O_u = \{u\}$ if $u \in O$, and $O_u = \emptyset$ otherwise.
--   4. Remove $O_u$ from $O$ and $u$ from $\mathcal N'$.
--
--   The algorithm runs $n$ iterations. For each $u$: $X_u = 1$ iff $u$ was considered, and $Y_u = 1$ iff $u$ was added to $S$ and $u \notin O$ at the beginning of the iteration in which it was considered. Expectations over the coins are
--   $$\mathbb E[F] = \sum_{B \subseteq \mathcal N} q^{|B|}(1-q)^{n-|B|}\, F(\text{final state of the run with coins } B).$$
--
--   Lemmas 4–10 of the paper are statements about this run; Lemma 4 shows its output has the law of SampleGreedy's output.
--
--   **Formalization Note** The coin flips are fixed up front as a bit set, which is how the proof of Lemma 4 (p. 10) treats them. "The smallest set" of line 6 is read as minimum cardinality, chosen once by `Classical.choose`; the lemmas hold for every such choice. A fallback value $\emptyset$ is used if no admissible set exists; on runs from an independent $T$ an admissible set always exists ($O \setminus S$ itself). The state records the set of $u$ with $Y_u = 1$ directly.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 9 (Algorithm 2), p. 10 (fixed random bits b_1, …, b_n and tie-breaking), p. 11 ('considered', S_u, O_u), p. 13 (X_u), p. 15 (Y_u)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Model

namespace SubsampleSubmod.SampleGreedy

open Finset

/-- The state of Algorithm 2 (Equivalent-SampleGreedy, p. 9): the solution `S`, the set `O`, the
not-yet-considered elements `rem` (the set `𝒩′` of Algorithm 2), the considered elements, the sets
`O_u`, `S_u`, and the set of `u` with `Y_u = 1` (p. 15: `u` is added to `S` and `u ∉ O` at the
beginning of the iteration in which `u` is considered). -/
structure Alg2State (α : Type) where
  S : Finset α
  O : Finset α
  rem : Finset α
  considered : Finset α
  Ou : α → Finset α
  Su : α → Finset α
  Y : Finset α

/-- Line 1 of Algorithm 2: `𝒩′ = 𝒩`, `S = ∅`, `O = T` (the comparison set, OPT), `O_u = S_u = ∅`. -/
def alg2Init {α : Type} [Fintype α] (T : Finset α) : Alg2State α :=
  ⟨∅, T, Finset.univ, ∅, fun _ => ∅, fun _ => ∅, ∅⟩

open Classical in
/-- Line 6 of Algorithm 2: a smallest (minimum-cardinality) `X ⊆ O \ S` with `O \ X ∈ ℐ`; one fixed
choice. (The fallback `∅` is never used on runs from an independent `T`, where `X = O \ S` works.) -/
noncomputable def minRemoval {α : Type} [DecidableEq α] (I : Finset α → Prop) (O S : Finset α) :
    Finset α :=
  if h : ((O \ S).powerset.filter (fun X => I (O \ X))).Nonempty then
    Classical.choose (Finset.exists_min_image _ Finset.card h)
  else ∅

/-- One iteration of the while loop of Algorithm 2 (lines 2–11), with the coin flips fixed by the bit
set `B` (`u` is added to `S` iff `u ∈ B`). If there is no candidate, the state is unchanged. -/
noncomputable def alg2Step {α : Type} [LinearOrder α] (f : Finset α → ℝ) (I : Finset α → Prop)
    (B : Finset α) (st : Alg2State α) : Alg2State α :=
  match pick f I st.rem st.S with
  | none => st
  | some u =>
    if u ∈ B then
      let S' := insert u st.S
      let O' := insert u st.O
      let X := minRemoval I O' S'
      { S := S', O := O' \ X, rem := st.rem.erase u, considered := insert u st.considered,
        Ou := Function.update st.Ou u X, Su := Function.update st.Su u st.S,
        Y := if u ∈ st.O then st.Y else insert u st.Y }
    else
      let X : Finset α := if u ∈ st.O then {u} else ∅
      { S := st.S, O := st.O \ X, rem := st.rem.erase u, considered := insert u st.considered,
        Ou := Function.update st.Ou u X, Su := Function.update st.Su u st.S, Y := st.Y }

/-- The final state of Algorithm 2 run with comparison set `T` (OPT) and coin flips `B`, after
`n = |𝒩|` iterations (each effective iteration considers a new element). -/
noncomputable def alg2 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) : Alg2State α :=
  (alg2Step f I B)^[Fintype.card α] (alg2Init T)

/-- Expectation over the coin flips of Algorithm 2 (each element's coin is `1` with probability `q`,
independently) of a function `F` of the final state. -/
noncomputable def E2 {α : Type} [Fintype α] [LinearOrder α] (q : ℝ) (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) (F : Alg2State α → ℝ) : ℝ :=
  ∑ B : Finset α, sampleWeight q B * F (alg2 f I T B)

end SubsampleSubmod.SampleGreedy


