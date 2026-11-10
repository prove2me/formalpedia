-- Prove2me | Definitions.Def_NearOptOWF_NPNotSubsetIoCoAM
-- name    : NearOptOWF_NPNotSubsetIoCoAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:39.014127+00:00
-- url     : https://prove2.me/theorems/1ead11b0-8da1-4971-8f15-ff1116bce687
-- title:
--   The hypothesis $\mathsf{NP} \not\subseteq_{\mathrm{i.o.}} \mathsf{coAM}$
-- statement:
--   The hypothesis $\mathsf{NP} \not\subseteq_{\mathrm{i.o.}} \mathsf{coAM}$ states that some language $L \in \mathsf{NP}$ agrees infinitely often with no language $L' \in \mathsf{coAM}$: for every $L' \in \mathsf{coAM}$, for all sufficiently large $n$ there is a string of length $n$ on which $L$ and $L'$ differ.
--
--   Here $L' \in \mathsf{coAM}$ means that the complement of $L'$ has an Arthur–Merlin proof: a one-round public-coin interactive proof with polynomial verifier time, communication and randomness, completeness $2/3$ and soundness $1/3$ (the published `LaconicBarrier.InCoAMPoly`).
--
--   This is the complexity assumption of Theorem 4.1.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13), first bullet; §3 Notations, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_AgreeIO
import Definitions.Def_NearOptOWF_InNP
import Definitions.Def_LaconicBarrier_InCoAMPoly

namespace NearOptOWF

/-- The hypothesis **`NP ⊄_{i.o.} coAM`** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13), first bullet; §3
Notations, p.8 (PDF p.10) for `⊆_{i.o.}`): some language `L ∈ NP` agrees with no language of
`coAM` on all inputs of length `n` for infinitely many `n`.

**Formalization Note** `coAM` is the published `LaconicBarrier.InCoAMPoly`: the complement has a
one-round public-coin (Arthur–Merlin) proof with polynomial verifier time, communication and
randomness, completeness `2/3` and soundness `1/3`. The infinitely-often inclusion is read as in
`AgreeIO`. -/
def NPNotSubsetIoCoAM : Prop :=
  ∃ L : Set (List Bool), InNP L ∧ ∀ L' : Set (List Bool), LaconicBarrier.InCoAMPoly L' → ¬ AgreeIO L L'

end NearOptOWF


