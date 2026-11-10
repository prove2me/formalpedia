-- Prove2me | Definitions.Def_NearOptOWF_CoNPNotSubsetIoNP
-- name    : NearOptOWF_CoNPNotSubsetIoNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:29.730376+00:00
-- url     : https://prove2.me/theorems/49051500-b8f5-45f2-b85e-f78a0d13f3b8
-- title:
--   The hypothesis $\mathsf{coNP} \not\subseteq_{\mathrm{i.o.}} \mathsf{NP}$
-- statement:
--   The hypothesis $\mathsf{coNP} \not\subseteq_{\mathrm{i.o.}} \mathsf{NP}$ states that some language $L$ whose complement is in NP agrees infinitely often with no language in NP.
--
--   It is the complexity assumption of Lemma 3.6, and it follows from $\mathsf{NP} \not\subseteq_{\mathrm{i.o.}} \mathsf{coAM}$ because $\mathsf{NP} \subseteq \mathsf{AM}$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.6, p.9 (PDF p.11); §3 Notations, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_AgreeIO
import Definitions.Def_NearOptOWF_InNP

namespace NearOptOWF

/-- The hypothesis **`coNP ⊄_{i.o.} NP`** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.6, p.9 (PDF p.11); §3 Notations, p.8
(PDF p.10) for `⊆_{i.o.}`): some language `L` whose complement is in NP agrees with no NP language on
all inputs of length `n` for infinitely many `n`. -/
def CoNPNotSubsetIoNP : Prop :=
  ∃ L : Set (List Bool), InNP Lᶜ ∧ ∀ L' : Set (List Bool), InNP L' → ¬ AgreeIO L L'

end NearOptOWF


