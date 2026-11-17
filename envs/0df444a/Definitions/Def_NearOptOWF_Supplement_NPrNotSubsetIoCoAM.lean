-- Prove2me | Definitions.Def_NearOptOWF_Supplement_NPrNotSubsetIoCoAM
-- name    : NearOptOWF_Supplement_NPrNotSubsetIoCoAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:01.430692+00:00
-- url     : https://prove2.me/theorems/ca928fef-da40-4a53-8eae-e355c49227cd
-- title:
--   The hypothesis $\mathsf{NP}[r]\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$
-- statement:
--   The hypothesis $\mathsf{NP}[r]\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$ states that some $L\in\mathsf{NP}[r]$ agrees infinitely often with no language of $\mathsf{coAM}$: for every $L'\in\mathsf{coAM}$, for all sufficiently large $n$ the languages $L$ and $L'$ differ on some string of length $n$. It is the complexity assumption of Theorem 5.2, the base hypothesis $\mathsf{NP}\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$ restricted to certificates of length $r$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2, first bullet, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_NearOptOWF_Supplement_InNPr
import Definitions.Def_NearOptOWF_AgreeIO
import Definitions.Def_LaconicBarrier_InCoAMPoly

namespace NearOptOWF.Supplement

/-- The hypothesis **`NP[r] ⊄_{i.o.} coAM`** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2, first bullet, p.23 (PDF p.25)): some
language `L ∈ NP[r]` agrees infinitely often (base `AgreeIO`) with no language of `coAM` (the published
`LaconicBarrier.InCoAMPoly`). This is the base `NPNotSubsetIoCoAM` with `NP` replaced by `NP[r]`. -/
def NPrNotSubsetIoCoAM (r : ℕ → ℕ) : Prop :=
  ∃ L : Set (List Bool), InNPr r L ∧
    ∀ L' : Set (List Bool), LaconicBarrier.InCoAMPoly L' → ¬ AgreeIO L L'

end NearOptOWF.Supplement


