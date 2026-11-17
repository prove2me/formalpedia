-- Prove2me | Definitions.Def_NearOptOWF_Supplement_InNPr
-- name    : NearOptOWF_Supplement_InNPr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:09:28.888445+00:00
-- url     : https://prove2.me/theorems/65e51cb4-1b69-4fd5-8c39-04ac3a7c689b
-- title:
--   The class $\mathsf{NP}[r]$
-- statement:
--   For $r:\mathbb N\to\mathbb N$, a language $L$ is in $\mathsf{NP}[r]$, the **NP languages with certificate length at most $r$**, if $L = \{x : \exists w,\ R(x,w)\}$ for an NP relation $R$ (polynomial-time decidable, with polynomially bounded witnesses) all of whose witnesses satisfy
--   $$
--   R(x, w)\ \Rightarrow\ |w|\le r(|x|).
--   $$
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2, first bullet, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang

namespace NearOptOWF.Supplement

/-- `L ∈ NP[r]`, the **NP languages with certificate length at most `r`** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2, first bullet,
p.23 (PDF p.25): "`NP[r]` denote the set of NP languages with certificate length at most `r`"; §1, p.4
(PDF p.6)): `L = {x | ∃ w, R x w}` for an NP relation `R` (the published `LaconicBarrier.IsNPRel`, as in
the base `InNP`) all of whose witnesses for an input of length `ℓ` have length at most `r(ℓ)`. -/
def InNPr (r : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ (R : List Bool → List Bool → Prop) (q : Polynomial ℕ),
    LaconicBarrier.IsNPRel R q ∧ (∀ x w, R x w → w.length ≤ r x.length) ∧ L = LaconicBarrier.Lang R

end NearOptOWF.Supplement


