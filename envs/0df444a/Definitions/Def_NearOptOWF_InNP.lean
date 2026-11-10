-- Prove2me | Definitions.Def_NearOptOWF_InNP
-- name    : NearOptOWF_InNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:22.535204+00:00
-- url     : https://prove2.me/theorems/0a4a0bf0-2813-4605-a9eb-6a926315e725
-- title:
--   The class NP
-- statement:
--   A language $L$ is in **NP** if $L = \{x : \exists w,\ R(x, w)\}$ for an NP relation $R$: a relation decidable in polynomial time whose witnesses satisfy $|w| \le q(|x|)$ for a polynomial $q$ (the published predicate `LaconicBarrier.IsNPRel`).
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3, p.8 (PDF p.10); Theorem 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_LaconicBarrier_Lang

namespace NearOptOWF

/-- `L ∈ NP`: `L` is the language `{x | ∃ w, R x w}` of an NP relation `R` (a polynomial-time
predicate with polynomially bounded witnesses, the published `LaconicBarrier.IsNPRel`) (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3,
p.8 (PDF p.10), and §4, p.11 (PDF p.13): the class NP in "NP ⊄_{i.o.} coAM"). -/
def InNP (L : Set (List Bool)) : Prop :=
  ∃ (R : List Bool → List Bool → Prop) (q : Polynomial ℕ),
    LaconicBarrier.IsNPRel R q ∧ L = LaconicBarrier.Lang R

end NearOptOWF


