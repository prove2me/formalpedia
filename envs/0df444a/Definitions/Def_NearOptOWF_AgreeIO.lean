-- Prove2me | Definitions.Def_NearOptOWF_AgreeIO
-- name    : NearOptOWF_AgreeIO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:02.095052+00:00
-- url     : https://prove2.me/theorems/017d10c6-12b8-41fd-9ab8-1dc8d7cea1db
-- title:
--   Infinitely-often agreement of two languages
-- statement:
--   Two languages $L, L' \subseteq \{0,1\}^*$ **agree infinitely often** if there are infinitely many input lengths $n$ such that
--   $$
--   \forall x \in \{0,1\}^n:\quad x \in L \iff x \in L' .
--   $$
--   For complexity classes $\mathcal A, \mathcal B$, the paper's inclusion $\mathcal A \subseteq_{\mathrm{i.o.}} \mathcal B$ ("for every $L \in \mathcal A$, there exists a reduction that works on every instance at infinitely many input lengths $n$") means that every $L \in \mathcal A$ agrees infinitely often with some $L' \in \mathcal B$.
--
--   **Formalization Note** This is the standard reading of the infinitely-often inclusion; strings are Lean lists of booleans.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3 Notations, p.8 (PDF p.10)

import Mathlib

namespace NearOptOWF

/-- `L` and `L'` agree on every string of length `n`, for infinitely many `n` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3
Notations, p.8 (PDF p.10): "`A ⊆_{i.o.} B` … for every `L ∈ A`, there exists a reduction that works on
every instance at infinitely many input lengths `n`").

**Formalization Note** This is the standard reading of the infinitely-often inclusion: `L` lies in
`i.o.-B` when some `L' ∈ B` agrees with `L` on all inputs of length `n` for infinitely many `n`. -/
def AgreeIO (L L' : Set (List Bool)) : Prop :=
  ∃ᶠ n in Filter.atTop, ∀ x : List Bool, x.length = n → (x ∈ L ↔ x ∈ L')

end NearOptOWF


