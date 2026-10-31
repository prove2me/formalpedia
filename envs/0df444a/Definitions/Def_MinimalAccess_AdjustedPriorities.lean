-- Prove2me | Definitions.Def_MinimalAccess_AdjustedPriorities
-- name    : MinimalAccess_AdjustedPriorities
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:58.44204+00:00
-- url     : https://prove2.me/theorems/f58884a3-8bc1-438a-a4cf-32320176e8f0
-- title:
--   Adjusted priorities $\succ^r$ and classical stability
-- statement:
--   Given priorities $\succ$ and rights $r$, the **adjusted priorities** $\succ^r=(\succ^r_s)_{s\in S}$ are the strict priorities with, for each school $s$ and $r(s)=\{i: s\in r(i)\}$:
--
--   1. for $i,j\notin r(s)$: $i\succ^r_s j$ iff $i\succ_s j$;
--   2. for $i,j\in r(s)$: $i\succ^r_s j$ iff $i\succ_s j$;
--   3. for $i\in r(s)$, $j\notin r(s)$: $i\succ^r_s j$.
--
--   For a classical school choice problem $(P,\succ')$ with strict priorities $\succ'$, student $i$ has **justified envy** (Abdulkadiroğlu–Sönmez 2003) at $\mu$ if there are $j$, $s$ with $\mu(j)=s\,P_i\,\mu(i)$ and $i\succ'_s j$; $\mu$ is **classically stable** if it is individually rational, non-wasteful, and no student has justified envy.
--
--   Remark 1 of the paper identifies stability for $(P,\succ,r)$ with classical stability for $(P,\succ^r)$, and the deferred acceptance mechanism of the paper is classical deferred acceptance on $(P,\succ^r)$.
--
--   **Formalization Note** Classical priorities are given by keys `key : Fin m → Fin n → ℕ`, a smaller key being a higher priority ($i\succ'_s j$ iff `key s i < key s j`); theorems assume each `key s` injective. The adjusted priorities are the keys `adjKey pri r s i = (if s ∈ r i then 0 else n) + pri s i`; since every rank is below $n$, these realise exactly (1)–(3).
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Remark 1, pp.5–6

import Mathlib
import Definitions.Def_MinimalAccess_Model

namespace MinimalAccess

/-!
Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism*,
BSE Working Paper 1264 (rev. July 2023), Remark 1, pp.5–6: the adjusted priorities `≻^r` and
classical stability with respect to a classical school choice problem `(P, ≻^r)`
(Abdulkadiroğlu–Sönmez 2003).

**Formalization Note.** A classical priority profile is given by keys
`key : Fin m → Fin n → ℕ`, a smaller key being a higher priority (`i` ranked above `j` at `s`
iff `key s i < key s j`); the theorems assume each `key s` injective, which makes it a strict
order. The adjusted priorities are the keys `adjKey pri r`.
-/

open GaleShapley1962.Admissions

/-- The adjusted priorities `≻^r` of Remark 1 (p.6) as keys:
`adjKey pri r s i = (if s ∈ r(i) then 0 else n) + rank of i under ≻_s`. Since every rank is
`< n`, every `i ∈ r(s)` is above every `j ∉ r(s)` ((3)), and inside each of the two groups the
order is `≻_s` ((1), (2)); `i ≻^r_s j :⇔ adjKey pri r s i < adjKey pri r s j`. -/
def adjKey {n m : ℕ} (pri : Fin m → Prio n) (r : Fin n → Finset (Fin m)) (s : Fin m)
    (i : Fin n) : ℕ :=
  (if s ∈ r i then 0 else n) + (pri s i : ℕ)

/-- Justified envy in the classical sense (Abdulkadiroğlu–Sönmez 2003) at `μ` with respect to
`(P, key)`: there are `j` and `s` with `μ(j) = s P_i μ(i)` and `i` ranked above `j` at `s`. -/
def HasClassicalEnvy {n m : ℕ} (P : Fin n → Pref m) (key : Fin m → Fin n → ℕ)
    (μ : Assignment n m) (i : Fin n) : Prop :=
  ∃ j s, μ j = some s ∧ P i (some s) < P i (μ i) ∧ key s i < key s j

/-- Classical stability with respect to `(P, key)` (p.6, "as in college admissions"):
individually rational, non-wasteful, and no student has classical justified envy. -/
def IsClassicallyStable {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m)
    (key : Fin m → Fin n → ℕ) (μ : Assignment n m) : Prop :=
  IsIndividuallyRational P μ ∧ IsNonWasteful q P μ ∧ ∀ i, ¬ HasClassicalEnvy P key μ i

end MinimalAccess


