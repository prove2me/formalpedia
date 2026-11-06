-- Prove2me | Definitions.Def_PADMPriv_Adjacent
-- name    : PADMPriv_Adjacent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:08.755262+00:00
-- url     : https://prove2.me/theorems/1149a485-cb77-48ef-8338-9b350f5f8d58
-- title:
--   Neighbouring data sets $D\sim D'$
-- statement:
--   A data set is a sequence $D=(d_{(1)},\dots,d_{(n)})\in R^n$ of records. Two data sets $D$ and $D'$ are **neighbouring**, written $D\sim D'$, if they differ in at most one record: there is an index $i$ with $d_{(j)}=d'_{(j)}$ for all $j\ne i$.
--
--   **Formalization Note** Data sets are indexed by $\{0,\dots,n-1\}$ (record $k+1$ of the paper at index $k$). "At most one" includes $D=D'$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 2.2, p.3

import Mathlib

namespace PADMPriv

/-- Neighbouring data sets, Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), Section 2.2, p.3: `D = (d₍₁₎, …, d₍ₙ₎)` and
`D′` are neighbouring, `D ∼ D′`, if they differ in at most one record.

**Formalization Note** A data set is `Fin n → R` (record `k + 1` of the paper at index `k`).
"At most one" includes `D = D′`. -/
def Adjacent {R : Type*} {n : ℕ} (D D' : Fin n → R) : Prop :=
  ∃ i : Fin n, ∀ j : Fin n, j ≠ i → D j = D' j

end PADMPriv


