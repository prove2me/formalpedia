-- Prove2me | Definitions.Def_Chi2QEC_Supplement_errorWeight
-- name    : Chi2QEC_Supplement_errorWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:06:57.693587+00:00
-- url     : https://prove2.me/theorems/7d2db3a6-3666-42d8-9a6a-aca74589d485
-- title:
--   Weight of a generalized Pauli error
-- statement:
--   The weight of the generalized Pauli error $W_e$ with exponents $e=((a_1,b_1),\dots,(a_n,b_n))$ is the number of qudits on which it acts nontrivially,
--   $$
--   \operatorname{wt}(e)=\#\{\ell:(a_\ell,b_\ell)\neq(0,0)\}.
--   $$
--   An error of weight $j$ is an error on $j$ physical qudits, the "$j\le t$ physical qudits with errors" of the proof of Theorem 1.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, proof of Theorem 1, p.15

import Mathlib

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. V A, proof of Theorem 1, p.15 ("Suppose that there are j ≤ t physical
qudits with errors"): the weight of the generalized Pauli error with exponents `e`, the number of
qudits `ℓ` on which it acts nontrivially, `e ℓ ≠ (0, 0)`.

**Formalization Note.** `e ℓ ≠ (0, 0)` is written on the underlying natural numbers so that the
definition needs no `NeZero q`. -/
def errorWeight {n q : ℕ} (e : Fin n → Fin q × Fin q) : ℕ :=
  (Finset.univ.filter fun ℓ => ((e ℓ).1 : ℕ) ≠ 0 ∨ ((e ℓ).2 : ℕ) ≠ 0).card

end Chi2QEC.Supplement


