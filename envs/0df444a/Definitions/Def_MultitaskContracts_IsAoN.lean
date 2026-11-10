-- Prove2me | Definitions.Def_MultitaskContracts_IsAoN
-- name    : MultitaskContracts_IsAoN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:31:24.332196+00:00
-- url     : https://prove2.me/theorems/77e8b21d-3ee6-47ed-953b-dbe023d4ef88
-- title:
--   All-or-nothing (AoN) contract (Definition 2)
-- statement:
--   An **all-or-nothing (AoN) contract** is a bundle contract with a single nonzero payment, for success on all tasks: $t(Y)\ge 0$ for every $Y$, and
--   $$t(Y)=0\quad\text{for every } Y\subsetneq K.$$
--   Under the strongest-indicator condition (eq. (3)) some optimal Min-Pay contract is of this form (Lemma 1), which reduces Min-Pay to choosing the single payment $t(K)$.
--
--   **Formalization Note** $Y\subsetneq K$ is `Y ≠ Finset.univ`; the payment $t(K)\ge0$ is allowed to be $0$.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Definition 2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MultitaskContracts_bundle

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **All-or-nothing (AoN) contract** (Definition 2, p.12, PDF 14): a bundle contract with a
single nonzero payment, for success in all tasks, i.e. `t(Y) = 0` for every `Y ⊊ K`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Definition 2, p.12.

**Formalization Note.** `Y ⊊ K` is `Y ≠ Finset.univ`; the payment `t(K) ≥ 0` may be `0`. -/
def IsAoN {K : Type*} [Fintype K] [DecidableEq K] (t : Finset K → ℝ) : Prop :=
  t ∈ bundle K ∧ ∀ Y, Y ≠ Finset.univ → t Y = 0

end MultitaskContracts


