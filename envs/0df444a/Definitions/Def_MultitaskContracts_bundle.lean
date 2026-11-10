-- Prove2me | Definitions.Def_MultitaskContracts_bundle
-- name    : MultitaskContracts_bundle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:30:42.906624+00:00
-- url     : https://prove2.me/theorems/79220004-8bf4-433b-ba03-922c5fa03406
-- title:
--   Bundle contracts $\mathbb R^{2^K}_{\ge 0}$
-- statement:
--   A **bundle contract** on the task set $K$ is any payment scheme $t:2^K\to\mathbb R_{\ge 0}$: the principal pays $t(Y)\ge0$ when she observes that exactly the tasks in $Y$ succeed. The class of bundle contracts is $\mathbb R^{2^K}_{\ge0}$; the payment may depend arbitrarily on the combination of outcomes.
--
--   Bundle contracts are the benchmark class against which separable contracts are compared in the price of separation.
--
--   **Formalization Note** A contract is a function `Finset K → ℝ`; limited liability $t(Y)\ge0$ is the membership condition.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §2, "Classes of contracts", p.8 (PDF p.10)

import Mathlib

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- The class of **bundle contracts** `ℝ^Y_{≥0}` (§2, p.8, PDF 10): every nonnegative payment
scheme `t : 2^K → ℝ_{≥0}` on performances, which may depend arbitrarily on the combination of
outcomes. E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §2, p.8.

**Formalization Note.** A contract is a function `Finset K → ℝ`; limited liability (`t(Y) ≥ 0`)
is the membership condition. -/
def bundle (K : Type*) [Fintype K] [DecidableEq K] : Set (Finset K → ℝ) :=
  {t | ∀ Y, 0 ≤ t Y}

end MultitaskContracts


