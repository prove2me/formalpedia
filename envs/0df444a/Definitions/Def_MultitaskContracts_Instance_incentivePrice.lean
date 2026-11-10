-- Prove2me | Definitions.Def_MultitaskContracts_Instance_incentivePrice
-- name    : MultitaskContracts_Instance_incentivePrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:29.56665+00:00
-- url     : https://prove2.me/theorems/70c24702-37a7-482a-8c87-703774519516
-- title:
--   Incentive price $\theta(S)$ (Definition 3)
-- statement:
--   The **incentive price** of a strategy $S\subsetneq K$ is
--   $$\theta(S)=\frac{c(K)-c(S)}{P_K(K)-P_S(K)}.$$
--   It is the smallest payment for success on all tasks that deters the deviation $S$ under an all-or-nothing contract.
--
--   **Formalization Note** Real division. The paper defines $\theta$ only for $S\subsetneq K$ (at $S=K$ the Lean expression is $0/0=0$); every statement using it restricts to $S\neq K$, where the denominator is positive under eq. (3).
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Definition 3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Incentive price** (Definition 3, p.13, PDF 15) of a strategy `S ⊊ K`:
`θ(S) := (c(K) − c(S)) / (P_K(K) − P_S(K))`. E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Definition 3, p.13.

**Formalization Note.** Real division; the paper defines `θ` only for `S ⊊ K` (at `S = K` the
expression is `0/0 = 0` in Lean), and every statement that uses it restricts to `S ≠ univ`. -/
noncomputable def Instance.incentivePrice {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K)
    (S : Finset K) : ℝ :=
  (I.cost Finset.univ - I.cost S) / (I.P Finset.univ Finset.univ - I.P S Finset.univ)

end MultitaskContracts


