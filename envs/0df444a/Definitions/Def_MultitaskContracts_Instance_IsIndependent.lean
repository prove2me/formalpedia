-- Prove2me | Definitions.Def_MultitaskContracts_Instance_IsIndependent
-- name    : MultitaskContracts_Instance_IsIndependent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:24.95002+00:00
-- url     : https://prove2.me/theorems/2018c07c-2480-490a-8759-bb5cbda426dd
-- title:
--   Independent tasks: $P_S$ is the product of its marginals
-- statement:
--   The tasks of an instance are **independent** if for every strategy $S$ the distribution $P_S$ is the product of its marginals (1):
--   $$P_S(Y)=\prod_{k\in Y\cap S}p_k\prod_{k\in Y\setminus S}q_k\prod_{k\in S\setminus Y}(1-p_k)\prod_{k\notin S\cup Y}(1-q_k)\qquad\text{for all } S,Y\subseteq K.$$
--   Independence is the first and smallest class of the dependence hierarchy Independent $\subset$ MMLRP $\subset$ Strongest indicator $\subset$ Arbitrary.
--
--   **Formalization Note** The four products are one product over all tasks, with the factor of task $k$ chosen by whether $k\in S$ and whether $k\in Y$.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §2, "Dependence between tasks", p.6 (PDF p.8)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Independent tasks** (§2, p.6, PDF 8): for every strategy `S` the distribution `P_S` is the
product of its marginals,
`P_S(Y) = ∏_{k∈Y∩S} p_k ∏_{k∈Y∖S} q_k ∏_{k∈S∖Y} (1 − p_k) ∏_{k∉S∪Y} (1 − q_k)`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §2, p.6.

**Formalization Note.** The four products are written as one product over all tasks with the
factor chosen by whether `k ∈ S` and whether `k ∈ Y`. -/
def Instance.IsIndependent {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K) : Prop :=
  ∀ S Y : Finset K, I.P S Y =
    ∏ k, if k ∈ S then (if k ∈ Y then I.p k else 1 - I.p k)
      else (if k ∈ Y then I.q k else 1 - I.q k)

end MultitaskContracts


