-- Prove2me | Definitions.Def_MultitaskContracts_Instance_IsIdentical
-- name    : MultitaskContracts_Instance_IsIdentical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:30.513256+00:00
-- url     : https://prove2.me/theorems/854bc765-4514-49eb-9b65-265a912ac7a6
-- title:
--   Identical (exchangeable) tasks, eq. (9)
-- statement:
--   The tasks of an instance are **identical** if they share $c$, $p$ and $q$ ($c_k=c$, $p_k=p$, $q_k=q$ for all $k$) and their joint distribution is equivariant under every permutation $\sigma$ of the tasks:
--   $$P_{\sigma S}(\sigma Y)=P_S(Y)\qquad\text{for all } S,Y\subseteq K, \tag{9}$$
--   where $\sigma S=\{\sigma(k):k\in S\}$ and likewise $\sigma Y$.
--
--   For identical independent tasks the optimal Min-Pay contract has a closed form (Proposition 1), which gives the lower bound in Theorem 2.
--
--   **Formalization Note** $\sigma S$ is `S.map σ` for `σ : Equiv.Perm K`.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §2, eq. (9), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Identical tasks** (§2, p.8, PDF 10): the tasks share `c`, `p` and `q`, and the joint
distribution is equivariant under every permutation `σ` of the tasks,
`P_{σS}(σY) = P_S(Y)` for all `S, Y` (eq. (9)), where `σS := {σ(k) : k ∈ S}`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §2, p.8, eq. (9).

**Formalization Note.** `σS` is `S.map σ` for `σ : Equiv.Perm K`. -/
def Instance.IsIdentical {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K) : Prop :=
  (∀ k k' : K, I.c k = I.c k' ∧ I.p k = I.p k' ∧ I.q k = I.q k') ∧
  ∀ (σ : Equiv.Perm K) (S Y : Finset K),
    I.P (S.map σ.toEmbedding) (Y.map σ.toEmbedding) = I.P S Y

end MultitaskContracts


