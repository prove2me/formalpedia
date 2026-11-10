-- Prove2me | Definitions.Def_CritContracts_BipInst
-- name    : CritContracts_BipInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:18.788679+00:00
-- url     : https://prove2.me/theorems/60c2deaf-5001-41e6-b726-129ea8cf5529
-- title:
--   Quadratic rewards on a bipartite graph (form (2)), $\lambda$-stable profiles and $S(\lambda)$
-- statement:
--   An **instance of the form (2)** is a two-agent instance in which agent 1 owns a ground set $U$, agent 2 owns a disjoint ground set $V$, every vertex is an action with a cost, and the reward is the total weight of the edges covered on both ends:
--   $$f(A,B)=\sum_{u\in A,\ v\in B}f_{uv}.$$
--   For $B\subseteq V$ and $u\in U$ the **support** of $u$ is $d_B(u)=\sum_{v\in B}f_{uv}$, and symmetrically $d_A(v)=\sum_{u\in A}f_{uv}$ for $A\subseteq U$, $v\in V$.
--
--   For a payment vector $\lambda=(\lambda_1,\lambda_2)$, a profile $(A,B)$ is **$\lambda$-stable** if
--   $$\lambda_1\,d_B(u)\ge c(u)\ \text{ for every }u\in A,\qquad \lambda_2\,d_A(v)\ge c(v)\ \text{ for every }v\in B,$$
--   and $S(\lambda)$ is the **union of all $\lambda$-stable profiles**.
--
--   Lemma B.1 shows that $S(\lambda)$ is the reward-maximizing pure Nash equilibrium at payments $\lambda$; Lemmas B.2–B.8 describe $S(\lambda)$ in the reduction's graph.
--
--   **Formalization Note** One vertex type with a side map (`0` for $U$, `1` for $V$) stands for the disjoint ground sets; only the weights $f_{uv}$ with $u\in U$, $v\in V$ enter the reward. The payment vector is indexed by the side. `toModel` is the corresponding two-agent contract instance.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Appendix B.1, (2), pp.32–33 (PDF pp.33–34): the reward (2), supports, λ-stable profiles and S(λ)

import Mathlib
import Definitions.Def_CritContracts_Model

set_option autoImplicit false

namespace CritContracts

/-- A **two-agent instance with a quadratic reward on a bipartite graph**, the form (2) of Ezra–Feldman–Molina–
Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027 submission (manuscript
sha256 430be35c…), Appendix B.1, (2), p.32, PDF p.33: agent 1 owns the vertices `U = {x | side x = 0}`, agent 2
owns `V = {x | side x = 1}`, each vertex `x` is an action with cost `c x`, and
`f(A, B) = Σ_{u ∈ A, v ∈ B} f_uv` with `f_uv = w u v` for `u ∈ U`, `v ∈ V`.

**Formalization Note** One vertex type with a side map stands for the disjoint ground sets `U` and `V`; only the
values `w u v` with `u ∈ U`, `v ∈ V` enter the reward. -/
structure BipInst (X : Type) where
  /-- The side of a vertex: `0` for `U` (agent 1), `1` for `V` (agent 2). -/
  side : X → Fin 2
  /-- The edge weights `f_uv` (`u ∈ U`, `v ∈ V`). -/
  w : X → X → ℝ
  /-- The vertex costs. -/
  c : X → ℝ

namespace BipInst

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The reward (2): `f(S) = Σ_{u ∈ S ∩ U} Σ_{v ∈ S ∩ V} f_uv`. -/
def reward (I : BipInst X) (S : Finset X) : ℝ :=
  ∑ u ∈ S.filter (fun x => I.side x = 0), ∑ v ∈ S.filter (fun x => I.side x = 1), I.w u v

/-- The two-agent contract instance of form (2): agent `side x` owns vertex `x`. -/
def toModel (I : BipInst X) : Model (Fin 2) X := ⟨I.side, I.reward, I.c⟩

/-- The **support** of a vertex against a profile `S` (pp.32–33): `d_B(u) = Σ_{v ∈ B} f_uv` for `u ∈ U` and
`d_A(v) = Σ_{u ∈ A} f_uv` for `v ∈ V`, where `(A, B) = (S ∩ U, S ∩ V)`. -/
def support (I : BipInst X) (S : Finset X) (x : X) : ℝ :=
  if I.side x = 0 then ∑ v ∈ S.filter (fun y => I.side y = 1), I.w x v
  else ∑ u ∈ S.filter (fun y => I.side y = 0), I.w u x

/-- A profile is **`λ`-stable** (p.33): `λ₁ d_B(u) ≥ c(u)` for every `u ∈ A` and `λ₂ d_A(v) ≥ c(v)` for every
`v ∈ B`. The payment vector `lam = (λ₁, λ₂)` is indexed by the side. -/
def IsStable (I : BipInst X) (lam : Fin 2 → ℝ) (S : Finset X) : Prop :=
  ∀ x ∈ S, I.c x ≤ lam (I.side x) * I.support S x

/-- `S(λ)`, the **union of all `λ`-stable profiles** (p.33). -/
noncomputable def stableUnion (I : BipInst X) (lam : Fin 2 → ℝ) : Finset X :=
  haveI := Classical.decPred (I.IsStable lam)
  (Finset.univ.powerset.filter (I.IsStable lam)).sup id

end BipInst

end CritContracts


