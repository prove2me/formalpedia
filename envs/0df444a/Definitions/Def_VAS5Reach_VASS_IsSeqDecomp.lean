-- Prove2me | Definitions.Def_VAS5Reach_VASS_IsSeqDecomp
-- name    : VAS5Reach_VASS_IsSeqDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:29.130712+00:00
-- url     : https://prove2.me/theorems/5323795f-8a5a-4be8-be12-c88207eaf0aa
-- title:
--   Sequential VASS $U = (U_1)u_1(U_2)\cdots u_{k-1}(U_k)$
-- statement:
--   Let $U_1, \dots, U_k$ be strongly connected $d$-VASS with pairwise disjoint state sets, and for $i < k$ let $u_i = (q_i, a_i, p_{i+1})$ with $q_i \in Q_i$, $p_{i+1} \in Q_{i+1}$ be a **bridge**. The **sequential VASS** $U = (U_1)u_1(U_2)\cdots u_{k-1}(U_k)$ has state set $\bigcup_i Q_i$ and transition set $\bigcup_i T_i \cup \{u_1, \dots, u_{k-1}\}$ (`IsSeqDecomp`). A VASS is **strongly connected** if every state has a path to every state (`IsStronglyConnected`), and $U$ is a **sub-VASS** of $V$ if its states and transitions are among those of $V$ (`IsSubVASS`).
--
--   When a sequential VASS is considered together with a designated run from $p$ to $q$, the paper retains only the traversed components, so that $p$ lies in $U_1$ and $q$ in $U_k$; `IsSequential U p q` records this.
--
--   **Formalization Note** The $k$ components are indexed by $0, \dots, k-1$ (written `Fin (k+1)` with the paper's $k$ shifted by one) and the bridges by $0, \dots, k-2$.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'B-Encoding and Sequential VASS', p.16 (PDF p.18)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun

namespace VAS5Reach

namespace VASS

variable {S ι : Type}

/-- `U` is a sub-VASS of `V`: its states and transitions are among those of `V`. -/
def IsSubVASS (U V : VASS S ι) : Prop :=
  U.states ⊆ V.states ∧ U.trans ⊆ V.trans

/-- `V` is strongly connected: every state of `V` has a path of `V` to every state of `V`
(a one-state VASS with no transitions is strongly connected through the empty path). -/
def IsStronglyConnected (V : VASS S ι) : Prop :=
  ∀ p ∈ V.states, ∀ q ∈ V.states, ∃ π, IsPath V p π q

/-- `IsSeqDecomp U k C b`: `U` is the sequential VASS `U = (U₁) u₁ (U₂) ⋯ u_{k} (U_{k+1})` with
components `C 0, …, C k` (the paper's `U₁, …, U_{k+1}`) and bridges `b 0, …, b (k−1)` (the paper's
`u₁, …, u_k`): each component is strongly connected, the components have pairwise disjoint state
sets, the bridge `b i = (qᵢ, aᵢ, pᵢ₊₁)` leads from a state of component `i` to a state of component
`i + 1`, the state set of `U` is the union of the components' state sets, and its transition set is
the union of the components' transition sets and the bridges.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 "B-Encoding and
Sequential VASS", printed p. 16 (PDF p. 18): "Let Ui = (Qi, Ti), for i ∈ [k], be strongly connected
d-VASS with pairwise disjoint state sets, and, for i ∈ [k − 1], let ui = (qi, ai, pi+1) with
qi ∈ Qi and pi+1 ∈ Qi+1 be a bridge. The sequential VASS U = (U1)u1(U2) · · · uk−1(Uk) has state set
⋃i Qi and transition set ⋃i Ti ∪ {u1, . . . , uk−1}."

**Formalization Note** The paper's `k` components are indexed here by `Fin (k + 1)` (so the
paper's `k` is `k + 1` here, and there is at least one component), and the bridges by `Fin k`;
`C 0` is the first component `U₁` and `C (Fin.last k)` the last component. -/
def IsSeqDecomp (U : VASS S ι) (k : ℕ) (C : Fin (k + 1) → VASS S ι)
    (b : Fin k → S × (ι → ℤ) × S) : Prop :=
  (∀ i, IsStronglyConnected (C i)) ∧
  (∀ i j, i ≠ j → Disjoint (C i).states (C j).states) ∧
  (∀ i : Fin k, (b i).1 ∈ (C i.castSucc).states ∧ (b i).2.2 ∈ (C i.succ).states) ∧
  (∀ p, p ∈ U.states ↔ ∃ i, p ∈ (C i).states) ∧
  (∀ τ, τ ∈ U.trans ↔ (∃ i, τ ∈ (C i).trans) ∨ ∃ i, τ = b i)

/-- `IsSequential U p q`: `U` is a sequential VASS whose source state `p` lies in its first
component and whose target state `q` lies in its last component. This is the paper's convention
for a sequential VASS considered together with a designated run from a state `p` to a state `q`.

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, printed p. 16 (PDF p. 18): "When
considering a sequential VASS together with a designated run or Z-run, we retain only the
components traversed by that run and index them as U1, . . . , Uk. Thus its source and target
states belong to U1 and Uk, respectively." -/
def IsSequential (U : VASS S ι) (p q : S) : Prop :=
  ∃ (k : ℕ) (C : Fin (k + 1) → VASS S ι) (b : Fin k → S × (ι → ℤ) × S),
    IsSeqDecomp U k C b ∧ p ∈ (C 0).states ∧ q ∈ (C (Fin.last k)).states

end VASS

end VAS5Reach


