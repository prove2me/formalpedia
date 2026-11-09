-- Prove2me | Definitions.Def_CutRankSched_Instance_Valid
-- name    : CutRankSched_Instance_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:31:21.837289+00:00
-- url     : https://prove2.me/theorems/e7ef22b2-ea37-42e2-bc53-13ab2511c3f5
-- title:
--   Valid instance: $\emptyset\neq\operatorname{supp}(p_i)\subseteq V(T_i)$, $T_i$ connected
-- statement:
--   An instance is **valid** if for every event $i$:
--
--   1. $p_i \in \mathbb F_2^{2m} \setminus \{0\}$ is a nonidentity Pauli vector;
--   2. $\operatorname{supp}(p_i) \subseteq V(T_i)$;
--   3. the exposure region $T_i \subseteq H$ is a connected subgraph.
--
--   Together these give $\emptyset \ne \operatorname{supp}(p_i) \subseteq V(T_i) \subseteq Q$. These are the standing assumptions of Section 3.1 under which all results of the paper are stated.
--
--   **Formalization Note** Connectedness of a subgraph in Mathlib includes nonemptiness of its vertex set.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_supp

set_option autoImplicit false

namespace CutRankSched

/-- A **valid** instance (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4): every event carries a nonidentity Pauli
vector `p_i ∈ 𝔽₂^{2m} ∖ {0}`, and its exposure region `T_i` is a connected subgraph of `H`
with `∅ ≠ supp(p_i) ⊆ V(T_i)`.

**Formalization Note** `supp(p_i) ≠ ∅` is equivalent to `p_i ≠ 0`; `Subgraph.Connected` includes
nonemptiness of `V(T_i)`. -/
def Instance.Valid (I : Instance) : Prop :=
  ∀ i : Fin I.n, I.p i ≠ 0 ∧ (↑(supp (I.p i)) : Set (Fin I.m)) ⊆ (I.T i).verts ∧ (I.T i).Connected

end CutRankSched


