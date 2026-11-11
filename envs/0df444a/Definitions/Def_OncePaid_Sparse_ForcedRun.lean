-- Prove2me | Definitions.Def_OncePaid_Sparse_ForcedRun
-- name    : OncePaid_Sparse_ForcedRun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:40.591596+00:00
-- url     : https://prove2.me/theorems/75beade2-0d5e-4b63-84a0-ba7c60a3e07d
-- title:
--   The forced-run once-paid source of a bipartite host and the alternating target $(01)^{2n}$
-- statement:
--   Let $H$ be a bipartite host whose $2n$ vertices are listed in a fixed order $u_1,\dots,u_{2n}$. For each vertex $u$ let $Z_u$ be the **zero-run** of $u$: one position with symbol $0$ and label $e$ for every edge resource $e$ incident to $u$, each exactly once, in a fixed order. With $1[z_j]$ a single position with symbol $1$ carrying the **marker resource** $z_j$, the **forced-run source** and its target are
--
--   $$
--   w=Z_{u_1}\,1[z_1]\,Z_{u_2}\,1[z_1]\,Z_{u_3}\,1[z_2]\,Z_{u_4}\,1[z_2]\cdots Z_{u_{2n-1}}\,1[z_n]\,Z_{u_{2n}}\,1[z_n],\qquad T=(01)^{2n}.
--   $$
--
--   The resources are the edges of $H$ together with the $n$ markers; every edge resource occurs twice (once in the run of each endpoint) and every marker twice.
--
--   This source turns once-paid subsequence optimization into full edge cover plus the mandatory marker payments (Eq. (4.2)); it is the family on which the main lower bound is proved.
--
--   **Formalization Note** Symbols are `Fin 2`. The vertex order is a bijection `σ : Fin (2n) ≃ V_L ⊕ V_R` ($u_{k+1}=\sigma(k)$), the within-run orders are a function `runs` from vertices to lists of edges, and `ValidRuns runs` requires each list to contain every incident edge exactly once and nothing else. Markers are `Fin n`, 0-based: after the $k$-th zero-run ($k=0,\dots,2n-1$) comes the marker $z_{\lfloor k/2\rfloor}$. The resource type is `Edge adj ⊕ Fin n`.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 8, §2.1 and p. 21, §4.1 (PDF pp. 10, 23)

import Mathlib
import Definitions.Def_OncePaid_Sparse_OncePaid
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-!
# The forced-run once-paid source of a bipartite host

Chao, Li, Gao, Wang, *Once-Paid Subsequences and the Cost of Min-Plus Approximation*,
STOC 2027 submission (manuscript sha256 9dc21472…), p. 8 §2.1 and p. 21 §4.1.

Symbols are `Fin 2` (`0`, `1`). The resources are the edge resources `Edge adj` and `n` marker
resources `z_0, …, z_{n-1}` (`Fin n`; the paper's `z_1, …, z_n`), as `Edge adj ⊕ Fin n`.

* A vertex order is a bijection `σ : Fin (2n) ≃ V_L ⊕ V_R`: `u_{k+1} = σ k` lists the `2n`
  vertices.
* A within-run order is `runs : V_L ⊕ V_R → List (Edge adj)`; it is valid (`ValidRuns`) when
  `runs u` lists every edge incident to `u` exactly once (and nothing else).
* `Z_u` is the zero-run of `u`: one position `(0, e)` per edge `e` in `runs u`.
* The source is `w = Z_{u_1} 1[z_1] Z_{u_2} 1[z_1] Z_{u_3} 1[z_2] ⋯ Z_{u_{2n}} 1[z_n]`: after the
  `k`-th zero-run (`k = 0, …, 2n-1`) comes the singleton one-run `(1, z_{⌊k/2⌋})`.
* The target is `T = (01)^{2n}`.
-/

variable {L R : Type}

/-- The edge `e` is incident to the vertex `u`. -/
def IncidentTo {adj : L → R → Prop} (e : Edge adj) : L ⊕ R → Prop
  | Sum.inl i => e.left = i
  | Sum.inr j => e.right = j

/-- A valid within-run order: `runs u` lists every edge incident to `u` exactly once. -/
def ValidRuns {adj : L → R → Prop} (runs : L ⊕ R → List (Edge adj)) : Prop :=
  ∀ u, (runs u).Nodup ∧ ∀ e, e ∈ runs u ↔ IncidentTo e u

/-- The forced-run source
`w = Z_{σ 0} 1[z_0] Z_{σ 1} 1[z_0] Z_{σ 2} 1[z_1] Z_{σ 3} 1[z_1] ⋯ Z_{σ (2n-1)} 1[z_{n-1}]`. -/
def forcedRunSource {adj : L → R → Prop} (n : ℕ) (σ : Fin (2 * n) ≃ (L ⊕ R))
    (runs : L ⊕ R → List (Edge adj)) : List (Fin 2 × (Edge adj ⊕ Fin n)) :=
  (List.finRange (2 * n)).flatMap (fun k =>
    ((runs (σ k)).map (fun e => ((0 : Fin 2), (Sum.inl e : Edge adj ⊕ Fin n)))) ++
      [((1 : Fin 2), (Sum.inr ⟨k.val / 2, by have := k.isLt; omega⟩ : Edge adj ⊕ Fin n))])

/-- The alternating target `(01)^m`. -/
def alternatingTarget (m : ℕ) : List (Fin 2) :=
  (List.replicate m [(0 : Fin 2), 1]).flatten

end OncePaid.Sparse


