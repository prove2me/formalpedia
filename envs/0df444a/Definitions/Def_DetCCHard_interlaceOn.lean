-- Prove2me | Definitions.Def_DetCCHard_interlaceOn
-- name    : DetCCHard_interlaceOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:23.822252+00:00
-- url     : https://prove2.me/theorems/0aabb9a0-3cf0-4ea4-9a16-bf2037c5d781
-- title:
--   Interlace of a base matrix on a tuple list, its row weights and block weights
-- statement:
--   For a base matrix $R : X \times Y \to \{0,1\}$ and a tuple list $(L, \nu, z)$ of length $q$, the **interlace** has rows $(i, u) \in [q] \times X$, a column for each label $\ell \in L$, and entry
--   $$
--   I(R)\bigl((i, u), \ell\bigr) = R\bigl(u, z_i(\ell)\bigr).
--   $$
--   Row $(i, u)$ has weight $\mu_X(u)/q$ and column $\ell$ has weight $\nu(\ell)$. **Block** $i$ is the row set $\{i\} \times X$, and the **base row weight retained in block $i$** by a set $U$ of rows is $\mu_X(\{u : (i, u) \in U\})$, without division by $q$.
--
--   On the full product this is the full $q$-fold interlace $I_q(R)$ of Definition 4.3. Interlacing is the step of each round that adds communication.
--
--   **Formalization Note** Blocks are indexed from $0$. The transpose of an interlace is written directly as the function with swapped arguments.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definitions 4.3 and 4.4, pp.14–15

import Mathlib
import Definitions.Def_DetCCHard_TupleList

namespace DetCCHard

/-- The **interlace of a base matrix on a tuple list** (Gaspers–He–Mackenzie, arXiv:2508.05597,
held version sha256 ad552d13…a4a03, Definitions 4.3 and 4.4, pp.14–15): for `R : X × Y → {0, 1}`
and a tuple list `T` of length `q`, the table with rows `(i, u) ∈ [q] × X`, a column for each
label `ℓ`, and entry `R(u, z_i(ℓ))`. Block `i` is the row set `{i} × X`.

**Formalization Note** Blocks are indexed from `0` (`Fin q`). The full `q`-fold interlace `I_q(R)`
of Definition 4.3 is the case of the full product list (labels `Y^q`, identity decoder, product
weights). -/
def interlaceOn {X Y : Type} {q : ℕ} (R : X → Y → Bool) (T : TupleList Y (Fin q)) :
    Fin q × X → T.L → Bool :=
  fun r ℓ => R r.2 (T.z ℓ r.1)

/-- The **row weights of an interlace** (Definition 4.3, p.14): row `(i, u)` has weight
`μX(u)/q`. -/
def interlaceRowWt {X : Type} (μX : X → ℚ) (q : ℕ) : Fin q × X → ℚ :=
  fun r => μX r.2 / q

/-- The **base row weight retained in block `i`** by a set `U` of interlace rows (Definition 4.4,
p.15: "we measure row weight within a block by the base row weights, without division by `q`"):
`μX({u : (i, u) ∈ U})`. -/
noncomputable def blockWt {X : Type} [Fintype X] {q : ℕ} (μX : X → ℚ) (U : Set (Fin q × X))
    (i : Fin q) : ℚ :=
  wt μX {u | (i, u) ∈ U}

end DetCCHard


