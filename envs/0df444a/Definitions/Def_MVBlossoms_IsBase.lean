-- Prove2me | Definitions.Def_MVBlossoms_IsBase
-- name    : MVBlossoms_IsBase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:41:59.37554+00:00
-- url     : https://prove2.me/theorems/6e9da26e-b19e-42fe-8bb8-df1529ab2a29
-- title:
--   The base of a vertex
-- statement:
--   The **base** of $v$ is $b$ when $B(v)=\{b\}$. A vertex that is the base of some vertex of eligible tenacity is called **basal**.
--
--   **Formalization Note** The base is a relation, $B(v)=\{b\}$, rather than a function: "let $b=\mathrm{base}(v)$" becomes "for every $b$ with $B(v)=\{b\}$", and Statement 2 of Theorem 3 provides such a $b$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 21 and 29, pp.2030, 2037

import Mathlib
import Definitions.Def_MVBlossoms_baseSet

namespace MVBlossoms

/-- **The base of a vertex (as a relation).** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 21 (p.2030) and 29
(p.2037): "For each v ∈ U_t, define base(v) to be the unique vertex, say b, in the set B(v). We will
say that the base of v is b."

`IsBase M v b` means `B(v) = {b}`.

**Formalization Note.** The paper's base(v) is defined only once `B(v)` is known to be a
singleton (Theorem 3, Statement 2). Encoding it as the relation `baseSet M v = {b}` avoids any
junk value: "let b = base(v)" becomes "for every `b` with `IsBase M v b`", and Statement 2 supplies
such a `b`. -/
def IsBase {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (v b : V) : Prop :=
  baseSet M v = {b}

end MVBlossoms


