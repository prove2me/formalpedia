-- Prove2me | Definitions.Def_AnchoredEP_Supplement_PthOrderMethod
-- name    : AnchoredEP_Supplement_PthOrderMethod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:11:54.751801+00:00
-- url     : https://prove2.me/theorems/2889d574-75d2-40ec-8062-d0cc5a963831
-- title:
--   Deterministic $p$th-order method on $\mathbb R^n$
-- statement:
--   For $p\ge2$, a **deterministic $p$th-order method** chooses its $t$-th query $z_t$ as an arbitrary deterministic function of the starting point $z_0$ and of the previous oracle outputs
--   $$
--   \{D^jF(z_s):0\le j\le p-1,\ 0\le s<t\},\qquad D^0F=F.
--   $$
--   Formally, a method is a family of arbitrary maps, the $t$-th of which sends the oracle outputs at $z_0,\dots,z_{t-1}$ to the next point $z_t$. No structural restriction is imposed (for instance, the iterates need not lie in the span of past derivative information).
--
--   **Formalization Note** The starting point is fixed before the method is chosen, so the dependence on $z_0$ is carried by the method itself; its $0$-th map is unused.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 6, p.12

import Mathlib
import Definitions.Def_AnchoredEP_Supplement_OracleOutput

namespace AnchoredEP.Supplement

/-- **A deterministic `p`th-order method on `ℝ^n`.** Jiang–Yoon, arXiv:2609.30212, Section 6, p.12:
"a deterministic `p`th-order method … chooses its `t`th query `z_t` as an arbitrary deterministic
function of `z₀` and the previous oracle outputs `{D^jF(z_s) : 0 ≤ j ≤ p − 1, 0 ≤ s < t}`, where
`D⁰F = F`."

A method `M : PthOrderMethod p n` is a family of arbitrary maps: `M t` sends the oracle outputs
at the queries `z_0, …, z_{t−1}` (a map `Fin t → OracleOutput p n`) to the next point `z_t`.

**Formalization Note.** No structural restriction is placed on `M` (no linear-span condition).
The starting point `z₀` is fixed before the method is chosen in Theorems 6.1 and 6.4, so the
dependence on `z₀` is carried by `M` itself; `M 0` is not used (`z_0` is the given start). -/
def PthOrderMethod (p n : ℕ) : Type :=
  (t : ℕ) → (Fin t → OracleOutput p n) → EuclideanSpace ℝ (Fin n)

end AnchoredEP.Supplement


