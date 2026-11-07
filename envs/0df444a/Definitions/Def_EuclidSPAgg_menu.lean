-- Prove2me | Definitions.Def_EuclidSPAgg_menu
-- name    : EuclidSPAgg_menu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:34.847755+00:00
-- url     : https://prove2.me/theorems/f3dd797a-8151-4859-850e-bacc9e090961
-- title:
--   Unilateral menu $M_i(x_{-i})$
-- statement:
--   For a mechanism $f$, an agent $i$ and reports $x_{-i}$ of the other agents, the **unilateral menu** is the set of outcomes agent $i$ can obtain by varying its own report:
--   $$
--   M_i(x_{-i})=C_{\{i\}}(x_{-i})=\{f(a,x_{-i}):a\in E\}.
--   $$
--
--   **Formalization Note** The menu is written as a function of a whole profile $x$; the entry $x_i$ is overwritten and does not matter.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The unilateral menu `M_i(x₋ᵢ) = C_{i}(x₋ᵢ) = {f(a, x₋ᵢ) : a ∈ E}` of agent `i` against the
reports `x₋ᵢ` of the others (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.2, p.9 (PDF p.11)).

**Formalization Note** The menu does not depend on `x i`: `Function.update x i a` overwrites it,
so `menu f i x` is the paper's `M_i(x₋ᵢ)` with `x₋ᵢ` the other coordinates of `x`. -/
def menu {n d : ℕ} (f : Mech n d) (i : Fin n) (x : Fin n → E d) : Set (E d) :=
  Set.range fun a : E d => f (Function.update x i a)

end EuclidSPAgg


