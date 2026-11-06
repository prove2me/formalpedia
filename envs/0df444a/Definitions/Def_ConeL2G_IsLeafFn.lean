-- Prove2me | Definitions.Def_ConeL2G_IsLeafFn
-- name    : ConeL2G_IsLeafFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:51.81125+00:00
-- url     : https://prove2.me/theorems/9d82fc43-4d68-48a3-9869-09b3d4821149
-- title:
--   Leaf functions of a cone
-- statement:
--   For a cone centered at $v$, a function $h$ of colorings is a **leaf function** if it does not depend on the color of the center: $h(x)=h(y)$ whenever $x_u=y_u$ for every $u\ne v$.
--
--   **Formalization Note** The condition is imposed on all assignments. A leaf function on $\Omega_H$ extends to one of this kind through its values on the restrictions to the leaves, and values off $\Omega_H$ never enter a $\mu$-weighted form.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 6, p.18

import Mathlib

namespace ConeL2G

/-- **A leaf function** of a cone centered at `v`: a function that does not depend on the color of
the center. Li–Oveis Gharan, arXiv:2610.37721, Section 6, p.18: "For a cone `H`, we say a function
`h : Ω_H → ℝ` is a leaf function if it does not depend on the color of the center `v`."

**Formalization Note.** Functions are on all of `V → Fin K` (realizing `L²(µ_H)`); the condition is
imposed on all assignments. Every leaf function on `Ω_H` extends to one of this kind (through its
values on the restrictions to the leaves), and values off `Ω_H` never enter a `µ`-weighted form,
so the class is the paper's. -/
def IsLeafFn {V : Type*} {K : ℕ} (v : V) (h : (V → Fin K) → ℝ) : Prop :=
  ∀ x y : V → Fin K, (∀ u, u ≠ v → x u = y u) → h x = h y

end ConeL2G


