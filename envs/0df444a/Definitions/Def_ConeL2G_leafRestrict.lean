-- Prove2me | Definitions.Def_ConeL2G_leafRestrict
-- name    : ConeL2G_leafRestrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:52.668504+00:00
-- url     : https://prove2.me/theorems/4497e9b5-8e2e-40c7-be65-888514049ff9
-- title:
--   Restriction $x\mapsto x_{H'}$ to the leaves
-- statement:
--   For a cone centered at $v$ and an assignment $x$, $x_{H'}$ is the restriction of $x$ to the leaves $V\setminus\{v\}$. The paper sets $\Omega_{H'}=\{x_{H'}:x\in\Omega\}$ and identifies a function $h$ on leaf colorings with the leaf function $(c,x)\mapsto h(x)$ on $\Omega$; in the formalization this is $h\circ(x\mapsto x_{H'})$.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 6, p.18

import Mathlib

namespace ConeL2G

/-- **Restriction to the leaves** `x ↦ x_{H′}` of a cone centered at `v`. Li–Oveis Gharan,
arXiv:2610.37721, Section 6, p.18: "`Ω_{H′} := {x_{H′} : x ∈ Ω}` … We will often abuse notation and
identify a leaf function `h : Ω_{H′} → ℝ` with `(c, x) ↦ h(x)` on `Ω`."

So `Ω_{H′} = (properColorings H L).image (leafRestrict v)`, and a function `h′` of the leaf colors
is identified with the leaf function `h′ ∘ leafRestrict v` on `V → Fin K`. -/
def leafRestrict {V : Type*} {K : ℕ} (v : V) (x : V → Fin K) : {u : V // u ≠ v} → Fin K :=
  fun u => x u.1

end ConeL2G


