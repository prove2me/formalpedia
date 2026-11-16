-- Prove2me | Definitions.Def_QPVEntanglement_Supplement_GeometryD
-- name    : QPVEntanglement_Supplement_GeometryD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:16:58.570659+00:00
-- url     : https://prove2.me/theorems/c79d213b-d53e-4509-9eab-65acc7c7cd04
-- title:
--   $d$-dimensional mobile-verifier geometry (Definition 4)
-- statement:
--   Let $d\ge1$. A **$d$-dimensional mobile-verifier geometry** consists of a one-dimensional geometry $G$ of the mission (verifier coordinates $v_0,v_1\in\mathbb R$ and an admissible claimed coordinate $x$ strictly between them), a point $o\in\mathbb R^d$ and a unit vector $u\in\mathbb R^d$, $\|u\|_2=1$. The coordinate $r\in\mathbb R$ is placed at the point
--
--   $$\iota(r)=o+r\,u\in\mathbb R^d .$$
--
--   The verifier $V_b$ stands at $\iota(v_b)$ and the claimed location is $\iota(x)$, which lies in the convex hull of the two verifier positions and is not one of them. The space $\mathbb R^d$ carries the Euclidean distance, and signals travel at speed $1$.
--
--   This is Definition 4 of the paper: the one-dimensional protocol is translated and rotated into $\mathbb R^d$, and the whole one-dimensional configuration (the paths of the verifier inputs, the logical times, the response deadlines) is preserved. Every distance along the verifier axis equals the one-dimensional distance, so a timing schedule of the one-dimensional protocol for $G$ is a schedule of its $d$-dimensional version, unchanged.
--
--   **Formalization Note** Definition 4 puts the claimed location at the midpoint of the verifier segment (verifiers at $z\pm Ru$). Here the claimed location may be any admissible point of the segment; the midpoint placement is the case $v_0=x-R$, $v_1=x+R$. The space $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Definition 4, p.29; Definition 2 (admissible claimed location, mobile-verifier security), p.28

import Mathlib
import Definitions.Def_QPVEntanglement_Geometry

set_option autoImplicit false

namespace QPVEntanglement.Supplement

open QPVEntanglement

/-- **d-dimensional mobile-verifier geometry** (Definition 4, p.29; Definition 2, p.28).
Behera–Goyal, *Breaking the Bounded Entanglement Barrier for Quantum Position Verification*,
arXiv:2609.39234 (sha256 bdf2928d…), Definition 4, p.29.

A one-dimensional geometry `G` (verifier positions `G.v 0`, `G.v 1` and an admissible claimed
location `G.x` strictly between them) placed in `ℝ^d` along the line through the origin `o` with
unit direction `u`: the real coordinate `r` is placed at `ι r = o + r • u`. The verifier `V_b`
stands at `ι (G.v b)` and the claimed location is `ι G.x`, which lies in
`Conv(ι (G.v 0), ι (G.v 1)) \ {ι (G.v 0), ι (G.v 1)}` (admissible in the sense of Definition 2).
Definition 4: "The entire one-dimensional configuration, including the directed paths of the
verifier inputs, the logical times, and the response deadlines, is preserved by this translation
and rotation", so a timing schedule of the one-dimensional protocol for `G` is a timing
schedule of its `d`-dimensional version unchanged.

**Formalization Note.** Definition 4 puts the claimed location at the midpoint (verifiers at
`z ± R u`); here the claimed location may be any admissible point of the verifier segment and
`R` is arbitrary (a generalization: every placement `Relocate(x)` of Definition 4 is the case
`G.v 0 = G.x − R`, `G.v 1 = G.x + R`). `ℝ^d` is `EuclideanSpace ℝ (Fin d)` with its Euclidean
distance; the speed of light is `1`. -/
structure GeometryD (d : ℕ) where
  /-- the underlying one-dimensional configuration (positions along the verifier axis) -/
  G : Geometry
  /-- the point of `ℝ^d` with axis coordinate `0` -/
  o : EuclideanSpace ℝ (Fin d)
  /-- the direction of the verifier axis -/
  u : EuclideanSpace ℝ (Fin d)
  /-- `u` is a unit vector -/
  u_norm : ‖u‖ = 1

namespace GeometryD

variable {d : ℕ}

/-- The point `ι r = o + r • u` of `ℝ^d` with axis coordinate `r`. -/
noncomputable def embed (GD : GeometryD d) (r : ℝ) : EuclideanSpace ℝ (Fin d) := GD.o + r • GD.u

/-- The position `ι (G.v b)` of the verifier `V_b`. -/
noncomputable def verifier (GD : GeometryD d) (b : Fin 2) : EuclideanSpace ℝ (Fin d) :=
  GD.embed (GD.G.v b)

/-- The claimed location `ι G.x`. -/
noncomputable def claimed (GD : GeometryD d) : EuclideanSpace ℝ (Fin d) := GD.embed GD.G.x

end GeometryD

end QPVEntanglement.Supplement


