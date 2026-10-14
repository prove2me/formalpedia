-- Prove2me | Definitions.Def_ThomsonCampaign_Configurations
-- name    : ThomsonCampaign_Configurations
-- status  : Definition
-- author  : @vatsj
-- created : 2026-10-13T22:06:09.244975+00:00
-- url     : https://prove2.me/theorems/ec77a7a2-0d57-4ed1-92ae-b5b969d6ba5c
-- title:
--   Conjectured minimisers for N = 9, 10 and 32
-- statement:
--   Three explicit point configurations on the unit sphere.
--
--   - **Capped square antiprism** (10 points, parameter $h$): a square at height $h$ with vertices at angles $\pi k/2$, a square at height $-h$ turned by $\pi/4$, and the two poles.
--   - **Tricapped trigonal prism** (9 points, parameter $z$): triangles at heights $\pm z$ with vertices at angles $2\pi k/3$, and three points on the equator at angles $\pi/3 + 2\pi k/3$.
--   - **Icosahedron plus dodecahedron** (32 points): the 12 vertices $(0,\pm1,\pm\varphi)$ and cyclic permutations, together with the 20 vertices of the dual dodecahedron, $(\pm1,\pm1,\pm1)$ and the cyclic permutations of $(\pm1/\varphi, 0, \pm\varphi)$, each scaled to unit length, where $\varphi$ is the golden ratio. Each dodecahedron vertex is the centre of an icosahedron face.
--
--   Numerically, the first two have their lowest energy at $h \approx 0.42269$ (energy $\approx 32.716949$) and $z \approx 0.70365$ (energy $\approx 25.759987$); the third has energy $\approx 412.261275$.
-- source:
--   Numerically best-known Thomson minimisers for N = 9, 10, 32; the N = 9 family is taken from the N = 7 package's stretch target (https://github.com/huwngtran/thomson-n7-lean).

import Mathlib
import Definitions.Def_ThomsonCampaign_Basic

open Real

namespace ThomsonCampaign

/-- The D4d capped square antiprism with parameter `h`: indices `0..3` the top square (height `h`,
angles `πk/2`), `4..7` the bottom square (height `-h`, angles `π/4 + πk/2`), `8` north pole, `9` south pole. -/
noncomputable def cappedSquareAntiprism (h : ℝ) : Fin 10 → R3 := fun i =>
  if (i : ℕ) < 4 then cyl (√(1 - h ^ 2)) (π * (i : ℕ) / 2) h
  else if (i : ℕ) < 8 then cyl (√(1 - h ^ 2)) (π / 4 + π * ((i : ℕ) - 4) / 2) (-h)
  else if (i : ℕ) = 8 then cyl 0 0 1
  else cyl 0 0 (-1)

/-- The D3h tricapped trigonal prism with parameter `z`: indices `0..2` top triangle (height `z`),
`3..5` bottom triangle (height `-z`), `6..8` equatorial caps at angles `π/3 + 2πk/3`. -/
noncomputable def triCapPrism (z : ℝ) : Fin 9 → R3 := fun i =>
  if (i : ℕ) < 3 then cyl (√(1 - z ^ 2)) (2 * π * (i : ℕ) / 3) z
  else if (i : ℕ) < 6 then cyl (√(1 - z ^ 2)) (2 * π * ((i : ℕ) - 3) / 3) (-z)
  else cyl 1 (π / 3 + 2 * π * ((i : ℕ) - 6) / 3) 0

/-- Unnormalised vertices: an icosahedron (12 points, `(0,±1,±φ)` and cyclic permutations) followed
by the dual dodecahedron (20 points, `(±1,±1,±1)`, `(0,±1/φ,±φ)`-type, with `(±1/φ,0,±φ)` etc. oriented
so that each dodecahedron vertex is the centre of an icosahedron face). -/
noncomputable def icoDodecaRaw : Fin 32 → R3 :=
  let p := goldenRatio
  ![!₂[0, 1, p],
    !₂[1, p, 0],
    !₂[p, 0, 1],
    !₂[0, 1, -p],
    !₂[1, -p, 0],
    !₂[-p, 0, 1],
    !₂[0, -1, p],
    !₂[-1, p, 0],
    !₂[p, 0, -1],
    !₂[0, -1, -p],
    !₂[-1, -p, 0],
    !₂[-p, 0, -1],
    !₂[1, 1, 1],
    !₂[1, 1, -1],
    !₂[1, -1, 1],
    !₂[1, -1, -1],
    !₂[-1, 1, 1],
    !₂[-1, 1, -1],
    !₂[-1, -1, 1],
    !₂[-1, -1, -1],
    !₂[1 / p, 0, p],
    !₂[1 / p, 0, -p],
    !₂[-1 / p, 0, p],
    !₂[-1 / p, 0, -p],
    !₂[p, 1 / p, 0],
    !₂[p, -1 / p, 0],
    !₂[-p, 1 / p, 0],
    !₂[-p, -1 / p, 0],
    !₂[0, p, 1 / p],
    !₂[0, p, -1 / p],
    !₂[0, -p, 1 / p],
    !₂[0, -p, -1 / p]]

/-- The icosahedron-plus-dodecahedron configuration on the unit sphere (32 points). -/
noncomputable def icoDodeca (i : Fin 32) : R3 := ‖icoDodecaRaw i‖⁻¹ • icoDodecaRaw i

end ThomsonCampaign


