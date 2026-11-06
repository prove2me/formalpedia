-- Prove2me | Definitions.Def_DecodablePOMDP_Params
-- name    : DecodablePOMDP_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:52.069727+00:00
-- url     : https://prove2.me/theorems/b29257cd-a176-48a0-90d5-5d557b9231d5
-- title:
--   The parameters $L$ and $\eta$ of (8)
-- statement:
--   For a horizon $H$, $\rho\in(0,1]$ and $\varepsilon>0$,
--
--   $$L=\min\Big\{H,\Big\lceil\frac2\rho\log\frac{4H^2}{\varepsilon}\Big\rceil\Big\},\qquad \eta=\frac{\varepsilon}{8H^2}.\tag{8}$$
--
--   With these choices the killing loss and the planner error are each at most $\varepsilon/4$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The paper needs an integer $L\ge1$; when $\varepsilon\ge4H^2$ the printed ceiling is $\le0$ and the formalization takes $L=1$. For $\varepsilon<4H^2$ and $H\ge1$ the value is the printed one.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.3, p.12, (8)

import Mathlib

namespace DecodablePOMDP

/-- **Killing length** `L := min{H, ⌈(2/ρ) log(4H²/ε)⌉}` of (8) (§4.3, p.12).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.3, p.12, (8): "Set
L := min{H, ⌈(2/ρ) log (4H²/ε)⌉} and η := ε/(8H²)."

**Formalization Note.** `log` is the natural logarithm. The paper needs an integer `L ≥ 1`
("Fix some integer L ≥ 1", p.8); when `ε ≥ 4H²` the printed ceiling is `≤ 0`, and Lean takes
`L = 1` there (`max 1 ·`). For `ε < 4H²` and `H ≥ 1` the value is the printed one. -/
noncomputable def Lsel (H : ℕ) (ρ ε : ℝ) : ℕ :=
  max 1 (min H ⌈2 / ρ * Real.log (4 * (H : ℝ) ^ 2 / ε)⌉₊)

/-- **Grid accuracy** `η := ε/(8H²)` of (8) (§4.3, p.12).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.3, p.12, (8). -/
noncomputable def ηsel (H : ℕ) (ε : ℝ) : ℝ :=
  ε / (8 * (H : ℝ) ^ 2)

end DecodablePOMDP


