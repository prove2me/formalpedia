-- Prove2me | Definitions.Def_PrivLittlestone_oddceil
-- name    : PrivLittlestone_oddceil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:48.925195+00:00
-- url     : https://prove2.me/theorems/1e9a522b-d20d-4281-a0a1-3f565b948e20
-- title:
--   $\mathrm{oddceil}(x)$, the smallest odd integer at least $x$
-- statement:
--   $\mathrm{oddceil}(x)$ is the smallest odd integer at least $x$.
--
--   **Formalization Note** Natural-number valued; it agrees with the definition for $x > 0$, the only use, and returns $1$ for $x \le 0$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (11), p.10

import Mathlib

namespace PrivLittlestone

/-- `oddceil(x)`, **the smallest odd integer at least `x`** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
(11), p.10).

**Formalization Note** Valued in `ℕ`; it agrees with the paper for `x > 0` (every use), and
returns `1` for `x ≤ 0`. -/
noncomputable def oddceil (x : ℝ) : ℕ :=
  if Odd ⌈x⌉₊ then ⌈x⌉₊ else ⌈x⌉₊ + 1

end PrivLittlestone


