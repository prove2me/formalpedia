-- Prove2me | Definitions.Def_OnlineCAP_acount
-- name    : OnlineCAP_acount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:42.463369+00:00
-- url     : https://prove2.me/theorems/725f675e-cfb0-4669-97d2-3a3b70176771
-- title:
--   Number of active copies a_p = ⌈n z_p⌉
-- statement:
--   For a fractional vector $x$ on $P$ with $n=|P|$, the number of **active copies** of the point $p$ is
--   $$a_p=\lceil n\,z_p\rceil ,$$
--   with $z$ the vector of eq. (2). Since $z_p\le1$, $a_p\le n$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.16

import Mathlib
import Definitions.Def_OnlineCAP_zvec

namespace OnlineCAP

/-- **Number of active copies `a_p`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, p.16 (PDF p.16): "we say that at time step t
the first a^t_p = ⌈n z^t_p⌉ copies of point p ∈ P are active". -/
noncomputable def acount (P : Finset (ℝ × ℝ)) (x : ↥P → ℝ) (p : ↥P) : ℕ :=
  ⌈(P.card : ℝ) * zvec P x p⌉₊

end OnlineCAP


