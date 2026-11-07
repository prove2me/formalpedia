-- Prove2me | Definitions.Def_OnlineCAP_active
-- name    : OnlineCAP_active
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:35.666106+00:00
-- url     : https://prove2.me/theorems/bb96d5de-fd65-42ca-b7b8-61edc0ef21a7
-- title:
--   The set A of active copies
-- statement:
--   For a fractional vector $x$ on $P$, the set of **active copies** is
--   $$A=\bigcup_{p\in P}\{p\}\times[a_p]\subseteq\mathcal P,$$
--   the first $a_p$ copies of every point $p$.
--
--   **Formalization Note** Copies are numbered from $0$, so $[a_p]=\{0,\dots,a_p-1\}$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.16

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_zvec
import Definitions.Def_OnlineCAP_acount

namespace OnlineCAP

/-- **The active copies `A`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, p.16 (PDF p.16): "A^t := ⋃_{p∈P} ({p} × [a^t_p]) ⊆ 𝒫
is the set of all active copies at time t".

`active P x` is the set of virtual points `(p, i)` with `i < a_p`: the first `a_p` copies of each
point `p`.

**Formalization Note.** Copies are indexed from `0`, so `[a_p]` is `{0, …, a_p − 1}`. -/
noncomputable def active (P : Finset (ℝ × ℝ)) (x : ↥P → ℝ) : Finset (VirtualPt P) :=
  Finset.univ.filter (fun e => e.2.val < acount P x e.1)

end OnlineCAP


