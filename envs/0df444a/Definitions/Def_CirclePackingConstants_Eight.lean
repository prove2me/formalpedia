-- Prove2me | Definitions.Def_CirclePackingConstants_Eight
-- name    : CirclePackingConstants_Eight
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-06T08:48:54.397499+00:00
-- url     : https://prove2.me/theorems/75b778fe-4712-4645-acb9-8bfecf7f37b8
-- title:
--   The eight cells $\sigma_1,\dots,\sigma_8$ of Schaer–Meir
-- statement:
--   Let $s=(2-\sqrt3)/2$, so that $d_8^2=2-\sqrt3=2s$ for the optimal separation $d_8=\sqrt{2-\sqrt3}=(\sqrt6-\sqrt2)/2$ of eight points in the unit square. We use coordinates $(u,v)=(x-\tfrac12,\,y-\tfrac12)$ centred at the centre $C$ of the unit square.
--
--   Schaer and Meir (1965, Proposition 2) cover the square by eight sets $\sigma_1,\dots,\sigma_8$, each of diameter at most $d_8$: four corner squares $[s,\tfrac12]^2$ (and its rotations by multiples of $90^\circ$), which contain the corners $A_1,\dots,A_4$, and four pentagons $C\,H_i\,E_i\,D_{i+1}\,H_{i+1}$ filling the arms of the central cross $\{|u|\le s\}\cup\{|v|\le s\}$, where $H_i=(\pm s,\pm s)$. `eightCell i p` states that the point $p$ lies in the *closed* cell number $i$ (numbered $0,\dots,7$; even indices are corner squares, odd indices arms; index $7$ is the right arm $\{|v|\le s,\ |v|\le u\le \tfrac12\}$ and index $1$ the top arm).
--
--   **Formalization Note.** In the paper the cells are made disjoint by removing boundary segments and the point $C$; here they are closed, which suffices for the argument.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Proposition 2 and Figure 3.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

/-- The constant `s = (2 - √3)/2`, so that `d₈² = 2 - √3 = 2 s` and `d₈ = (√6 - √2)/2` is the optimal
separation of eight points in the unit square. -/
def eightS : ℝ := (2 - Real.sqrt 3) / 2

/-- The eight closed cells `σ₁, …, σ₈` of Schaer–Meir, in coordinates centred at the centre of the
unit square, `(u, v) = (x - 1/2, y - 1/2)`.  Even indices `0,2,4,6` are the four corner squares
`[s, 1/2]²` and its rotations (they contain the corners `A₁, A₂, A₃, A₄`); odd indices `1,3,5,7`
are the four pentagons `C H E D H' C` (they contain the arms of the central cross: top, left,
bottom, right).  Index `7` is the right arm `{ |v| ≤ s, |v| ≤ u ≤ 1/2 }`. -/
def eightCell (i : Fin 8) (p : Point) : Prop :=
  match i.val with
  | 0 => eightS ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ eightS ≤ p.2 ∧ p.2 ≤ 1 / 2
  | 1 => -eightS ≤ p.1 ∧ p.1 ≤ eightS ∧ -p.2 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 / 2
  | 2 => -(1 / 2) ≤ p.1 ∧ p.1 ≤ -eightS ∧ eightS ≤ p.2 ∧ p.2 ≤ 1 / 2
  | 3 => -eightS ≤ p.2 ∧ p.2 ≤ eightS ∧ p.1 ≤ -p.2 ∧ p.1 ≤ p.2 ∧ -(1 / 2) ≤ p.1
  | 4 => -(1 / 2) ≤ p.1 ∧ p.1 ≤ -eightS ∧ -(1 / 2) ≤ p.2 ∧ p.2 ≤ -eightS
  | 5 => -eightS ≤ p.1 ∧ p.1 ≤ eightS ∧ p.2 ≤ -p.1 ∧ p.2 ≤ p.1 ∧ -(1 / 2) ≤ p.2
  | 6 => eightS ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ -(1 / 2) ≤ p.2 ∧ p.2 ≤ -eightS
  | _ => -eightS ≤ p.2 ∧ p.2 ≤ eightS ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1 / 2

end CirclePackingConstants


