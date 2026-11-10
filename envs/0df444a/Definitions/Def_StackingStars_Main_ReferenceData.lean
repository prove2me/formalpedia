-- Prove2me | Definitions.Def_StackingStars_Main_ReferenceData
-- name    : StackingStars_Main_ReferenceData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:43:41.295388+00:00
-- url     : https://prove2.me/theorems/96d1a9c5-7323-404a-a617-08d0b32994d2
-- title:
--   Reference data of a star (q_P, R_P, r_P, e_P, L_P, w_P, v_P, T_P), its core K_P, and size groups
-- statement:
--   For a set $S$ (the region of a star), `RefData S` is one admissible choice of reference data. It consists of a reference point $q_P$ in the kernel, a farthest point $R_P\in S$ from $q_P$ in Euclidean distance, and a point $L_P\in S$ at maximal distance from the radius line $q_PR_P$. Every theorem of the mission quantifies over all such choices, as the paper's choices are arbitrary. From it:
--
--   * $r_P=\|R_P-q_P\|$ (`r`), $e_P=(R_P-q_P)/r_P$ (`e`), and $w_P=\operatorname{dist}(L_P,q_PR_P)=|e_P\times(L_P-q_P)|$ (`w`).
--   * `IsLeft`: $L_P$ lies (weakly) to the left of the directed radius. $v_P$ (`v`) is the unit normal to $e_P$ pointing toward $L_P$: $e_P$ turned $90^\circ$ counterclockwise if $L_P$ is on the left, and clockwise otherwise.
--   * `tri` $=T_P=\triangle q_PL_PR_P$.
--   * the core `core` $=K_P=\triangle q'_PR'_PL'_P$ with $q'_P=(q_P+R_P)/2+w_Pv_P/10$, $R'_P=q'_P+(R_P-q_P)/10$, $L'_P=q'_P+(L_P-q_P)/10$.
--   * `InGroup r w`: $r_P\in(r/2,r]$ and $w_P\in(w/2,w]$, so the star lies in the size group with scales $r,w$.
--   * `rMax`, `wMax`: $r_{\max}=\max_Pr_P$ and $w_{\max}=\max_Pw_P$ over a family. `groupIdx` gives the size group $G_{a,b}$ of a star, the unique $(a,b)\in\mathbb N^2$ with $r_P\in(r_{\max}/2^{a+1},r_{\max}/2^a]$ and $w_P\in(w_{\max}/2^{b+1},w_{\max}/2^b]$, that is $a=\lfloor\log_2(r_{\max}/r_P)\rfloor$ and $b=\lfloor\log_2(w_{\max}/w_P)\rfloor$.
--
--   **Formalization Note.** The paper's "without loss of generality $L_P$ lies to the left of the directed radius" is not imposed on the input. Instead $v_P$ points toward $L_P$ on either side, which is the mirror image of the paper's left-side case.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 11 (§3.1 reference data), p. 12 (size groups), p. 20 (cores)

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon

namespace StackingStars.Main

/-!
# Reference data of a star: `q_P, R_P, r_P, e_P, L_P, w_P, v_P, T_P`, the core `K_P`, size groups

Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…), §3.1,
p. 11 (PDF 13): "We choose an arbitrary reference point q_P deterministically in the kernel […] Let
R_P be an arbitrary farthest point in P from q_P, and let r_P be the radius length […] Let
e_P = (R_P − q_P)/r_P […] Let L_P be an arbitrary point in P that maximizes the distance from the
radius line q_P R_P, and let w_P = dist(L_P, q_P R_P) be the width of P. Let v_P be the unit vector
perpendicular to e_P pointing toward L_P. […] Let T_P denote the triangle △q_P L_P R_P." p. 12
(PDF 14): size groups. p. 20 (PDF 22): cores.

`RefData S` is one admissible choice of `(q_P, R_P, L_P)` for the set `S`; every statement of the
mission quantifies over all such choices. The paper's "without loss of generality L_P lies to the
left of the directed radius" is not imposed: `IsLeft` records the side, and `v_P` points toward
`L_P` on either side.
-/

/-- An admissible choice of reference data for `S`: `q` in the kernel, `R` a farthest point of `S`
from `q` (Euclidean distance), `L` a point of `S` at maximal distance from the line `qR`
(`|(R − q) × (z − q)|` is `‖R − q‖` times that distance). -/
structure RefData (S : Set Pt) where
  /-- the reference point `q_P` -/
  q : Pt
  /-- the far endpoint `R_P` of the radius -/
  R : Pt
  /-- the width point `L_P` -/
  L : Pt
  q_mem : q ∈ kernel S
  R_mem : R ∈ S
  R_far : ∀ z ∈ S, len (z - q) ≤ len (R - q)
  L_mem : L ∈ S
  L_far : ∀ z ∈ S, |cross (R - q) (z - q)| ≤ |cross (R - q) (L - q)|

namespace RefData

variable {S : Set Pt} (D : RefData S)

/-- The radius length `r_P = ‖R_P − q_P‖`. -/
noncomputable def r : ℝ := len (D.R - D.q)

/-- The orientation `e_P = (R_P − q_P)/r_P`. -/
noncomputable def e : Pt := (1 / D.r) • (D.R - D.q)

/-- The width `w_P = dist(L_P, line q_P R_P) = |e_P × (L_P − q_P)|`. -/
noncomputable def w : ℝ := |cross D.e (D.L - D.q)|

/-- `L_P` lies (weakly) to the left of the directed radius `q_P → R_P`. -/
def IsLeft : Prop := 0 ≤ cross (D.R - D.q) (D.L - D.q)

open Classical in
/-- `v_P`: the unit vector perpendicular to `e_P` pointing toward `L_P` (`e_P` turned by 90°
counterclockwise when `L_P` is on the left, clockwise when it is on the right). -/
noncomputable def v : Pt := if D.IsLeft then rotCCW D.e else rotCW D.e

/-- The triangle `T_P = △ q_P L_P R_P`. -/
def tri : Set Pt := convexHull ℝ {D.q, D.L, D.R}

/-- `q′_P = (q_P + R_P)/2 + w_P v_P / 10`. -/
noncomputable def q' : Pt := (1 / 2 : ℝ) • (D.q + D.R) + (D.w / 10) • D.v

/-- The core `K_P = △ q′_P R′_P L′_P`, with `R′_P = q′_P + (R_P − q_P)/10` and
`L′_P = q′_P + (L_P − q_P)/10` (p. 20, PDF 22). -/
noncomputable def core : Set Pt :=
  convexHull ℝ {D.q', D.q' + (1 / 10 : ℝ) • (D.R - D.q), D.q' + (1 / 10 : ℝ) • (D.L - D.q)}

/-- The star lies in the size group with scales `r`, `w`: `r_P ∈ (r/2, r]` and `w_P ∈ (w/2, w]`
(p. 12, PDF 14). -/
def InGroup (r w : ℝ) : Prop := r / 2 < D.r ∧ D.r ≤ r ∧ w / 2 < D.w ∧ D.w ≤ w

end RefData

/-- `r_max = max_P r_P` over a family of reference data. -/
noncomputable def rMax {n : ℕ} {S : Fin n → Set Pt} (D : ∀ i, RefData (S i)) : ℝ :=
  ⨆ i, (D i).r

/-- `w_max = max_P w_P` over a family of reference data. -/
noncomputable def wMax {n : ℕ} {S : Fin n → Set Pt} (D : ∀ i, RefData (S i)) : ℝ :=
  ⨆ i, (D i).w

/-- The size group `G_{a,b}` of star `i` (p. 12, PDF 14): the unique `(a, b) ∈ ℕ²` with
`r_P ∈ (r_max/2^{a+1}, r_max/2^a]` and `w_P ∈ (w_max/2^{b+1}, w_max/2^b]`, i.e.
`a = ⌊log₂(r_max/r_P)⌋`, `b = ⌊log₂(w_max/w_P)⌋`. -/
noncomputable def groupIdx {n : ℕ} {S : Fin n → Set Pt} (D : ∀ i, RefData (S i)) (i : Fin n) :
    ℕ × ℕ :=
  (⌊Real.logb 2 (rMax D / (D i).r)⌋₊, ⌊Real.logb 2 (wMax D / (D i).w)⌋₊)

end StackingStars.Main


