-- Prove2me | Definitions.Def_StackingStars_Main_FineType
-- name    : StackingStars_Main_FineType
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:44:42.533017+00:00
-- url     : https://prove2.me/theorems/f0f6665a-cae3-4967-93ba-39a3becf6020
-- title:
--   Fine types of a size group: N = 100⌈r/w⌉ directions d_τ, the perpendicular u_τ, and the fine type of a star
-- statement:
--   Fix a size group with scales $r,w$. Let $N=100\lceil r/w\rceil$ (`numDirs`) and $\delta=2\pi/N$ (`delta`). A fine type $\tau$ (`FineType`) consists of a direction index $k$ and a side (left or right). Its direction is $d_\tau=(\cos k\delta,\sin k\delta)$ (`d`). Its perpendicular $u_\tau$ (`u`) is $d_\tau$ turned $90^\circ$ clockwise for the left side, and counterclockwise for the mirrored right side.
--
--   A star with reference data $D$ has fine type $\tau$ (`HasFineType r w D τ`) when $k<N$, the side of $\tau$ is the side of $L_P$, and
--   $$d_\tau=\sin\beta\,e_P+\cos\beta\,v_P\qquad\text{for some }\beta\in[\delta,2\delta).$$
--   For a left-side star, $\beta$ is the clockwise angular displacement from $v_P$ toward $d_\tau$, as on p. 12. Then $u_\tau=\cos\beta\,e_P-\sin\beta\,v_P$ on both sides. Every star has exactly one fine type.
--
--   **Formalization Note.** The paper records the side of $L_P$ in the fine type (p. 5) and treats left-side stars, which is its WLOG on p. 11. Right-side stars get the mirrored family, so no input is excluded.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 12, Eq. (2) and fine types; p. 5

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_ReferenceData

namespace StackingStars.Main

/-!
# Fine types

Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…), §3.1,
p. 12 (PDF 14): "Define N = 100⌈r/w⌉ as the number of fine types in the size group and
δ = 2π/N ≤ π/50 (2) as the angle range of each fine type. Let D = {(cos kδ, sin kδ) : 0 ≤ k < N}
[…] We create a fine type τ for each vector d_τ ∈ D, and let u_τ be the unit vector obtained by
rotating d_τ by 90 degrees clockwise. For each star P, we associate it with the unique fine type τ
such that the clockwise angular displacement β_P from v_P toward d_τ is in [δ, 2δ). In other words,
d_τ = sin β_P e_P + cos β_P v_P, u_τ = cos β_P e_P − sin β_P v_P." p. 5 (PDF 7): "the fine type
of a star is the interval containing its orientation, together with the side of the radius on
which L_P lies".

A fine type is a direction index `k < N` and a side. The paper treats left-side stars
(`L_P` left of the radius, its WLOG on p. 11); a right-side star is the mirror image, for which
the displacement is counterclockwise and `u_τ` is `d_τ` turned 90° counterclockwise. On both sides
`d_τ = sin β e_P + cos β v_P` and `u_τ = cos β e_P − sin β v_P` with `β ∈ [δ, 2δ)`.
-/

/-- A fine type: the index `k` of the direction `d_τ = (cos kδ, sin kδ)`, and the side of `L_P`. -/
structure FineType where
  /-- direction index, `0 ≤ k < N` -/
  k : ℕ
  /-- `true`: `L_P` lies left of the directed radius -/
  left : Bool

/-- `N = 100 ⌈r/w⌉`, the number of directions in the size group with scales `r`, `w`. -/
noncomputable def numDirs (r w : ℝ) : ℕ := 100 * ⌈r / w⌉₊

/-- `δ = 2π/N`. -/
noncomputable def delta (r w : ℝ) : ℝ := 2 * Real.pi / numDirs r w

namespace FineType

/-- `d_τ = (cos kδ, sin kδ)`. -/
noncomputable def d (r w : ℝ) (τ : FineType) : Pt :=
  (Real.cos (τ.k * delta r w), Real.sin (τ.k * delta r w))

/-- `u_τ`: `d_τ` turned by 90° clockwise (left side) or counterclockwise (mirrored right side). -/
noncomputable def u (r w : ℝ) (τ : FineType) : Pt :=
  if τ.left then rotCW (τ.d r w) else rotCCW (τ.d r w)

end FineType

/-- The star with reference data `D` has fine type `τ` in the size group with scales `r`, `w`:
`k < N`, the side of `τ` is the side of `L_P`, and `d_τ = sin β e_P + cos β v_P` for some
`β ∈ [δ, 2δ)`. -/
def HasFineType {S : Set Pt} (r w : ℝ) (D : RefData S) (τ : FineType) : Prop :=
  τ.k < numDirs r w ∧ (τ.left = true ↔ D.IsLeft) ∧
    ∃ β ∈ Set.Ico (delta r w) (2 * delta r w), τ.d r w = Real.sin β • D.e + Real.cos β • D.v

end StackingStars.Main


