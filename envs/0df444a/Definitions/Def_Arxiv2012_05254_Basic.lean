-- Prove2me | Definitions.Def_Arxiv2012_05254_Basic
-- name    : Arxiv2012_05254_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T03:37:50.77507+00:00
-- url     : https://prove2.me/theorems/32b77c78-1663-4d90-8b38-564dc5bf6237
-- title:
--   Fringe null phase curves, closure phases and image/aperture areas of a closed interferometer polygon
-- statement:
--   Objects of Sections 2-3 and Appendices 1-2 of Thyagarajan and Carilli (2021).
--
--   1. **Planes.** In the flat-sky approximation with a coplanar aperture ($w_{ab}=0$), the image plane, with direction cosines $\hat s=(\ell,m)$, and the aperture plane, with coordinates in wavelengths, are both the Euclidean plane $\mathbb R^2$. The cross product of $v,w$ is $v_0w_1-v_1w_0$.
--   2. **Spacings.** For elements at positions $x_0,\dots,x_{n-1}$ (in wavelengths) forming an $n$-polygon in cyclic order, the spacing of side $a$ is $u_{a\lceil a+1\rfloor_n}=x_{\lceil a+1\rfloor_n}-x_a$, with indices taken mod $n$.
--   3. **Fringe null phase curves (eq. 7).** The NPC of a fringe with spacing $u$ and phase offset $\psi=\phi+2\pi n$ is the line $\{\hat s:\ 2\pi\,u\cdot\hat s+\psi=0\}$. Its signed perpendicular offset from the phase centre is $\delta s=\psi/(2\pi|u|)$ (eq. 8).
--   4. **Closure phase (eqs. 10, 11, 14).** The closure phase of an $n$-polygon with side phase offsets $\psi_{a\lceil a+1\rfloor_n}$ is $\psi_n=\sum_a\psi_{a\lceil a+1\rfloor_n}$.
--   5. **Change of phase centre (eqs. 15-16).** Measured from a phase centre $\hat s_0$, the NPC $2\pi u\cdot\hat s+\psi=0$ has phase offset $\psi'=\psi+2\pi\,u\cdot\hat s_0$.
--   6. **Element-based corruption (eq. 5).** Element phases $\xi_a=\arg G_a$ change the side phases to $\tilde\psi_{a\lceil a+1\rfloor}=\psi_{a\lceil a+1\rfloor}+\xi_{\lceil a+1\rfloor}-\xi_a$. These are real numbers, as eq. (5) is written. The corrupted visibilities are $\tilde V_{ab}=G_a^*G_bV_{ab}$ (eqs. 3-4).
--   7. **Loops and elemental triads (Appendix 2).** Phase offsets $\psi_{ij}$ given for every ordered pair of elements are read along a closed loop $v_0\to v_1\to\cdots\to v_0$. For an $N$-polygon with $N=M+2$, the $q$-th elemental triad ($q=0,\dots,M-1$; the paper writes $q=1,\dots,N-2$) consists of the elements $0,q+1,q+2$ in this order. All triads share the vertex $0$.
--   8. **Translated NPC patterns.** The NPC pattern with phases $\psi'$ is the translate by $t$ of the pattern with phases $\psi$ if every NPC of $\psi'$ is the translate by $t$ of the NPC of $\psi$ on the same side.
--   9. **Areas (eqs. 19, 28).** The NPC vertices are the points lying on the NPCs of two consecutive sides. For a triad these are the vertices of the triangle enclosed by the three NPCs (the principal triangle when the $\psi$ are the principal phases). $A_{\mathcal I n}$ is the Lebesgue area of the convex hull of the NPC vertices. $A_{\mathcal A n}$ is the Lebesgue area of the convex hull of the element positions, which is the triangle for $n=3$ and the polygon itself for a convex polygon. A polygon is strictly convex in its cyclic order if, for every side, all other elements lie strictly on one fixed side of its line.
--   10. **Fringes and three-fringe images (eq. 6, Sec. 4.1).** The fringe of a baseline with spacing $u$ and visibility $V$ is $F(\hat s)=V e^{i2\pi u\cdot\hat s}$. The three-fringe image of a closed triad is $\sum_a 2\,\mathrm{Re}\,F_{a\lceil a+1\rfloor}(\hat s)$, the sum of the three fringes and of their conjugate baselines, i.e. the dirty image of the three visibilities.
--
--   **Formalization Note** Areas are Lebesgue measures of convex hulls in $\mathbb R^2$, so they are unsigned. The paper does not say whether its areas are signed. The NPC phases are real numbers carrying the $2\pi n_{ab}$ of eq. (7). Element corruption acts on them as in eq. (5), without reduction modulo $2\pi$.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), Sections 2-3 (eqs. (1)-(19)), Section 4.1 (eq. (20)), Appendices 1-2 (eqs. (21)-(28))

import Mathlib

/-!
Thyagarajan and Carilli, *A Geometric View of Closure Phases in Interferometry*,
arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021): the flat-sky image and aperture planes,
element spacings, fringe null phase curves (NPCs), closure phases, element-based corruptions,
three-fringe interference images, and the aperture- and image-plane areas of Section 2
(eqs. (1)-(14)), Section 3 (eqs. (15)-(19)), Section 4.1 (eq. (20)) and Appendices 1-2
(eqs. (21)-(28)).
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Arxiv2012_05254

/-- Section 2 (flat-sky approximation, coplanar aperture `w_ab = 0`): both the image plane, with
direction-cosine coordinates `(ℓ, m)`, and the aperture plane, with coordinates `(u, v)` in
wavelengths, are the Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The planar cross product `v₀ w₁ - v₁ w₀` (twice the signed area of the triangle spanned by
`v` and `w`); used to state convexity of an aperture polygon (Appendix 2). -/
def cross (v w : Plane) : ℝ := v 0 * w 1 - v 1 * w 0

/-- Section 2.2, before eq. (9): for elements at positions `x a` (in wavelengths) forming an
`n`-polygon in cyclic order, the spacing of side `a` is `u_{a⌈a+1⌋_n} = x_{⌈a+1⌋_n} - x_a`
(indices mod `n`). -/
def spacing {n : ℕ} [NeZero n] (x : Fin n → Plane) (a : Fin n) : Plane := x (a + 1) - x a

/-- Eq. (7): the fringe null phase curve (NPC) of a fringe with spacing `u` and phase offset
`ψ = φ + 2πn`: the line `{ŝ : 2π u·ŝ + ψ = 0}` of the image plane. -/
def npc (u : Plane) (ψ : ℝ) : Set Plane := {s | 2 * Real.pi * ⟪u, s⟫ + ψ = 0}

/-- Eq. (8): the signed perpendicular offset `δs = ψ / (2π |u|)` of the NPC with phase offset `ψ`
from the phase centre. -/
def perpOffset (u : Plane) (ψ : ℝ) : ℝ := ψ / (2 * Real.pi * ‖u‖)

/-- Eqs. (10)-(11) and (14): the closure phase of an `n`-polygon, the sum of the phase offsets
`ψ_{a⌈a+1⌋_n}` of its `n` fringes. -/
def closurePhase {n : ℕ} (ψ : Fin n → ℝ) : ℝ := ∑ a, ψ a

/-- Eqs. (15)-(16): the phase offset `ψ' = ψ + 2π u·ŝ₀` of the NPC `2π u·ŝ + ψ = 0` measured
from the phase centre `ŝ₀`, i.e. its phase in the coordinates `ŝ' = ŝ - ŝ₀`. -/
def recentredPhase (u : Plane) (ψ : ℝ) (s₀ : Plane) : ℝ := ψ + 2 * Real.pi * ⟪u, s₀⟫

/-- Eq. (5): phase offsets of the sides of an `n`-polygon after the element-based phase
corruption `ξ_a = arg G_a`: `ψ̃_{a⌈a+1⌋} = ψ_{a⌈a+1⌋} + ξ_{⌈a+1⌋} - ξ_a` (real phases, as
written in eq. (5)). -/
def elementCorrupt {n : ℕ} [NeZero n] (ξ ψ : Fin n → ℝ) : Fin n → ℝ :=
  fun a => ψ a + ξ (a + 1) - ξ a

/-- The phase offsets of the closed loop `v 0 → v 1 → ⋯ → v (n-1) → v 0` of array elements, read
off from phase offsets `ψ i j` given for every ordered pair of elements (Appendix 2). -/
def loopPhase {N n : ℕ} [NeZero n] (ψ : Fin N → Fin N → ℝ) (v : Fin n → Fin N) : Fin n → ℝ :=
  fun a => ψ (v a) (v (a + 1))

/-- Appendix 2, Fig. 10: the `q`-th elemental triad (`q = 1, …, N-2` in the paper, here
`q = 0, …, M-1` with `N = M + 2`) of the fan decomposition of an `N`-polygon with common vertex
`0`: the elements `0, q+1, q+2` in this cyclic order. -/
def fanTriad {M : ℕ} (q : Fin M) : Fin 3 → Fin (M + 2) := ![0, q.castSucc.succ, q.succ.succ]

/-- Section 3: the NPC pattern of the `n`-polygon with element positions `x` and phase offsets
`ψ'` is the translate by `t` of the pattern with phase offsets `ψ`: every NPC of `ψ'` is the
translate by `t` of the corresponding NPC of `ψ`. -/
def npcTranslate {n : ℕ} [NeZero n] (x : Fin n → Plane) (ψ ψ' : Fin n → ℝ) (t : Plane) : Prop :=
  ∀ a, npc (spacing x a) (ψ' a) = (fun s => s + t) '' npc (spacing x a) (ψ a)

/-- Section 3, eq. (13): the vertices of the polygon enclosed by the NPCs of the sides of an
`n`-polygon: the points lying on the NPCs of two consecutive sides. For `n = 3` these are the
three vertices of the (principal, when the `ψ` are principal phases) triangle. -/
def npcVertices {n : ℕ} [NeZero n] (x : Fin n → Plane) (ψ : Fin n → ℝ) : Set Plane :=
  {s | ∃ a : Fin n, s ∈ npc (spacing x a) (ψ a) ∧ s ∈ npc (spacing x (a + 1)) (ψ (a + 1))}

/-- Eq. (19): `A_{I n}`, the (dimensionless, direction-cosine) area enclosed by the NPCs in the
image plane, as the Lebesgue area of the convex hull of the NPC vertices. -/
def imageArea {n : ℕ} [NeZero n] (x : Fin n → Plane) (ψ : Fin n → ℝ) : ℝ :=
  (volume (convexHull ℝ (npcVertices x ψ))).toReal

/-- Eq. (19) and eq. (28): `A_{A n}`, the area (in wavelengths squared) enclosed by the element
positions in the aperture plane, as the Lebesgue area of their convex hull (the triangle for
`n = 3`; the polygon itself for a convex polygon). -/
def apertureArea {n : ℕ} (x : Fin n → Plane) : ℝ :=
  (volume (convexHull ℝ (Set.range x))).toReal

/-- The element positions `x 0, …, x (n-1)` form a strictly convex polygon in this cyclic order:
every other element lies strictly on one fixed side of each side's line. -/
def IsConvexPolygon {n : ℕ} [NeZero n] (x : Fin n → Plane) : Prop :=
  (∀ a b : Fin n, b ≠ a → b ≠ a + 1 → 0 < cross (x (a + 1) - x a) (x b - x a)) ∨
    (∀ a b : Fin n, b ≠ a → b ≠ a + 1 → cross (x (a + 1) - x a) (x b - x a) < 0)

/-- Eq. (6): the fringe `F_ab(ŝ) = |V_ab| e^{i(2π u_ab·ŝ + arg V_ab)} = V_ab e^{i 2π u_ab·ŝ}` of a
baseline with spacing `u` and (possibly corrupted) visibility `V`. -/
def fringe (u : Plane) (V : ℂ) (s : Plane) : ℂ :=
  V * Complex.exp (2 * Real.pi * Complex.I * (⟪u, s⟫ : ℂ))

/-- Eqs. (3)-(4): the corrupted visibility `Ṽ_ab = G_a^* G_b V_ab` for element gains `G`. -/
def corruptVis {N : ℕ} (G : Fin N → ℂ) (V : Fin N → Fin N → ℂ) (a b : Fin N) : ℂ :=
  (starRingEnd ℂ) (G a) * G b * V a b

/-- Section 3 and Section 4.1: the three-fringe interference image of the closed triad of
elements `v 0, v 1, v 2` (positions `x`, visibilities `V`): the sum of the fringes of the three
sides and of their conjugate baselines (`F_ba = F_ab^*`), i.e. `∑_a 2 Re F_{a⌈a+1⌋}(ŝ)` — the
dirty image of the three visibilities. -/
def triadImage {N : ℕ} (x : Fin N → Plane) (V : Fin N → Fin N → ℂ) (v : Fin 3 → Fin N)
    (s : Plane) : ℝ :=
  ∑ a : Fin 3, 2 * (fringe (x (v (a + 1)) - x (v a)) (V (v a) (v (a + 1))) s).re

end Arxiv2012_05254


