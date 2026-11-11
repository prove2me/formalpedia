-- Prove2me | Definitions.Def_FrechetNearLinear_Main_FreeSpace
-- name    : FrechetNearLinear_Main_FreeSpace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:35:59.631889+00:00
-- url     : https://prove2.me/theorems/9437756d-733a-46cc-be24-084440de3726
-- title:
--   Free space, bi-monotone paths, rectangles, boundary orders, boundary information, certified propagation, summaries, Lift and boundary maps (§2, §4)
-- statement:
--   Fix curves $P,Q$ with $n,m$ vertices. The **free-space diagram** is $[0,n-1]\times[0,m-1]$, and for $r\in\mathbb R$ the **free space** is $F_r=\{(x,y):\|P(x)-Q(y)\|\le r\}$. A path from $s$ to $t$ is a continuous map $[0,1]\to\mathbb R^2$ from $s$ to $t$; it is **bi-monotone** if both coordinates are nondecreasing. On $\mathbb R^2$, $s\le t$ is the coordinatewise order.
--
--   A **rectangle** $R=[x_0,x_1]\times[y_0,y_1]\subseteq[0,n-1]\times[0,m-1]$ has input boundary $\mathrm{In}(R)$ (left and bottom sides) and output boundary $\mathrm{Out}(R)$ (top and right sides). The **boundary order** $\preceq$ on $\mathrm{In}(R)$ starts at the top-left corner, runs down the left side and then right along the bottom side; on $\mathrm{Out}(R)$ it starts at the top-left corner, runs right along the top side and then down the right side (`inPos`, `outPos` give the position along these arcs). $sR_rt$ means that a bi-monotone path from $s$ to $t$ lies in $R\cap F_r$, and $R_r$ is the set of such pairs in $\mathrm{In}(R)\times\mathrm{Out}(R)$.
--
--   **Definition 2.2.** $B\subseteq\mathrm{In}(R)\times\mathrm{Out}(R)$ is $(r,C)$-**boundary information** of $R$ if $R_r\subseteq B\subseteq R_{Cr}$.
--
--   **Definition 2.1.** For labels in a linear order with unavailable value $+\infty$ (min) or $-\infty$ (max), $\lambda'$ on $\mathrm{Out}(R)$ is an $(r,C)$-**certified min-propagation** of $\lambda$ on $\mathrm{In}(R)$ if for every $t\in\mathrm{Out}(R)$: $\lambda'(t)\le\lambda(s)$ whenever $s\in\mathrm{In}(R)$ and $sR_rt$; and if $\lambda'(t)$ is finite, some $s\in\mathrm{In}(R)$ has $\lambda(s)=\lambda'(t)$ and $sR_{Cr}t$. Max-propagation reverses the inequality. Propagation **through a relation** $T$ takes at each exit $t$ the minimum (maximum) of $\lambda(s)$ over $(s,t)\in T$, and $+\infty$ ($-\infty$) when there is no such pair.
--
--   **Boundary edges.** The original vertices cut each side into **boundary edges**: on a side $[a,b]$, the edge of index $j\in\mathbb Z$ is $[\max(a,j),\min(b,j+1)]$, for every $j$ with $a<j+1$ and $j<b$ (a single edge $\lfloor a\rfloor$ if $a=b$). Input edges are $(\mathsf{left},j)$, $(\mathsf{bottom},i)$; output edges $(\mathsf{top},i)$, $(\mathsf{right},j)$. A point shared by two edges belongs to both; the edge is its role. The **free interval** $I_e$ is the free part of edge $e$. The representative port $p_e$ is the first point of $I_e$ in the forward direction (upward on the left and right sides, rightward on the bottom and top sides), and $z_g$ is the last point of $I_g$.
--
--   **Definition 4.2** (on the representative ports). A relation $B$ between input edges $e$ and output edges $g$ ($B(e,g)$ stands for $B(p_e,z_g)$) is an $(r,F)$-**summary** if it relates only edges with nonempty free intervals and $R_r\subseteq B\subseteq R_{Fr}$ on the pairs $(p_e,z_g)$.
--
--   **(4.2)** $\mathrm{Lift}(B)(s,t)$ iff $s\in I_e$, $t\in I_g$, $s\le t$ and $B(p_e,z_g)$ for some $e,g$. $C_{\mathrm{in}}(s,s')$ iff a bi-monotone path from $s$ to $s'$ lies in $\mathrm{In}(R)\cap F_r$, and $C_{\mathrm{out}}$ likewise on $\mathrm{Out}(R)$. **Definition 4.6:** the **boundary map** is
--   $$T_B=C_{\mathrm{out}}\circ\mathrm{Lift}(B)\circ C_{\mathrm{in}}.$$
--   A **decomposition** $(s,s',t',t,e,g)$ of a pair of $T_B$ has $(s,s')\in C_{\mathrm{in}}$, $s'\in I_e$, $t'\in I_g$, $s'\le t'$, $B(p_e,z_g)$ and $(t',t)\in C_{\mathrm{out}}$.
--
--   **Polygonal paths** are given by vertex lists $w$: `polyline w` is the union of the vertices and the segments between consecutive vertices; `IsMonoPolyline w s t` says that $w$ starts at $s$, ends at $t$ and consecutive vertices are coordinatewise nondecreasing; `IsGridPath w` says all vertices are integer points and all steps are $(1,0)$, $(0,1)$ or $(1,1)$. `clampBox s t z` clamps $z$ coordinatewise to $[s_x,t_x]\times[s_y,t_y]$. `inBreaksBetween s s'` counts the edge endpoints of $\mathrm{In}(R)$ (vertices on a side, and the bottom-left corner) strictly between $s$ and $s'$ in $\preceq$; `outBreaksBetween` likewise on $\mathrm{Out}(R)$.
--
--   **Formalization Note** In Definitions 2.2 and 4.2, "a witness can be reported" is read as the existence of the witness, which is exactly $B\subseteq R_{Cr}$ (resp. $R_{Fr}$); the definitions attach no time bound to it. Ports with roles are encoded by the edge they belong to. Since $I_e$ lies on an axis-parallel side, the first (last) point is the coordinatewise infimum (supremum). `inBreaksBetween` is an `ncard` of a finite set.
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 3, §2; p. 4, Definition 2.1; p. 5, Definition 2.2; p. 13, §4 and §4.1; p. 14, Definition 4.2; p. 15, (4.2); p. 16, Definition 4.6

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_Frechet

/-!
# Free space, bi-monotone paths, rectangles, boundary information and boundary maps

Huang, Wang, Zhang, *Constant Approximation of Fréchet Distance in Near-Linear Time*, STOC 2027
submission (manuscript sha256 08be7e65…dd2d): free space, reachability and rectangles p. 3 (§2);
Definition 2.1 p. 4; Definition 2.2 p. 5; boundary edges, roles, ports and the boundary orders
p. 13 (§4, §4.1); Definition 4.2 p. 14; representative ports and `Lift` (4.2) p. 15; `C_in`,
`C_out` p. 15–16; Definition 4.6 and decompositions p. 16.

Points of the free-space diagram `[0, n-1] × [0, m-1]` are pairs `(x, y) : ℝ × ℝ`; `≤` on
`ℝ × ℝ` is the coordinatewise order. A path from `s` to `t` is a Mathlib `Path s t`
(continuous on `[0,1]`); it is bi-monotone when both coordinates are nondecreasing.
-/

namespace FrechetNearLinear.Main

section FreeSpace

variable {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d)

/-- The free space `F_r = {(x, y) : ‖P(x) - Q(y)‖ ≤ r}`. -/
def freeSpace (r : ℝ) : Set (ℝ × ℝ) :=
  {z | ‖curvePt P z.1 - curvePt Q z.2‖ ≤ r}

/-- A path is bi-monotone: both coordinates are nondecreasing. -/
def BiMono {s t : ℝ × ℝ} (γ : Path s t) : Prop :=
  Monotone (fun u => (γ u).1) ∧ Monotone (fun u => (γ u).2)

/-- Some bi-monotone path from `s` to `t` lies inside the set `S`. -/
def PathIn (S : Set (ℝ × ℝ)) (s t : ℝ × ℝ) : Prop :=
  ∃ γ : Path s t, BiMono γ ∧ ∀ u, γ u ∈ S

end FreeSpace

/-- A rectangle `R = [x₀, x₁] × [y₀, y₁]` of the free-space diagram `[0, n-1] × [0, m-1]`
(sides at arbitrary real positions, possibly degenerate). -/
structure Rect (n m : ℕ) where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  hx0 : 0 ≤ x0
  hx : x0 ≤ x1
  hx1 : x1 ≤ (n : ℝ) - 1
  hy0 : 0 ≤ y0
  hy : y0 ≤ y1
  hy1 : y1 ≤ (m : ℝ) - 1

namespace Rect

variable {n m : ℕ} (R : Rect n m)

/-- The point set of `R`. -/
def carrier : Set (ℝ × ℝ) := Set.Icc R.x0 R.x1 ×ˢ Set.Icc R.y0 R.y1

/-- The input boundary `In(R)`: the union of the left and bottom sides. -/
def inB : Set (ℝ × ℝ) := {z | z ∈ R.carrier ∧ (z.1 = R.x0 ∨ z.2 = R.y0)}

/-- The output boundary `Out(R)`: the union of the top and right sides. -/
def outB : Set (ℝ × ℝ) := {z | z ∈ R.carrier ∧ (z.2 = R.y1 ∨ z.1 = R.x1)}

/-- Position of an input point in the boundary order `⪯`, which starts at the top-left corner,
runs down the left side and continues rightward along the bottom side. -/
noncomputable def inPos (z : ℝ × ℝ) : ℝ :=
  if z.1 = R.x0 then R.y1 - z.2 else (R.y1 - R.y0) + (z.1 - R.x0)

/-- Position of an output point in the boundary order `⪯`, which starts at the top-left corner,
runs rightward along the top side and continues down the right side. -/
noncomputable def outPos (z : ℝ × ℝ) : ℝ :=
  if z.2 = R.y1 then z.1 - R.x0 else (R.x1 - R.x0) + (R.y1 - z.2)

end Rect

section Boundary

variable {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m)

/-- `s R_r t`: some bi-monotone path from `s` to `t` lies in `R ∩ F_r`. -/
def ReachIn (r : ℝ) (s t : ℝ × ℝ) : Prop :=
  PathIn (R.carrier ∩ freeSpace P Q r) s t

/-- The relation `R_r ⊆ In(R) × Out(R)`: pairs `(s, t)` with `s ∈ In(R)`, `t ∈ Out(R)` and
`s R_r t`. -/
def Rrel (r : ℝ) (s t : ℝ × ℝ) : Prop :=
  s ∈ R.inB ∧ t ∈ R.outB ∧ ReachIn P Q R r s t

/-- Definition 2.2: a relation `B ⊆ In(R) × Out(R)` is `(r, C)`-boundary information of `R` if
`R_r ⊆ B ⊆ R_{Cr}`. (The witness of a pair of `B`, a bi-monotone path in `R ∩ F_{Cr}`, exists by
`B ⊆ R_{Cr}`; Definition 2.2 attaches no time bound to reporting it.) The theorems using it carry
the hypotheses `0 ≤ r`, `1 ≤ C` of Definition 2.2. -/
def IsBoundaryInfo (r C : ℝ) (B : ℝ × ℝ → ℝ × ℝ → Prop) : Prop :=
  (∀ s t, B s t → s ∈ R.inB ∧ t ∈ R.outB) ∧
  (∀ s t, Rrel P Q R r s t → B s t) ∧
  (∀ s t, B s t → Rrel P Q R (C * r) s t)

/-- Definition 2.1 (min version): `λ'` on `Out(R)` is an `(r, C)`-certified min-propagation of
`λ` on `In(R)`. Labels lie in a linear order `L`; `⊤` is the unavailable value `+∞`. -/
def IsCertifiedMinProp {L : Type*} [LinearOrder L] (r C : ℝ)
    (lam lam' : ℝ × ℝ → WithTop L) : Prop :=
  ∀ t ∈ R.outB,
    (∀ s ∈ R.inB, ReachIn P Q R r s t → lam' t ≤ lam s) ∧
    (lam' t ≠ ⊤ → ∃ s ∈ R.inB, lam s = lam' t ∧ ReachIn P Q R (C * r) s t)

/-- Definition 2.1 (max version), with unavailable value `⊥ = -∞`. -/
def IsCertifiedMaxProp {L : Type*} [LinearOrder L] (r C : ℝ)
    (lam lam' : ℝ × ℝ → WithBot L) : Prop :=
  ∀ t ∈ R.outB,
    (∀ s ∈ R.inB, ReachIn P Q R r s t → lam s ≤ lam' t) ∧
    (lam' t ≠ ⊥ → ∃ s ∈ R.inB, lam s = lam' t ∧ ReachIn P Q R (C * r) s t)

/-- Min-propagation of `λ` through a relation `T` (Definition 4.6): at every exit `t`, `λ'(t)` is
the minimum of `λ(s)` over the pairs `(s, t) ∈ T`, and `+∞` when there is no such pair. -/
def IsMinPropThrough {L : Type*} [LinearOrder L] (T : ℝ × ℝ → ℝ × ℝ → Prop)
    (lam lam' : ℝ × ℝ → WithTop L) : Prop :=
  ∀ t ∈ R.outB,
    (∀ s, T s t → lam' t ≤ lam s) ∧
    ((∃ s, T s t ∧ lam s = lam' t) ∨ ((¬ ∃ s, T s t) ∧ lam' t = ⊤))

/-- Max-propagation of `λ` through `T`: the maximum, and `-∞` when there is no pair. -/
def IsMaxPropThrough {L : Type*} [LinearOrder L] (T : ℝ × ℝ → ℝ × ℝ → Prop)
    (lam lam' : ℝ × ℝ → WithBot L) : Prop :=
  ∀ t ∈ R.outB,
    (∀ s, T s t → lam s ≤ lam' t) ∧
    ((∃ s, T s t ∧ lam s = lam' t) ∨ ((¬ ∃ s, T s t) ∧ lam' t = ⊥))

end Boundary

/-! ### Boundary edges, free intervals, representative ports -/

/-- The integer indices `j` of the original edges `[j, j+1]` that cut the side `[a, b]` into
boundary edges: those overlapping `[a, b]` in positive length when `a < b`; the single edge
`⌊a⌋` when the side is a point. -/
def sideEdges (a b : ℝ) : Set ℤ :=
  if a < b then {j | a < (j : ℝ) + 1 ∧ (j : ℝ) < b} else {⌊a⌋}

/-- The boundary edge of index `j` on the side `[a, b]`: `[max a j, min b (j + 1)]`. -/
def edgePiece (a b : ℝ) (j : ℤ) : Set ℝ :=
  Set.Icc (max a (j : ℝ)) (min b ((j : ℝ) + 1))

namespace Rect

variable {n m : ℕ} (R : Rect n m)

/-- Input boundary edges: `(true, j)` is the `j`-th edge of the left side, `(false, i)` the
`i`-th edge of the bottom side. A shared point (a corner, a vertex on a side) belongs to each
incident edge, which is its role. -/
def inEdges : Set (Bool × ℤ) :=
  {e | (e.1 = true ∧ e.2 ∈ sideEdges R.y0 R.y1) ∨ (e.1 = false ∧ e.2 ∈ sideEdges R.x0 R.x1)}

/-- Output boundary edges: `(true, i)` is the `i`-th edge of the top side, `(false, j)` the
`j`-th edge of the right side. -/
def outEdges : Set (Bool × ℤ) :=
  {g | (g.1 = true ∧ g.2 ∈ sideEdges R.x0 R.x1) ∨ (g.1 = false ∧ g.2 ∈ sideEdges R.y0 R.y1)}

/-- The point set of an input boundary edge. -/
def inEdgeSet (e : Bool × ℤ) : Set (ℝ × ℝ) :=
  if e.1 then {R.x0} ×ˢ edgePiece R.y0 R.y1 e.2 else edgePiece R.x0 R.x1 e.2 ×ˢ {R.y0}

/-- The point set of an output boundary edge. -/
def outEdgeSet (g : Bool × ℤ) : Set (ℝ × ℝ) :=
  if g.1 then edgePiece R.x0 R.x1 g.2 ×ˢ {R.y1} else {R.x1} ×ˢ edgePiece R.y0 R.y1 g.2

/-- A point of the input boundary at which a boundary edge ends: a vertex of the left side
(integer `y`), a vertex of the bottom side (integer `x`), or the bottom-left corner. -/
def IsInBreak (z : ℝ × ℝ) : Prop :=
  z ∈ R.inB ∧ ((z.1 = R.x0 ∧ ∃ j : ℤ, z.2 = j) ∨ (z.2 = R.y0 ∧ ∃ i : ℤ, z.1 = i) ∨
    z = (R.x0, R.y0))

/-- A point of the output boundary at which a boundary edge ends (vertex of the top or right
side, or the top-right corner). -/
def IsOutBreak (z : ℝ × ℝ) : Prop :=
  z ∈ R.outB ∧ ((z.2 = R.y1 ∧ ∃ i : ℤ, z.1 = i) ∨ (z.1 = R.x1 ∧ ∃ j : ℤ, z.2 = j) ∨
    z = (R.x1, R.y1))

/-- The number of edge endpoints of the input boundary strictly between `s` and `s'`; the number
of boundary edges between them is at most this plus one. -/
noncomputable def inBreaksBetween (s s' : ℝ × ℝ) : ℕ :=
  Set.ncard {z | R.IsInBreak z ∧ min (R.inPos s) (R.inPos s') < R.inPos z ∧
    R.inPos z < max (R.inPos s) (R.inPos s')}

/-- The number of edge endpoints of the output boundary strictly between `t'` and `t`. -/
noncomputable def outBreaksBetween (t' t : ℝ × ℝ) : ℕ :=
  Set.ncard {z | R.IsOutBreak z ∧ min (R.outPos t') (R.outPos t) < R.outPos z ∧
    R.outPos z < max (R.outPos t') (R.outPos t)}

end Rect

section Ports

variable {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) (R : Rect n m)

/-- The free interval `I_e` of an input boundary edge `e` at radius `r`. -/
def freeIn (r : ℝ) (e : Bool × ℤ) : Set (ℝ × ℝ) := R.inEdgeSet e ∩ freeSpace P Q r

/-- The free interval `I_g` of an output boundary edge `g` at radius `r`. -/
def freeOut (r : ℝ) (g : Bool × ℤ) : Set (ℝ × ℝ) := R.outEdgeSet g ∩ freeSpace P Q r

/-- The representative input port `p_e`: the first point of `I_e` in the forward direction
(upward on the left side, rightward on the bottom side). As `I_e` lies on an axis-parallel side,
it is the coordinatewise infimum. -/
noncomputable def repIn (r : ℝ) (e : Bool × ℤ) : ℝ × ℝ :=
  (sInf (Prod.fst '' freeIn P Q R r e), sInf (Prod.snd '' freeIn P Q R r e))

/-- The representative output port `z_g`: the last point of `I_g` in the forward direction. -/
noncomputable def repOut (r : ℝ) (g : Bool × ℤ) : ℝ × ℝ :=
  (sSup (Prod.fst '' freeOut P Q R r g), sSup (Prod.snd '' freeOut P Q R r g))

/-- Definition 4.2 on the representative ports: a relation `B` between input and output edges
(`B e g` stands for `B(p_e, z_g)`; the edge is the port's role) is an `(r, F)`-summary when it
only relates edges with nonempty free intervals and
`R_r ∩ (S_in × S_out) ⊆ B ⊆ R_{Fr} ∩ (S_in × S_out)` for the representative ports. -/
def IsRepSummary (r F : ℝ) (B : Bool × ℤ → Bool × ℤ → Prop) : Prop :=
  ∀ e g,
    (B e g → e ∈ R.inEdges ∧ g ∈ R.outEdges ∧ (freeIn P Q R r e).Nonempty ∧
      (freeOut P Q R r g).Nonempty) ∧
    (e ∈ R.inEdges → g ∈ R.outEdges → (freeIn P Q R r e).Nonempty →
      (freeOut P Q R r g).Nonempty →
      (ReachIn P Q R r (repIn P Q R r e) (repOut P Q R r g) → B e g) ∧
      (B e g → ReachIn P Q R (F * r) (repIn P Q R r e) (repOut P Q R r g)))

/-- (4.2): `Lift(B)(s, t)` iff `s ∈ I_e`, `t ∈ I_g`, `s ≤ t` and `B(p_e, z_g)` for some input
edge `e` and output edge `g`. -/
def Lift (r : ℝ) (B : Bool × ℤ → Bool × ℤ → Prop) (s t : ℝ × ℝ) : Prop :=
  ∃ e g, e ∈ R.inEdges ∧ g ∈ R.outEdges ∧ s ∈ freeIn P Q R r e ∧ t ∈ freeOut P Q R r g ∧
    s ≤ t ∧ B e g

/-- `C_in`: some bi-monotone path from `s` to `s'` lies in `In(R) ∩ F_r`. -/
def Cin (r : ℝ) (s s' : ℝ × ℝ) : Prop := PathIn (R.inB ∩ freeSpace P Q r) s s'

/-- `C_out`: some bi-monotone path from `t'` to `t` lies in `Out(R) ∩ F_r`. -/
def Cout (r : ℝ) (t' t : ℝ × ℝ) : Prop := PathIn (R.outB ∩ freeSpace P Q r) t' t

/-- Definition 4.6: the boundary map `T_B = C_out ∘ Lift(B) ∘ C_in`. -/
def boundaryMap (r : ℝ) (B : Bool × ℤ → Bool × ℤ → Prop) (s t : ℝ × ℝ) : Prop :=
  ∃ s' t', Cin P Q R r s s' ∧ Lift P Q R r B s' t' ∧ Cout P Q R r t' t

/-- A decomposition `(s, s', t', t, e, g)` of a pair of `T_B` (p. 16): `(s, s') ∈ C_in`,
`s' ∈ I_e`, `t' ∈ I_g`, `s' ≤ t'`, `B(p_e, z_g)`, `(t', t) ∈ C_out`. -/
def IsDecomposition (r : ℝ) (B : Bool × ℤ → Bool × ℤ → Prop) (s s' t' t : ℝ × ℝ)
    (e g : Bool × ℤ) : Prop :=
  Cin P Q R r s s' ∧ e ∈ R.inEdges ∧ g ∈ R.outEdges ∧ s' ∈ freeIn P Q R r e ∧
    t' ∈ freeOut P Q R r g ∧ s' ≤ t' ∧ B e g ∧ Cout P Q R r t' t

end Ports

/-! ### Polygonal paths given by vertex lists -/

/-- The point set of the polygonal path through the vertex list `w`: its vertices and the
segments between consecutive vertices. -/
def polyline (w : List (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z | ∃ k, ∃ h : k < w.length, z = w[k]} ∪
    {z | ∃ k, ∃ h : k + 1 < w.length, z ∈ segment ℝ w[k] w[k + 1]}

/-- A bi-monotone polygonal path from `s` to `t`: a nonempty vertex list starting at `s`,
ending at `t`, with consecutive vertices coordinatewise nondecreasing. -/
def IsMonoPolyline (w : List (ℝ × ℝ)) (s t : ℝ × ℝ) : Prop :=
  w.head? = some s ∧ w.getLast? = some t ∧ w.IsChain (fun a b => a ≤ b)

/-- A grid path: every vertex is an integer point and every step is `(1,0)`, `(0,1)` or
`(1,1)`. -/
def IsGridPath (w : List (ℝ × ℝ)) : Prop :=
  (∀ z ∈ w, ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ))) ∧
    w.IsChain (fun a b => b - a = (1, 0) ∨ b - a = (0, 1) ∨ b - a = (1, 1))

/-- Coordinatewise clamping of `z` to the box `[s.1, t.1] × [s.2, t.2]`. -/
def clampBox (s t z : ℝ × ℝ) : ℝ × ℝ :=
  (max s.1 (min t.1 z.1), max s.2 (min t.2 z.2))

end FrechetNearLinear.Main


