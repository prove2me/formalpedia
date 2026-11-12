-- Prove2me | Definitions.Def_EuclidCVRP_Main_Pairing
-- name    : EuclidCVRP_Main_Pairing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:41.750373+00:00
-- url     : https://prove2.me/theorems/c186ae89-e037-44b2-9e66-7482d6e41705
-- title:
--   Pairing graphs, compact orderings, smooth flows and close flows (Definitions 22, 24, 29)
-- statement:
--   Let a dissection square have $m$ portals, numbered $0,\dots,m-1$ clockwise. An edge of the complete directed graph $H[S]$ on the portals is an ordered pair $(a,b)$, loops included.
--
--   1. **Crossing** (p. 25). Two edges do not cross if one is a loop or they share an endpoint; otherwise $(a,b)$ and $(c,d)$ cross iff exactly one of $c,d$ lies strictly between $\min(a,b)$ and $\max(a,b)$. A **pairing graph** is a set of pairwise non-crossing edges.
--   2. **Distance** (p. 26): $d(e,e')=|a-c|+|b-d|$ for $e=(a,b)$, $e'=(c,d)$.
--   3. **Definition 22.** An ordering $e_1,\dots,e_k$ of the edge set $E$ of a pairing graph is **compact** if
--   $$\sum_{i=1}^{k-1}\log_2\bigl(2\,d(e_i,e_{i+1})\bigr)\le 24m.$$
--   4. A **valid pairing flow** (p. 27) is an integer flow $f$ on $H[S]$ whose support is a pairing graph $E$ and with $f_e\le 2n$ on every edge ($n$ the number of non-terminals).
--   5. **Definition 24.** With $d_i=d(e_i,e_{i+1})$ and $f_i=f_{e_i}$, the flow $f$ is **smooth** with respect to the ordering if for $i=1,\dots,k-1$: (i) $f_{i+1}\ge(\varepsilon/d_i)f_i$; (ii) $f_i\ge(\varepsilon/d_i)f_{i+1}$; (iii) $f_{i+1}=\lfloor(1+\varepsilon/d_i)^j\rfloor$ for some integer $j$.
--   6. A square with side $s$ and $m'$ segments per side has $m=4m'$ portals at the segment endpoints, numbered clockwise from an arbitrary portal; consecutive portals are at distance $\tau(S)=s/m'$.
--   7. **Definition 29.** Valid pairing flows $f^*,\tilde f$ with the same support $E$ and the same total value $F=\sum_{e\in E}f^*_e=\sum_{e\in E}\tilde f_e$ are **close** (with constant $C$) if a nonnegative integer **detour flow** $dt$ on the complete directed graph on the copies $p^{\mathrm{in}}[S],p^{\mathrm{out}}[S]$ of the portals satisfies, for every portal $p$,
--   $$\tilde f^{\mathrm{in}}(p)=f^{*\mathrm{in}}(p)+dt^{\mathrm{in}}(p^{\mathrm{in}})-dt^{\mathrm{out}}(p^{\mathrm{in}}),\qquad \tilde f^{\mathrm{out}}(p)=f^{*\mathrm{out}}(p)+dt^{\mathrm{out}}(p^{\mathrm{out}})-dt^{\mathrm{in}}(p^{\mathrm{out}}),$$
--   and $c(dt)\le C\,\varepsilon\,F\,\tau(S)$, where $c(dt)$ weights each arc by the Euclidean distance of its portals (zero between the two copies of a portal).
--
--   These are the objects of Lemmas 21, 23, 25 and 30.
--
--   **Formalization Note** The paper numbers the portals $1,\dots,m$; numbering from $0$ changes no definition. The constant of the $O(\varepsilon)$ in Definition 29 is a parameter $C$ of the closeness predicate.
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), §4.1, p. 24 (portals, τ(S)), p. 25 (H[S], crossing, pairing graphs), p. 26 (d(e,e'), Definition 22), p. 27 (valid flows, Definition 24), pp. 28–29 (Definition 29)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Instance

set_option autoImplicit false

namespace EuclidCVRP.Main

/-!
# Pairing graphs, compact orderings, smooth flows and close flows (§4.1)

Blauth, Grandoni, Mátravölgyi, Mousavi, Ren, Salavatipour, STOC 2027 submission #1236 (October 2026),
§4.1: portals of a dissection square (p. 24), pairing graphs and crossing edges (p. 25), the
distance between edges and Definition 22 (p. 26), valid pairing flows and Definition 24 (p. 27),
detour flows and Definition 29 (pp. 28–29).

The `m` portals of a square are numbered `0, …, m−1` in clockwise order (the paper numbers them
`1, …, m`); an edge of `H[S]` is an ordered pair of portal numbers, loops included.
-/

/-- An edge `(a, b)` of the complete directed graph `H[S]` on the portals (loops allowed). -/
abbrev PEdge := ℕ × ℕ

/-- **Crossing edges** (p. 25): two edges are not crossing if one is a loop or they share an endpoint;
otherwise `(a, b)` and `(c, d)` cross iff exactly one of `c`, `d` is visited when going clockwise from
`min(a,b)` to `max(a,b)`. -/
def Crossing (e e' : PEdge) : Prop :=
  e.1 ≠ e.2 ∧ e'.1 ≠ e'.2 ∧ e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2 ∧
    Xor (min e.1 e.2 < e'.1 ∧ e'.1 < max e.1 e.2) (min e.1 e.2 < e'.2 ∧ e'.2 < max e.1 e.2)

/-- **A pairing graph** on `m` portals (p. 25): an edge set of `H[S]` (all endpoints `< m`) whose
edges are pairwise non-crossing. -/
def IsPairingGraph (m : ℕ) (E : Finset PEdge) : Prop :=
  (∀ e ∈ E, e.1 < m ∧ e.2 < m) ∧ ∀ e ∈ E, ∀ e' ∈ E, ¬ Crossing e e'

/-- The distance `d(e, e') = |a − c| + |b − d|` between edges `e = (a,b)` and `e' = (c,d)` (p. 26). -/
def edgeDist (e e' : PEdge) : ℕ :=
  Int.natAbs ((e.1 : ℤ) - e'.1) + Int.natAbs ((e.2 : ℤ) - e'.2)

/-- **A compact ordering** (Definition 22, p. 26) of the edge set `E` of a pairing graph on `m` portals:
an ordering `e₁, …, e_k` of `E` (each edge exactly once) with
`∑_{i=1}^{k−1} log₂ (2 d(eᵢ, eᵢ₊₁)) ≤ 24 m`. -/
def IsCompactOrdering (m : ℕ) (E : Finset PEdge) (l : List PEdge) : Prop :=
  l.Nodup ∧ l.toFinset = E ∧
    ((l.zip l.tail).map (fun p => Real.logb 2 (2 * (edgeDist p.1 p.2 : ℝ)))).sum ≤ 24 * (m : ℝ)

/-- **A valid pairing flow** for a square with `m` portals and an instance with `n` non-terminals
(p. 27): an integer flow `f` on `H[S]` whose support `E(f)` is exactly `E`, where `E` is a pairing
graph (non-crossing), and with `f_e ≤ 2n` on every edge. -/
def IsValidFlow (m n : ℕ) (E : Finset PEdge) (f : PEdge → ℕ) : Prop :=
  IsPairingGraph m E ∧ (∀ e, f e ≠ 0 ↔ e ∈ E) ∧ ∀ e ∈ E, f e ≤ 2 * n

/-- **A smooth flow** with respect to the ordering `l = e₁, …, e_k` (Definition 24, p. 27): with
`dᵢ = d(eᵢ, eᵢ₊₁)` and `fᵢ = f_{eᵢ}`, for `i = 1, …, k−1`: (i) `f_{i+1} ≥ (ε/dᵢ) fᵢ`,
(ii) `fᵢ ≥ (ε/dᵢ) f_{i+1}`, and (iii) `f_{i+1} = ⌊(1 + ε/dᵢ)^j⌋` for some integer `j`. -/
def IsSmooth (ε : ℝ) (l : List PEdge) (f : PEdge → ℕ) : Prop :=
  ∀ p ∈ l.zip l.tail,
    (f p.2 : ℝ) ≥ ε / (edgeDist p.1 p.2 : ℝ) * f p.1 ∧
    (f p.1 : ℝ) ≥ ε / (edgeDist p.1 p.2 : ℝ) * f p.2 ∧
    ∃ j : ℤ, (f p.2 : ℤ) = ⌊(1 + ε / (edgeDist p.1 p.2 : ℝ)) ^ j⌋

/-- The flow into portal `p` in `H[S]`: `f^in(p) = ∑_a f_{(a,p)}`. -/
def flowIn (m : ℕ) (f : PEdge → ℕ) (p : ℕ) : ℕ := ∑ a ∈ Finset.range m, f (a, p)

/-- The flow out of portal `p` in `H[S]`: `f^out(p) = ∑_b f_{(p,b)}`. -/
def flowOut (m : ℕ) (f : PEdge → ℕ) (p : ℕ) : ℕ := ∑ b ∈ Finset.range m, f (p, b)

/-- **A square of the dissection with its portals** (p. 24): an axis-parallel square (lower-left
corner, side length), each side cut into `m'` equal segments, the `4m'` segment endpoints being the
portals, numbered clockwise starting from the portal `start` (an arbitrary portal). -/
structure DSquare where
  /-- lower-left corner -/
  corner : Pt
  /-- side length -/
  side : ℝ
  /-- number of segments per side -/
  m' : ℕ
  /-- position (in the clockwise order from the lower-left corner) of the portal numbered `0` -/
  start : ℕ

namespace DSquare

variable (S : DSquare)

/-- The number `m = 4m'` of portals of the square. -/
def m : ℕ := 4 * S.m'

/-- The distance `τ(S) = side/m'` between consecutive portals. -/
noncomputable def τ : ℝ := S.side / S.m'

/-- The `k`-th segment endpoint in clockwise order from the lower-left corner (up the left side,
right along the top, down the right side, left along the bottom). -/
noncomputable def boundaryPt (k : ℕ) : Pt :=
  let x0 := S.corner.ofLp 0
  let y0 := S.corner.ofLp 1
  let r : ℝ := ((k % S.m' : ℕ) : ℝ) * S.τ
  match k / S.m' with
  | 0 => !₂[x0, y0 + r]
  | 1 => !₂[x0 + r, y0 + S.side]
  | 2 => !₂[x0 + S.side, y0 + S.side - r]
  | _ => !₂[x0 + S.side - r, y0]

/-- The portal numbered `p`. -/
noncomputable def portal (p : ℕ) : Pt := S.boundaryPt ((p + S.start) % S.m)

/-- **A detour flow** (Definition 29) lives on the copies `p^in[S]` (`true`) and `p^out[S]` (`false`) of
the portals: a nonnegative integer flow on the complete directed graph on these copies. -/
abbrev Detour := (Fin S.m × Bool) → (Fin S.m × Bool) → ℕ

/-- The cost `c(dt) = ∑ w_{xy} dt_{xy}`, with `w` the Euclidean distance between the portals of the
copies (zero between the two copies of one portal). -/
noncomputable def detourCost (dt : S.Detour) : ℝ :=
  ∑ x, ∑ y, dist (S.portal x.1) (S.portal y.1) * (dt x y : ℝ)

/-- **`f*` and `f̃` are close** (Definition 29, pp. 28–29), with the constant `C` of its `O(ε)`: both
have support `E` and the same total value `F = ∑_{e∈E} f*_e = ∑_{e∈E} f̃_e`, and some detour flow `dt`
satisfies, for every portal `p`, `f̃^in(p) = f*^in(p) + dt^in(p^in[S]) − dt^out(p^in[S])` and
`f̃^out(p) = f*^out(p) + dt^out(p^out[S]) − dt^in(p^out[S])`, with `c(dt) ≤ C ε F τ(S)`. -/
def IsClose (C ε : ℝ) (E : Finset PEdge) (f f' : PEdge → ℕ) : Prop :=
  (∀ e, f e ≠ 0 ↔ e ∈ E) ∧ (∀ e, f' e ≠ 0 ↔ e ∈ E) ∧
  ∑ e ∈ E, f e = ∑ e ∈ E, f' e ∧
  ∃ dt : S.Detour,
    (∀ p : Fin S.m,
      (flowIn S.m f' p : ℤ) = flowIn S.m f p + (∑ y, dt y (p, true) : ℕ) - (∑ y, dt (p, true) y : ℕ) ∧
      (flowOut S.m f' p : ℤ) = flowOut S.m f p + (∑ y, dt (p, false) y : ℕ) - (∑ y, dt y (p, false) : ℕ)) ∧
    S.detourCost dt ≤ C * ε * (∑ e ∈ E, f e : ℕ) * S.τ

end DSquare

end EuclidCVRP.Main


