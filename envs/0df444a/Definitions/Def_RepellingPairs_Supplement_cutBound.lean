-- Prove2me | Definitions.Def_RepellingPairs_Supplement_cutBound
-- name    : RepellingPairs_Supplement_cutBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:57:50.488773+00:00
-- url     : https://prove2.me/theorems/217afde0-22bc-44bc-a49f-4b59ffa69417
-- title:
--   Boundary points $X$, terminal pairs crossing a boundary cut, repelling numbers $a_{x,y}$ and cut bounds $b_{x,y}$
-- statement:
--   Let $D$ be a metric on terminals $0,\dots,k-1$ placed on the boundary of a disk in this cyclic order. Let $X=\{x_0,\dots,x_{m-1}\}$, $m=2k$, be the boundary points in cyclic order, where $x_{2t}$ is terminal $t$ and $x_{2t+1}$ is a **reference point** in the boundary interval between terminals $t$ and $t+1$ (indices mod $k$).
--
--   1. Two points $x_p,x_q\in X$ divide the boundary into two arcs. A terminal pair $(s,t)$ (the trivial pair $(t,t)$ included) **crosses the $x_p$–$x_q$ cut** if its endpoints lie on opposite arcs, or if an endpoint coincides with $x_p$ or $x_q$. When $p=q$ one arc is empty and only pairs with an endpoint at $x_p$ cross.
--   2. A finite set $M$ of terminal pairs is **repelling** if any two distinct members repel.
--   3. The **repelling number** is
--   $$
--   a_{x,y}=\max\{|M| : M\text{ repelling, every pair of }M\text{ crosses the }x\text{–}y\text{ cut}\}.
--   $$
--   4. The **cut bound** is
--   $$
--   b_{x,y}=\begin{cases}2a_{x,y}-2,& x,y\in T,\\ 2a_{x,y}-1,& |\{x,y\}\cap T|=1,\\ 2a_{x,y},& x,y\notin T.\end{cases}
--   $$
--
--   The numbers $b_{x,y}$ are lower bounds on the number of medial chords crossing a boundary cut in any OS realization of $D$ (inequality (2) of the paper), and the template $\Phi(D)$ of Theorem 32 is the one that meets them with equality.
--
--   **Formalization Note** Points of $X$ are $\mathrm{Fin}(2k)$, and $x_i$ is a terminal iff $i$ is even. Lying on opposite open arcs is expressed with the base mission's `Config.onSide p q` (membership in $\{p+1,\dots,q\}$), which agrees with the open arcs for points other than $x_p,x_q$. Pairs are ordered, but $(s,t)$ never repels $(t,s)$, so no repelling set contains both orientations. The maximum is a supremum over a finite family that contains the empty set, so it is attained. $b$ takes values in $\mathbb Z$.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.6 (PDF p.7): X and boundary cuts; §5.3.2, p.32 (PDF p.33): a_{x,y}, b_{x,y}

import Mathlib
import Definitions.Def_RepellingPairs_Repel
import Definitions.Def_RepellingPairs_Config

set_option autoImplicit false

namespace RepellingPairs

namespace Supplement

open Classical

/-- The boundary point `x_{2t}` of `X` occupied by terminal `t`. With `k` terminals, `X` has `m = 2k`
points `x_0, …, x_{m-1}` in boundary order: `x_{2t}` is terminal `t` and `x_{2t+1}` is the reference point
in the boundary interval between terminals `t` and `t + 1` (mod `k`).
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.6 ("let X contain every
terminal and one additional reference point in each boundary interval between consecutive terminals") and
§5.3.1, p.31.

**Formalization Note.** The paper's `x_1, …, x_m` are `0, …, m - 1`; the parity convention is one choice of
labelling and changes no instance. The point `x_i` is the bar `ī` of `Config.dist` (between the template
points `z_i` and `z_{i+1}`). -/
def terminalPoint {k : ℕ} (t : Fin k) : Fin (2 * k) := ⟨2 * t.val, by omega⟩

/-- `x_i ∈ T`: the point `x_i` of `X` is a terminal, i.e. `i` is even. -/
def IsTerminalPoint {k : ℕ} (i : Fin (2 * k)) : Prop := Even i.val

/-- The terminal pair `(s, t)` crosses the `x_p`-`x_q` boundary cut: "its endpoints lie on opposite arcs, or
an endpoint coincides with x or y" (§2, p.6). For points other than `x_p, x_q`, lying on opposite open arcs is
lying on different sides `Config.onSide p q` (the side `{p+1, …, q}`). For `p = q` one arc is empty and only
pairs with an endpoint at `x_p` cross. Trivial pairs `(t, t)` are terminal pairs. -/
def PairCrossesCut {k : ℕ} (p q : Fin (2 * k)) (st : Fin k × Fin k) : Prop :=
  terminalPoint st.1 = p ∨ terminalPoint st.1 = q ∨ terminalPoint st.2 = p ∨ terminalPoint st.2 = q ∨
    Config.onSide p q (terminalPoint st.1) ≠ Config.onSide p q (terminalPoint st.2)

/-- A repelling set of terminal pairs: "a family of terminal pairs is repelling if its members repel
pairwise" (§2, p.6), trivial pairs `(t, t)` allowed.

**Formalization Note.** Pairs are ordered, but `(s, t)` never repels `(t, s)`, so a repelling set never
holds both orientations of one pair and its size is the paper's. -/
def IsRepellingSet {k : ℕ} (D : Fin k → Fin k → ℝ) (M : Finset (Fin k × Fin k)) : Prop :=
  ∀ P ∈ M, ∀ Q ∈ M, P ≠ Q → Repel D P.1 P.2 Q.1 Q.2

/-- The repelling number `a_{x_p, x_q} = max{|M| : M is a repelling set and every pair in M crosses the
x_p-x_q cut}` (§5.3.2, p.32). The maximum is over a finite nonempty family (the empty set qualifies), so it
is attained, and it is `0` when no pair crosses. -/
noncomputable def repellingNumber {k : ℕ} (D : Fin k → Fin k → ℝ) (p q : Fin (2 * k)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin k × Fin k))).filter
    (fun M => IsRepellingSet D M ∧ ∀ P ∈ M, PairCrossesCut p q P)).sup Finset.card

/-- The cut bound `b_{x,y}` of §5.3.2, p.32: `2a_{x,y} − 2` if `x, y ∈ T`, `2a_{x,y} − 1` if exactly one of
`x, y` is in `T`, and `2a_{x,y}` if neither is. Computed in `ℤ`, so that no truncation occurs. -/
noncomputable def cutBound {k : ℕ} (D : Fin k → Fin k → ℝ) (p q : Fin (2 * k)) : ℤ :=
  2 * (repellingNumber D p q : ℤ) - (if IsTerminalPoint p then 1 else 0) -
    (if IsTerminalPoint q then 1 else 0)

end Supplement

end RepellingPairs


