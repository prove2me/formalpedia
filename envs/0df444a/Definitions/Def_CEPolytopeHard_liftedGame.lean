-- Prove2me | Definitions.Def_CEPolytopeHard_liftedGame
-- name    : CEPolytopeHard_liftedGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:42.375584+00:00
-- url     : https://prove2.me/theorems/f2f5da19-edc9-44ec-8d67-1f05608c9625
-- title:
--   The constructed game: lifted strategies, linear cost and utilities
-- statement:
--   The game of Section 4.1 has $q + 2$ players $x$, $y$ and copies $1, \dots, q$, each with strategy set $S$, the product over the $D$ coordinates of copies of the polytope (13). A strategy is $s = (x, t, w)$ with projection $x(s) = x$ and linear cost $c(s) = D^{-1}\sum_a t_a$. Writing $x = x(s_x)$, $y = x(s_y)$, $z^{(j)} = x(s_j)$ and $\langle u, v\rangle = \sum_a u_a v_a$, the utilities are
--   $$
--   u_x = \frac{2}{D(1 + qM)}\Big\langle x,\ y + M\sum_j z^{(j)}\Big\rangle - c(s_x), \qquad u_y = \frac2D\big\langle y, \tilde g(z^{(1)}, \dots, z^{(q)})\big\rangle - c(s_y), \qquad u_j = \frac2D\langle z^{(j)}, x\rangle - c(s_j),
--   $$
--   with a weight $M \ge 1$ per copy. Player $x$ imitates $y$ and the copies, $y$ imitates the map evaluated at the copies, and each copy imitates $x$.
--
--   **Formalization Note** The coordinates form a finite set of $D$ elements ($D = dr$ in the paper), and $\tilde g$ is a parameter (the construction's copy map in the paper). Players are encoded as `none` ($x$), `some none` ($y$) and `some (some j)` (copy $j$). The utilities are the unscaled ones of p.23 (values in $[-1, 2]$), as Claim 4.4 uses them.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), "The final construction", pp.22–23

import Mathlib
import Definitions.Def_CEPolytopeHard_pm

set_option autoImplicit false

namespace CEPolytopeHard

/-- the players of the constructed game: `none` is player `x`, `some none` is player `y`, and
`some (some j)` is copy player `j` -/
abbrev Role (q : ℕ) : Type := Option (Option (Fin q))

/-- a lifted strategy `s = (x, t, w)`: for each coordinate `a`, the triple `(x_a, t_a, w_a)` -/
abbrev LStrat (ι : Type) (m : ℕ) : Type := ι → ℝ × ℝ × (Fin (m + 1) → ℝ)

/-- the strategy set `S`, the product of copies of the polytope (13), one per coordinate -/
def LStratSet (ι : Type) (m : ℕ) : Set (LStrat ι m) :=
  {s | ∀ a, InPoly13 m (s a).1 (s a).2.1 (s a).2.2}

/-- the projection `x(s)` onto the original coordinates -/
def projX {ι : Type} {m : ℕ} (s : LStrat ι m) : ι → ℝ := fun a => (s a).1

/-- the linear cost `c(s) = D^{−1} ∑_a t_a` -/
noncomputable def lcost {ι : Type} [Fintype ι] {m : ℕ} (s : LStrat ι m) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ a, (s a).2.1

/-- the unnormalized inner product `⟨u, v⟩ = ∑_a u_a v_a` (p.10) -/
def ip {ι : Type} [Fintype ι] (u v : ι → ℝ) : ℝ := ∑ a, u a * v a

/-- The **utilities of the constructed game** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, "The final construction", pp.22–23: "The game
contains q + 2 players, each of whom has strategy set S. … u_x = (2/(dr(1 + qM)))⟨x, y + M∑_j z^{(j)}⟩ − c(s_x),
u_y = (2/(dr))⟨y, g̃(z^{(1)}, . . . , z^{(q)})⟩ − c(s_y), u_j = (2/(dr))⟨z^{(j)}, x⟩ − c(s_j) for j ∈ [q]"),
with `x = x(s_x)`, `y = x(s_y)`, `z^{(j)} = x(s_j)`, weight `M` and a map `g̃` of the copies.

**Formalization Note** The coordinates form a finite type `ι` with `D = card ι` in place of `dr`,
and `g̃` is a parameter (the construction's copy map is `gtilde`). The utilities are the unscaled
ones of p.23 (values in `[−1, 2]`), as in Claim 4.4. -/
noncomputable def gameUtility {ι : Type} [Fintype ι] (m q : ℕ) (M : ℝ)
    (gt : (Fin q → ι → ℝ) → ι → ℝ) : Role q → (Role q → LStrat ι m) → ℝ
  | none => fun s =>
      2 / ((Fintype.card ι : ℝ) * (1 + q * M)) *
        ip (projX (s none)) (projX (s (some none)) + M • ∑ j, projX (s (some (some j)))) -
      lcost (s none)
  | some none => fun s =>
      2 / (Fintype.card ι : ℝ) * ip (projX (s (some none))) (gt fun j => projX (s (some (some j)))) -
      lcost (s (some none))
  | some (some j) => fun s =>
      2 / (Fintype.card ι : ℝ) * ip (projX (s (some (some j)))) (projX (s none)) -
      lcost (s (some (some j)))

end CEPolytopeHard


