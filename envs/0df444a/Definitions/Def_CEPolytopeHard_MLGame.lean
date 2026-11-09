-- Prove2me | Definitions.Def_CEPolytopeHard_MLGame
-- name    : CEPolytopeHard_MLGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:23.192695+00:00
-- url     : https://prove2.me/theorems/87ece332-44b9-4d8e-80db-3da7cdef6822
-- title:
--   Multilinear polytope game (explicit representation)
-- statement:
--   A **multilinear polytope game** is given explicitly by its list of players $1, \dots, n$. Player $i$ has
--
--   1. a dimension $d_i$ and strategy space $\mathbb R^{d_i}$;
--   2. a finite list of rational inequalities $(a, b)$, $a \in \mathbb Q^{d_i}$, $b \in \mathbb Q$, each meaning $\sum_c a_c x_c \le b$; their solution set is the strategy polytope $X_i = \{x_i \in \mathbb R^{d_i} : A_i x_i \le b_i\}$;
--   3. a finite list of monomials $(\kappa, V)$ with rational coefficient $\kappa$ and a list $V$ of variables $(j, c)$ (coordinate $c$ of player $j$); the utility is
--   $$
--   u_i(x) = \sum_{(\kappa, V)} \kappa \prod_{(j,c) \in V} x_{j,c}.
--   $$
--
--   A profile is $x = (x_1, \dots, x_n)$ with $x_i \in \mathbb R^{d_i}$. The representation is **well formed** when every inequality of player $i$ has exactly $d_i$ coefficients, every variable index is in range, and the players occurring in one monomial are pairwise distinct, so that "every monomial contains at most one coordinate of each player's strategy (raised to the first power)": each utility is affine in each player's own strategy.
--
--   **Formalization Note** Indices are 0-based. An out-of-range variable evaluates to $0$; well-formedness excludes it.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.3, p.11 (multilinear polytope games)

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- The data of one player of a **multilinear polytope game** (Anagnostides–Daskalakis–Farina–
Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*,
arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 2.3, p.11):
the dimension `dim` of the player's strategy space `ℝ^dim`, the explicit list of rational linear
inequalities `rows` (a row `(a, b)` means `∑_c a_c x_c ≤ b`) describing the strategy polytope,
and the explicit list of rational monomials `monos` of the player's utility (a monomial
`(coef, vars)` is `coef · ∏_{(j, c) ∈ vars} x_{j,c}`, where `x_{j,c}` is coordinate `c` of player
`j`'s strategy). Indices are 0-based. -/
structure MLPlayer where
  /-- dimension `d_i` of the strategy space -/
  dim : ℕ
  /-- inequality rows `(a, b)`: `∑_c a_c x_c ≤ b` -/
  rows : List (List ℚ × ℚ)
  /-- utility monomials `(coef, [(player, coordinate), …])` -/
  monos : List (ℚ × List (ℕ × ℕ))

/-- A **multilinear polytope game** in its explicit representation (Section 2.3, p.11: "We
represent each polytope by an explicit list of linear inequalities with rational coefficients
and each utility by an explicit list of monomials with rational coefficients"): the list of its
players. The number of players is the length of the list. -/
structure MLGame where
  /-- the players `1, …, n` (0-based in Lean) -/
  players : List MLPlayer

namespace MLGame

/-- the number of players `n` -/
def n (G : MLGame) : ℕ := G.players.length

/-- the data of player `i` -/
def player (G : MLGame) (i : Fin G.n) : MLPlayer := G.players.get i

/-- the dimension `d_i` of player `i` -/
def dim (G : MLGame) (i : Fin G.n) : ℕ := (G.player i).dim

/-- a real strategy profile `x = (x_1, …, x_n)`, `x_i ∈ ℝ^{d_i}` -/
abbrev Profile (G : MLGame) : Type := (i : Fin G.n) → Fin (G.dim i) → ℝ

/-- a vector `y ∈ ℝ^d` satisfies the inequality row `(a, b)`: `∑_c a_c y_c ≤ b` -/
def rowHolds {d : ℕ} (r : List ℚ × ℚ) (y : Fin d → ℝ) : Prop :=
  ∑ c : Fin d, ((r.1.getD c.val 0 : ℚ) : ℝ) * y c ≤ (r.2 : ℝ)

/-- the strategy polytope `X_i = {y ∈ ℝ^{d_i} : A_i y ≤ b_i}` of player `i` -/
def strategySet (G : MLGame) (i : Fin G.n) : Set (Fin (G.dim i) → ℝ) :=
  {y | ∀ r ∈ (G.player i).rows, rowHolds r y}

/-- the value of the variable `(j, c)` (coordinate `c` of player `j`) in a profile; `0` for an
out-of-range index (excluded by `WellFormed`) -/
def coord (G : MLGame) (x : G.Profile) (v : ℕ × ℕ) : ℝ :=
  if h : v.1 < G.n then (if h' : v.2 < G.dim ⟨v.1, h⟩ then x ⟨v.1, h⟩ ⟨v.2, h'⟩ else 0) else 0

/-- the utility `u_i(x) = ∑_{(coef, vars)} coef · ∏_{v ∈ vars} x_v` of player `i` -/
def utility (G : MLGame) (i : Fin G.n) (x : G.Profile) : ℝ :=
  ((G.player i).monos.map fun m => (m.1 : ℝ) * (m.2.map (G.coord x)).prod).sum

/-- **Well-formedness** of the representation: every inequality row of player `i` has exactly
`d_i` coefficients; every variable of every monomial is in range; and the players occurring in a
monomial are pairwise distinct ("every monomial contains at most one coordinate of each
player's strategy (raised to the first power)", p.11). -/
def WellFormed (G : MLGame) : Prop :=
  ∀ i : Fin G.n, (∀ r ∈ (G.player i).rows, r.1.length = G.dim i) ∧
    ∀ m ∈ (G.player i).monos, (∀ v ∈ m.2, ∃ h : v.1 < G.n, v.2 < G.dim ⟨v.1, h⟩) ∧
      (m.2.map Prod.fst).Nodup

end MLGame

end CEPolytopeHard


