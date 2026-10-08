-- Prove2me | Definitions.Def_JeroslowMLP_Value_Game
-- name    : JeroslowMLP_Value_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:59:12.448679+00:00
-- url     : https://prove2.me/theorems/3463c53d-7349-4c18-88f7-0350b007be5b
-- title:
--   §4, pp. 154–155 — the (p+1)-level linear game J′(F)
-- statement:
--   Fix $p\ge1$, block sizes $n_1,\dots,n_p$ and a formula $F$ over the blocked atoms; let $L$ be the length of $F$ and write $\exists_k$ for "$p-k$ is even" ($Q_k$ existential). The game $J'(F)$ has the players $0,1,\dots,p$; player $0$ (the **bookkeeper**) moves last and player $p$ first. Its variables and constraints are:
--
--   1. the atom variables $x_{kj}\in[0,1]$, controlled by player $k$, and the node variables $x(G)$ of $L_F$, controlled by player $0$, subject to $L_F$;
--   2. a variable $u$, controlled by player $0$, with $u=1$;
--   3. for every atom $x_{kj}$ of a block $k\ge2$, two copies of the gadget (4.1), one on $\xi=x_{kj}$ and one on $\xi=1-x_{kj}$:
--   $$z\ge 2y-\xi,\qquad z\ge-(2y-\xi),\qquad 0\le y\le1,$$
--   with $y$ controlled by player $1$ and $z$ (unbounded above) by player $0$;
--   4. for every atom $x_{1j}$ of block $1$, and for $x(F)$, the gadget (4.6) on $\xi$: $z\le\xi$, $z\le1-\xi$, with $z$ controlled by player $0$.
--
--   The criteria, all minimised, are:
--
--   1. player $0$: $\sum z$ over the (4.1) gadgets minus $\sum z$ over the (4.6) gadgets, plus $\sum_G x(G)$ over the non-atomic subformulas;
--   2. player $1$: $u-x(F)$ if $\exists_1$ and $x(F)$ otherwise, plus $z$ of the (4.6) gadget on $x(F)$, plus $10L\sum_j z$ over the (4.6) gadgets on the $x_{1j}$, minus $\sum z$ over all (4.1) gadgets ((4.7)/(4.8));
--   3. player $k$, $2\le k\le p$: $u-x(F)$ if $\exists_k$ and $x(F)$ otherwise, plus $2y$ for both gadgets of every atom of its own block ((4.4)/(4.5)).
--
--   After the bookkeeper and player 1 have moved, these become the functions $Z_k=1-x(F)+2\sum_jP(x_{kj})$ (or $x(F)+2\sum_jP(x_{kj})$) and $Z_1=(1-x(F))+fr(1-x(F))+10L\sum_j fr(x_{1j})+\dots$ of the paper. The game reduces the $\Sigma_p$ sentence (3.3) to the value of a linear multi-level program with fixed criteria.
--
--   **Formalization Note** Lean blocks are 0-based: the atoms of block `k : Fin p` (the paper's $X_{k+1}$) are owned by player `k + 1`, and the (4.1) gadgets exist for the blocks with `1 ≤ k.val`; for $p=1$ there are none. Player 0 controls the $x(G)$, and its criterion includes $+x(G)$ for every non-atomic subformula, exactly as the sentence on p. 155 states. The constant $1$ of (4.4)/(4.7) enters through the variable $u$ with $u=1$, as on p. 155. Because $fr(1-x)=fr(x)$, a single (4.6) gadget on $x(F)$ serves both (4.7) and (4.8). If $F$ is an atom, $x(F)$ is that atom's variable and there are no node variables.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), pp. 154–155, §4, (4.1), (4.4)–(4.8)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Multilevel
import Definitions.Def_JeroslowMLP_Value_Formula

namespace JeroslowMLP.Value

/-- The variables of the `(p+1)`-level game `J'(F)` (§4, pp. 154–155).
* `atom a` — the binary-intended variable `x_{kj}` of the logical variable `a = ⟨k, j⟩`;
* `node g` — the variable `x(G)` of a non-atomic subformula occurrence `G` of `F`;
* `one` — the variable `u`, fixed by `u = 1`;
* `gy g s`, `gz g s` — the variables `y`, `z` of a (4.1) gadget, for an atom `g` of a block
  owned by a paper player `≥ 2`; `s = false` is the gadget on `x_{kj}`, `s = true` the gadget
  on `1 - x_{kj}`;
* `fz a` — the (4.6) variable `z` on an atom `a` of block `X₁`;
* `fzF` — the (4.6) variable `z` on `x(F)`. -/
inductive GVar (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) where
  | atom (a : Atom p n)
  | node (g : F.Node)
  | one
  | gy (g : {a : Atom p n // 1 ≤ a.1.val}) (s : Bool)
  | gz (g : {a : Atom p n // 1 ≤ a.1.val}) (s : Bool)
  | fz (a : {a : Atom p n // a.1.val = 0})
  | fzF
  deriving Fintype

namespace GVar

variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

/-- `x(F)` as a linear expression in the game variables. -/
def xF (x : GVar p n F → ℝ) : ℝ := F.nodeVal (fun a => x (atom a)) (fun g => x (node g))

/-- The argument `ξ` of a (4.1) gadget: `x_{kj}` for `s = false`, `1 - x_{kj}` for `s = true`. -/
def gArg (x : GVar p n F → ℝ) (g : {a : Atom p n // 1 ≤ a.1.val}) (s : Bool) : ℝ :=
  if s then 1 - x (atom g.1) else x (atom g.1)

/-- The coefficient vector of `x(F)`: `xF x = ∑ v, xFcoef v * x v`. -/
def xFcoef : GVar p n F → ℝ
  | atom a => if F.rootAtom = some a then 1 else 0
  | node g => if F.isRootNode g then 1 else 0
  | _ => 0

end GVar

open GVar

/-- The feasible set `S₀` of `J'(F)`: the system `L_F` with every variable in `[0, 1]`, the
constraint `u = 1`, the (4.1) constraints `z ≥ 2y - ξ`, `z ≥ -(2y - ξ)`, `0 ≤ y ≤ 1` of every
gadget (no bound on `z`), and the (4.6) constraints `z ≤ ξ`, `z ≤ 1 - ξ` on each `x_{1j}` and
on `x(F)`. -/
def jFeasible (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) : Set (GVar p n F → ℝ) :=
  {x |
    (∀ a, 0 ≤ x (atom a) ∧ x (atom a) ≤ 1) ∧
    F.LSys (fun a => x (atom a)) (fun g => x (node g)) ∧
    x one = 1 ∧
    (∀ g s, 2 * x (gy g s) - gArg x g s ≤ x (gz g s) ∧
      -(2 * x (gy g s) - gArg x g s) ≤ x (gz g s) ∧
      0 ≤ x (gy g s) ∧ x (gy g s) ≤ 1) ∧
    (∀ a, x (fz a) ≤ x (atom a.1) ∧ x (fz a) ≤ 1 - x (atom a.1)) ∧
    x fzF ≤ xF x ∧ x fzF ≤ 1 - xF x}

/-- Control in `J'(F)`: the variables of block `X_{k+1}` (0-based block `k`) belong to player
`k + 1`; every `y` of (4.1) belongs to player `1`; the bookkeeper, player `0`, controls the
`x(G)`, `u` and every gadget variable `z`. -/
def jOwner {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)} : GVar p n F → ℕ
  | atom a => a.1.val + 1
  | gy _ _ => 1
  | _ => 0

/-- The criteria of `J'(F)` (all minimised), with `∃_i :≡ Even (p - i)` (`Q_i` existential):
* player `0`: `+z` for every (4.1) gadget, `-z` for every (4.6) gadget, and
  `+x(G)` for every non-atomic subformula occurrence;
* player `1`: `u - x(F)` if `∃_1`, `x(F)` otherwise ((4.7)/(4.8)), plus the (4.6) term on
  `x(F)`, plus `10 L ∑_j z` over the (4.6) gadgets on `x_{1j}` (`L` the length of `F`), minus
  `z` for every (4.1) gadget;
* player `i`, `2 ≤ i ≤ p`: `u - x(F)` if `∃_i`, `x(F)` otherwise ((4.4)/(4.5)), plus `2 y` for
  both gadgets of every variable of its own block `X_i`;
* every other player: `0`. -/
def jCost (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) : ℕ → GVar p n F → ℝ
  | 0, v =>
      match v with
      | node _ => 1
      | gz _ _ => 1
      | fz _ => -1
      | fzF => -1
      | _ => 0
  | 1, v =>
      (if Even (p - 1) then -1 else 1) * xFcoef v +
      match v with
      | one => if Even (p - 1) then 1 else 0
      | fzF => 1
      | fz _ => 10 * (F.length : ℝ)
      | gz _ _ => -1
      | _ => 0
  | i + 2, v =>
      if i + 2 ≤ p then
        (if Even (p - (i + 2)) then -1 else 1) * xFcoef v +
        match v with
        | one => if Even (p - (i + 2)) then 1 else 0
        | gy g _ => if g.1.1.val + 1 = i + 2 then 2 else 0
        | _ => 0
      else 0

/-- The `(p+1)`-level linear game `J'(F)` of §4, with players `0, 1, …, p`. -/
def jGame (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) : MultilevelProgram (GVar p n F) where
  feasible := jFeasible p n F
  owner := jOwner
  cost := jCost p n F

end JeroslowMLP.Value


