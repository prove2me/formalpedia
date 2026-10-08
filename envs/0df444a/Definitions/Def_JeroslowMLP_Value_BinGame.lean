-- Prove2me | Definitions.Def_JeroslowMLP_Value_BinGame
-- name    : JeroslowMLP_Value_BinGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:59:01.209389+00:00
-- url     : https://prove2.me/theorems/b78663df-a7b4-4b98-8a83-d0e24c342b39
-- title:
--   §3, p. 151 — the p-level pure binary game J(F)
-- statement:
--   For $p$ blocks of atoms and a formula $F$, the **pure binary multi-level program** $J(F)$ has $p$ players. Its constraints are $L_F(x^1,\dots,x^p,w)$ with every variable binary. The atom variables $x^k=(x_{kj})$ of block $X_k$ are controlled by player $k$, and player $1$ also controls the node variables $w$ (nominally, since they are determined by the atoms). Player $j$ minimises
--   $$x(F)\ \text{ if } p+j \text{ is odd},\qquad -x(F)\ \text{ otherwise}.$$
--   So player $p$ maximises $x(F)$, and the existential players try to make $F$ true while the universal ones look for a counterexample.
--
--   **Formalization Note** The paper's players $1,\dots,p$ are indices $0,\dots,p-1$ in Lean, so paper player $j$ is index $j-1$ and owns the 0-based block $j-1$; the parity test is on the paper's $j$.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 151, §3

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Multilevel
import Definitions.Def_JeroslowMLP_Value_Formula

namespace JeroslowMLP.Value

/-- The variables of the pure binary game `J(F)` (§3, p. 151): the atom variables `x_{kj}` and
the node variables `w = (x(G))` of `L_F`. -/
inductive BVar (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) where
  | atom (a : Atom p n)
  | node (g : F.Node)
  deriving Fintype

namespace BVar

variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

/-- `x(F)` as a linear expression in the variables of `J(F)`. -/
def xF (x : BVar p n F → ℝ) : ℝ := F.nodeVal (fun a => x (atom a)) (fun g => x (node g))

/-- The coefficient vector of `x(F)`: `xF x = ∑ v, xFcoef v * x v`. -/
def xFcoef : BVar p n F → ℝ
  | atom a => if F.rootAtom = some a then 1 else 0
  | node g => if F.isRootNode g then 1 else 0

end BVar

open BVar

/-- The `p`-level pure binary program `J(F)` (§3, p. 151). The paper's players `1, …, p` are
indices `0, …, p - 1` here. The constraints are `L_F` with every variable binary; the atoms of
block `X_{k+1}` (0-based block `k`) belong to player index `k` (paper player `k + 1`), and `w`
belongs to player index `0` (paper player `1`). Paper player `j = i + 1` minimises `x(F)` if
`p + j` is odd and `-x(F)` otherwise. -/
def binGame (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) : MultilevelProgram (BVar p n F) where
  feasible := {x | (∀ v, IsBinary (x v)) ∧ F.LSys (fun a => x (atom a)) (fun g => x (node g))}
  owner := fun v =>
    match v with
    | atom a => a.1.val
    | node _ => 0
  cost := fun i v => if i < p then (if Odd (p + (i + 1)) then 1 else -1) * xFcoef v else 0

end JeroslowMLP.Value


