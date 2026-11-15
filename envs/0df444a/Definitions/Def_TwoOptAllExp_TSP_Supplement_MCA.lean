-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA
-- name    : TwoOptAllExp_TSP_Supplement_MCA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:42:10.183548+00:00
-- url     : https://prove2.me/theorems/08b8e946-e887-43ea-a647-137551f6305c
-- title:
--   Binary $(p,q,2)$-Maximum Constraint Assignment with the flip neighborhood
-- statement:
--   An instance of binary **Maximum Constraint Assignment** consists of variables $x_0,\dots,x_{N-1}$ taking values in $\{0,1\}$ and constraints $C_0,\dots,C_{m-1}$. Constraint $C_c$ has an ordered scope $(x_{i_1},\dots,x_{i_{p_c}})$ and assigns an integer weight $C_c(a_1,\dots,a_{p_c})$ to every assignment of the variables in its scope. The value of an assignment $\sigma$ is
--
--   $$\Phi(\sigma)=\sum_{c}C_c\bigl(\sigma(x_{i_1}),\dots,\sigma(x_{i_{p_c}})\bigr),$$
--
--   to be maximized. The instance is a **$(p,q,2)$-MCA instance** if every scope consists of at most $p$ distinct variables and every variable appears in at most $q$ constraints.
--
--   The **flip** of $x$ at $\sigma$ is $\sigma[x\mapsto 1-\sigma(x)]$; the flip neighborhood of $\sigma$ consists of all assignments obtained by flipping exactly one variable. A variable is **improving** if its flip increases $\Phi$; an assignment without improving variables is a **local optimum**. An **improving flip sequence** $(y_1,\dots,y_\ell)$ from $\sigma$ flips $y_j$ improvingly after $y_1,\dots,y_{j-1}$ have been flipped; it is **maximal** if it ends in a local optimum.
--
--   The local-search problem $(p,q,2)$-MCA with the flip neighborhood has these instances, all assignments as feasible solutions, objective $\Phi$ (maximized) and the flip neighborhood, as an instance of the published local-search interface whose all-exp property (Definition 4) is used by Theorems 2 and 3.
--
--   **Formalization Note** Values $0,1$ are `false`, `true`. The encoding size counts $N$, $m$, and for every constraint its arity, the binary lengths of its scope indices and the sign and binary length of every table entry (zero entries included), so large weights are not given unit cost.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §2.3, p. 8 (with §2.1, pp. 6–7)

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_LocalSearch

namespace TwoOptAllExp.TSP.Supplement

/-! # Binary Maximum Constraint Assignment with the flip neighborhood

Heimann, Hoang and Hougardy, *Closing All-Exp Gaps in Local Search for the Traveling Salesman
Problem and Maximum Constraint Assignment*, November 2, 2026 preprint (STOC 2027 submission #112),
§2.3, p. 8. Only the binary case `r = 2` is used in the paper; values `0, 1` are `false, true`. -/

/-- The integer value `[a] ∈ {0, 1}` of a Boolean value. -/
def b2i (a : Bool) : ℤ := if a then 1 else 0

/-- The flip of the variable `x` at the assignment `σ`: `σ[x ↦ 1 - σ(x)]` (§2.3, p. 8). -/
def flip {V : Type} [DecidableEq V] (σ : V → Bool) (x : V) : V → Bool :=
  Function.update σ x (!σ x)

/-- Performing the flips `y₁, …, y_ℓ` successively, starting from `σ`. -/
def applyFlips {V : Type} [DecidableEq V] (σ : V → Bool) (ys : List V) : V → Bool :=
  ys.foldl flip σ

/-- `x` is improving at `σ` for the objective `Φ` (to be maximized): its flip increases `Φ`. -/
def IsImprovingVar {V : Type} [DecidableEq V] (Φ : (V → Bool) → ℤ) (σ : V → Bool) (x : V) :
    Prop :=
  Φ σ < Φ (flip σ x)

/-- `(y₁, …, y_ℓ)` is an improving flip sequence from `σ` (§2.3, p. 8): the flip of `y_j` is
improving after the preceding flips `y₁, …, y_{j-1}` have been performed. -/
def IsImprovingFlipSeq {V : Type} [DecidableEq V] (Φ : (V → Bool) → ℤ) :
    (V → Bool) → List V → Prop
  | _, [] => True
  | σ, y :: ys => IsImprovingVar Φ σ y ∧ IsImprovingFlipSeq Φ (flip σ y) ys

/-- An assignment with no improving variable is a local optimum (§2.3, p. 8). -/
def IsLocalMax {V : Type} [DecidableEq V] (Φ : (V → Bool) → ℤ) (σ : V → Bool) : Prop :=
  ∀ x, ¬ IsImprovingVar Φ σ x

/-- A maximal improving flip sequence from `σ`: an improving flip sequence ending in a local
optimum (§2.1, p. 7, and §2.3, p. 8). -/
def IsMaximalFlipSeq {V : Type} [DecidableEq V] (Φ : (V → Bool) → ℤ) (σ : V → Bool)
    (ys : List V) : Prop :=
  IsImprovingFlipSeq Φ σ ys ∧ IsLocalMax Φ (applyFlips σ ys)

/-- An instance of binary Maximum Constraint Assignment (§2.3, p. 8): variables `x_0, …, x_{N-1}`
and constraints `C_0, …, C_{m-1}`. Constraint `C_c` has the ordered scope
`(x_{i_1}, …, x_{i_{p_c}})` and assigns the integer weight `table c a` to every assignment `a` of
the variables in its scope (`a k` is the value of the `k`-th scope variable). -/
structure MCAInstance where
  /-- The number of variables. -/
  N : ℕ
  /-- The number of constraints. -/
  m : ℕ
  /-- The ordered scope of every constraint. -/
  scope : Fin m → List (Fin N)
  /-- The weight table of every constraint. -/
  table : (c : Fin m) → (Fin (scope c).length → Bool) → ℤ

namespace MCAInstance

variable (I : MCAInstance)

/-- The value `Φ(σ) = ∑_{C ∈ 𝒞} C(σ(x_{i_1}), …, σ(x_{i_p}))` of an assignment (§2.3, p. 8). -/
def Φ (σ : Fin I.N → Bool) : ℤ :=
  ∑ c : Fin I.m, I.table c (fun k => σ ((I.scope c).get k))

/-- `I` is a `(p, q, 2)`-MCA instance (§2.3, p. 8): every constraint has at most `p` distinct
variables, and every variable appears in at most `q` constraints. -/
def IsPQ (p q : ℕ) : Prop :=
  (∀ c : Fin I.m, (I.scope c).Nodup ∧ (I.scope c).length ≤ p) ∧
  ∀ x : Fin I.N, (Finset.univ.filter (fun c : Fin I.m => x ∈ I.scope c)).card ≤ q

/-- The binary encoding size of an instance: the numbers of variables and constraints, and for
every constraint its arity, the binary indices of its scope variables, and the sign and binary
magnitude of every entry of its weight table (zero entries included). -/
def size : ℕ :=
  I.N + I.m + ∑ c : Fin I.m,
    (1 + (I.scope c).length + ((I.scope c).map (fun x => Nat.size x.val + 1)).sum +
      ∑ a : Fin (I.scope c).length → Bool, (Nat.size (I.table c a).natAbs + 2))

/-- The search space of an instance with the flip neighborhood (§2.3, p. 8): all assignments are
feasible, the objective `Φ` is maximized, and the neighbors of `σ` are the assignments obtained by
flipping exactly one variable. -/
def flipSpace : SearchSpace where
  Sol := Fin I.N → Bool
  sol_finite := inferInstance
  obj := I.Φ
  Nbr σ := {σ' | ∃ x, σ' = flip σ x}
  minimize := false

end MCAInstance

/-- The local-search problem `(p, q, 2)`-MCA with the flip neighborhood (§2.3, p. 8): instances
are the `(p, q, 2)`-MCA instances, with their binary encoding size. -/
def mcaFlip (p q : ℕ) : LocalSearchProblem where
  Inst := {I : MCAInstance // I.IsPQ p q}
  size I := I.1.size
  space I := I.1.flipSpace

end TwoOptAllExp.TSP.Supplement


