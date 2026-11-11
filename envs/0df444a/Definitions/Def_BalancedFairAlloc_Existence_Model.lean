-- Prove2me | Definitions.Def_BalancedFairAlloc_Existence_Model
-- name    : BalancedFairAlloc_Existence_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:11.67161+00:00
-- url     : https://prove2.me/theorems/3fab6734-5ed7-489c-a802-4805710f9365
-- title:
--   Additive mixed-manna instances, balanced allocations, EF[1,1], swapEF, P_bal, P_eq, constrained fPO, the weights α(w) and the dual LP (6)
-- statement:
--   There are $n$ agents $N=[n]$ (in Lean `Fin n`, numbered from $0$) and $m$ indivisible items $M=[m]$ (in Lean `Fin m`). Each agent $i$ has an additive valuation given by item values $v_{ig}\in\mathbb R$ of any sign (good, chore or neutral; **mixed manna**), `v : Fin n → Fin m → ℝ`; the value of a bundle $S\subseteq M$ is
--
--   $$v_i(S)=\sum_{g\in S}v_{ig}\qquad(\texttt{bval}).$$
--
--   An **integral complete allocation** is a map `A : Fin m → Fin n` sending each item to its owner; the **bundle** of agent $i$ is $A_i=\{g: A(g)=i\}$ (`bundle A i`). Writing $m=nr+s$ with $0\le s<n$ (so $r=\lfloor m/n\rfloor$, in Lean `m / n`), $A$ is **balanced** if $|A_i|\in\{r,r+1\}$ for every agent.
--
--   **EF[1,1]** (Definition 1, `IsEF11`): for all agents $i,j$ there are $C\subseteq A_i$ and $G\subseteq A_j$ with $|C|,|G|\le1$ and $v_i(A_i\setminus C)\ge v_i(A_j\setminus G)$. **swapEF** (Definition 2, `IsSwapEF`): for all $i,j$, either $v_i(A_i)\ge v_i(A_j)$ or there are $h\in A_i$, $g\in A_j$ with $v_i\big((A_i\setminus\{h\})\cup\{g\}\big)\ge v_i\big((A_j\setminus\{g\})\cup\{h\}\big)$.
--
--   A **fractional allocation** is a matrix $x\in\mathbb R^{N\times M}$, `Fin n → Fin m → ℝ`, with $x\ge0$ and $\sum_i x_{ig}\le1$ (`IsFracAlloc`); it is integral if its entries are $0$ or $1$ (`IsIntegralAlloc`); $v_i(x_i)=\sum_g x_{ig}v_{ig}$ (`fval`). `allocMatrix A` is the $0/1$ matrix of an integral allocation. The balanced polytope (2) and the exact-balance polytope are
--
--   $$P_{\mathrm{bal}}=\Big\{x\ge0:\ \sum_i x_{ig}=1\ \forall g,\ r\le\sum_g x_{ig}\le r+1\ \forall i\Big\},\qquad P_{\mathrm{eq}}=\Big\{x\ge0:\ \sum_i x_{ig}=1\ \forall g,\ \sum_g x_{ig}=r\ \forall i\Big\}.$$
--
--   `eqConstraintMatrix` and `balConstraintMatrix` are their integer constraint matrices apart from nonnegativity: one row per item, and one row per agent (two identical copies of it for $P_{\mathrm{bal}}$, one for each side of $r\le\sum_g x_{ig}\le r+1$); columns are the variables $x_{ig}$.
--
--   $y$ **Pareto dominates** $x$ if $v_i(y_i)\ge v_i(x_i)$ for every agent with at least one strict inequality. $x$ is **fPO in $P$** (Definition 6, `IsFPOIn v P x`) if $x\in P$ and no $y\in P$ Pareto dominates it. `MaximizesWeightedWelfare v α P x` says $x\in P$ and $x$ maximizes $\sum_i\alpha_iv_i(y_i)$ over $y\in P$.
--
--   Section 3 uses $V=\max_{i,g}|v_{ig}|$ (`vmax`, $0$ when there are no agents or items), $M_0=4V+1$ (`M0`), the standard simplex $\Delta=\{w\ge0:\sum_iw_i=1\}$ (Mathlib's `stdSimplex ℝ (Fin n)`), its faces $\Delta(T)=\{w\in\Delta: w_i=0\ \forall i\notin T\}$ (`simplexFace T`), and the weights (4)
--
--   $$\alpha_i(w)=\rho+(1-n\rho)\,w_i\qquad(\texttt{alphaW}\ \rho\ w).$$
--
--   The dual (6) of weighted welfare maximization over $P_{\mathrm{bal}}$ with weights $\alpha$ is: minimize $\Psi(\xi,p)=\sum_gp_g+r\sum_i\xi_i+\sum_i(\xi_i)_+$ (`dualObj`) subject to $\xi_i+p_g\ge\alpha_iv_{ig}$ for all $i,g$ (`IsDualFeasible`); `IsDualOptimal` is feasibility plus minimality of $\Psi$ among feasible points.
--
--   **Formalization Note.** Integral allocations in the paper's polytopes are complete, so they are encoded as maps `Fin m → Fin n`; balancedness uses natural-number division `m / n` for $r$. All quantities are real numbers.
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), pp. 8-11 (PDF 10-13), §2.1, Definitions 1, 2, 5, 6, eq. (2), P_eq; App. B p. 55 (PDF 57); pp. 13-14 (PDF 15-16), eqs. (4), (6); M0 p. 14 (PDF 16); Δ, Δ(T) p. 11 (PDF 13), Lemma 2

import Mathlib

namespace BalancedFairAlloc.Existence

open Finset

/-! ### Additive mixed-manna instances, balanced allocations, EF[1,1], swapEF, constrained fPO

Cookson, Shah, Verma, *Fair and Efficient Balanced Allocations for Additive Valuations*,
arXiv:2608.06325, §2.1 (pp. 8–11) and §3.1 (pp. 13–14).

Agents are `Fin n` (the paper's `N = [n]`, numbered from `0`) and items are `Fin m`
(the paper's `M = [m]`). A valuation profile is `v : Fin n → Fin m → ℝ`, `v i g = v_{ig}`,
with no sign restriction (mixed manna). -/

/-- An integral complete allocation: item `g` is given to agent `A g`. -/
abbrev Allocation (n m : ℕ) := Fin m → Fin n

/-- The bundle `A_i = {g : A g = i}` of agent `i`. -/
def bundle {n m : ℕ} (A : Allocation n m) (i : Fin n) : Finset (Fin m) :=
  univ.filter (fun g => A g = i)

/-- Additive value `v_i(S) = ∑_{g ∈ S} v_{ig}` of a bundle `S` for agent `i`. -/
def bval {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (S : Finset (Fin m)) : ℝ :=
  ∑ g ∈ S, v i g

/-- Balancedness (p. 10): writing `m = n r + s` with `0 ≤ s < n`, so `r = m / n`, every bundle
has `r` or `r + 1` items. -/
def IsBalanced {n m : ℕ} (A : Allocation n m) : Prop :=
  ∀ i : Fin n, (bundle A i).card = m / n ∨ (bundle A i).card = m / n + 1

/-- EF[1,1] (Definition 1): for all agents `i, j` there are `C ⊆ A_i`, `G ⊆ A_j` with
`|C|, |G| ≤ 1` and `v_i(A_i \ C) ≥ v_i(A_j \ G)`. -/
def IsEF11 {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) : Prop :=
  ∀ i j : Fin n, ∃ C ⊆ bundle A i, ∃ G ⊆ bundle A j, C.card ≤ 1 ∧ G.card ≤ 1 ∧
    bval v i (bundle A j \ G) ≤ bval v i (bundle A i \ C)

/-- Swap envy-freeness (Definition 2): for all agents `i, j`, either `v_i(A_i) ≥ v_i(A_j)` or
there are `h ∈ A_i`, `g ∈ A_j` with `v_i((A_i \ {h}) ∪ {g}) ≥ v_i((A_j \ {g}) ∪ {h})`. -/
def IsSwapEF {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) : Prop :=
  ∀ i j : Fin n, bval v i (bundle A j) ≤ bval v i (bundle A i) ∨
    ∃ h ∈ bundle A i, ∃ g ∈ bundle A j,
      bval v i (insert h ((bundle A j).erase g)) ≤ bval v i (insert g ((bundle A i).erase h))

/-- A fractional allocation is a real matrix `x : Fin n → Fin m → ℝ`; agent `i`'s utility is
`v_i(x_i) = ∑_g x_{ig} v_{ig}`. -/
def fval {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (x : Fin n → Fin m → ℝ) : ℝ :=
  ∑ g, x i g * v i g

/-- A fractional allocation (p. 9): `x ≥ 0` and `∑_i x_{ig} ≤ 1` for every item `g`. -/
def IsFracAlloc {n m : ℕ} (x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i g, 0 ≤ x i g) ∧ ∀ g, ∑ i, x i g ≤ 1

/-- An integral (possibly partial) allocation in matrix form: a fractional allocation with
entries in `{0, 1}`. -/
def IsIntegralAlloc {n m : ℕ} (x : Fin n → Fin m → ℝ) : Prop :=
  IsFracAlloc x ∧ ∀ i g, x i g = 0 ∨ x i g = 1

/-- The matrix form of an integral complete allocation: `x_{ig} = 1` iff `g ∈ A_i`. -/
def allocMatrix {n m : ℕ} (A : Allocation n m) : Fin n → Fin m → ℝ :=
  fun i g => if A g = i then 1 else 0

/-- The balanced polytope `P_bal` of eq. (2): `x ≥ 0`, `∑_i x_{ig} = 1` for every item, and
`r ≤ ∑_g x_{ig} ≤ r + 1` for every agent, with `r = m / n`. -/
def Pbal (n m : ℕ) : Set (Fin n → Fin m → ℝ) :=
  {x | (∀ i g, 0 ≤ x i g) ∧ (∀ g, ∑ i, x i g = 1) ∧
    ∀ i, ((m / n : ℕ) : ℝ) ≤ ∑ g, x i g ∧ ∑ g, x i g ≤ ((m / n : ℕ) : ℝ) + 1}

/-- The exact-balance polytope `P_eq` (p. 11, used when `n ∣ m`): `x ≥ 0`, `∑_i x_{ig} = 1`
for every item and `∑_g x_{ig} = r` for every agent, with `r = m / n`. -/
def Peq (n m : ℕ) : Set (Fin n → Fin m → ℝ) :=
  {x | (∀ i g, 0 ≤ x i g) ∧ (∀ g, ∑ i, x i g = 1) ∧ ∀ i, ∑ g, x i g = ((m / n : ℕ) : ℝ)}

/-- Constraint matrix of `P_eq` apart from nonnegativity (Appendix B): rows are the item
constraints `g` (`Sum.inl g`) and the agent constraints `i` (`Sum.inr i`); columns are the
variables `x_{ig}`, indexed by `(i, g)`. -/
def eqConstraintMatrix (n m : ℕ) : Matrix (Fin m ⊕ Fin n) (Fin n × Fin m) ℤ :=
  fun row col => match row with
    | Sum.inl g => if col.2 = g then 1 else 0
    | Sum.inr i => if col.1 = i then 1 else 0

/-- Constraint matrix of `P_bal` apart from nonnegativity (Appendix B): the item rows, then two
copies of each agent row (`Sum.inr (Sum.inl i)` for `r ≤ ∑_g x_{ig}` and `Sum.inr (Sum.inr i)` for
`∑_g x_{ig} ≤ r + 1`), as in the paper ("two copies of the same row"). -/
def balConstraintMatrix (n m : ℕ) : Matrix (Fin m ⊕ (Fin n ⊕ Fin n)) (Fin n × Fin m) ℤ :=
  fun row col => match row with
    | Sum.inl g => if col.2 = g then 1 else 0
    | Sum.inr (Sum.inl i) => if col.1 = i then 1 else 0
    | Sum.inr (Sum.inr i) => if col.1 = i then 1 else 0

/-- `y` Pareto dominates `x` (Definitions 5, 6): `v_i(y_i) ≥ v_i(x_i)` for every agent, with at
least one strict inequality. -/
def ParetoDominates {n m : ℕ} (v : Fin n → Fin m → ℝ) (y x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, fval v i x ≤ fval v i y) ∧ ∃ i, fval v i x < fval v i y

/-- Constrained fractional Pareto optimality (Definition 6): `x ∈ P` and no `y ∈ P` Pareto
dominates `x`. Applied to `allocMatrix A` for an integral allocation `A`. -/
def IsFPOIn {n m : ℕ} (v : Fin n → Fin m → ℝ) (P : Set (Fin n → Fin m → ℝ))
    (x : Fin n → Fin m → ℝ) : Prop :=
  x ∈ P ∧ ¬ ∃ y ∈ P, ParetoDominates v y x

/-- `x` maximizes the weighted welfare `∑_i α_i v_i(y_i)` over `y ∈ P` (and lies in `P`). -/
def MaximizesWeightedWelfare {n m : ℕ} (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    (P : Set (Fin n → Fin m → ℝ)) (x : Fin n → Fin m → ℝ) : Prop :=
  x ∈ P ∧ ∀ y ∈ P, ∑ i, α i * fval v i y ≤ ∑ i, α i * fval v i x

/-- `V := max_{i,g} |v_{ig}|` (p. 13); it is `0` when there are no agents or no items. -/
def vmax {n m : ℕ} (v : Fin n → Fin m → ℝ) : ℝ :=
  (univ : Finset (Fin n × Fin m)).fold max 0 (fun ig => |v ig.1 ig.2|)

/-- The box radius `M₀ := 4V + 1` (p. 14). -/
def M0 {n m : ℕ} (v : Fin n → Fin m → ℝ) : ℝ := 4 * vmax v + 1

/-- The weights `α_i(w) := ρ + (1 − nρ) w_i` of eq. (4), for `w` in the standard simplex
`Δ = stdSimplex ℝ (Fin n)`. -/
def alphaW {n : ℕ} (ρ : ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ρ + (1 - (n : ℝ) * ρ) * w i

/-- The face `Δ(T) = {w ∈ Δ : w_i = 0 for i ∉ T}` of the standard simplex
`Δ = stdSimplex ℝ (Fin n) = {w ∈ ℝ^n_{≥0} : ∑_i w_i = 1}` (Lemma 2, p. 11). -/
def simplexFace {n : ℕ} (T : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {w | w ∈ stdSimplex ℝ (Fin n) ∧ ∀ i, i ∉ T → w i = 0}

/-- The dual objective `Ψ(ξ, p) = ∑_g p_g + r ∑_i ξ_i + ∑_i (ξ_i)_+` of eq. (6), `r = m / n`. -/
def dualObj (n m : ℕ) (ξ : Fin n → ℝ) (p : Fin m → ℝ) : ℝ :=
  ∑ g, p g + ((m / n : ℕ) : ℝ) * ∑ i, ξ i + ∑ i, max (ξ i) 0

/-- Dual feasibility in eq. (6) for weights `α`: `ξ_i + p_g ≥ α_i v_{ig}` for all `i, g`. -/
def IsDualFeasible {n m : ℕ} (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) (ξ : Fin n → ℝ)
    (p : Fin m → ℝ) : Prop :=
  ∀ i g, α i * v i g ≤ ξ i + p g

/-- `(ξ, p)` is an optimal solution of the dual (6) for weights `α`. -/
def IsDualOptimal {n m : ℕ} (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) (ξ : Fin n → ℝ)
    (p : Fin m → ℝ) : Prop :=
  IsDualFeasible v α ξ p ∧
    ∀ (ξ' : Fin n → ℝ) (p' : Fin m → ℝ), IsDualFeasible v α ξ' p' →
      dualObj n m ξ p ≤ dualObj n m ξ' p'

end BalancedFairAlloc.Existence


