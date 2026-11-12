-- Prove2me | Definitions.Def_EuclidCVRP_Main_QPath
-- name    : EuclidCVRP_Main_QPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:38.968685+00:00
-- url     : https://prove2.me/theorems/0e75c56f-a576-4fdd-9d6b-a02bb94bd9fe
-- title:
--   The Unsplittable q-path problem (Definition 10)
-- statement:
--   **Definition 10.** Let $\varepsilon=1/m$ with $m\in\mathbb N$, $m\ge1$. An instance of the (Euclidean) **Unsplittable q-path problem** with parameter $\varepsilon$ consists of
--
--   1. a square bounding box $B$ of side length $L>0$; each side is cut into $m=1/\varepsilon$ segments of equal length, and the $4m$ segment endpoints are the **anchor points**;
--   2. $n$ non-terminal points inside $B$;
--   3. $\sigma$ pairs $(s_1,t_1),\dots,(s_\sigma,t_\sigma)$ of distinct anchor points (repetitions among pairs allowed), the terminals;
--   4. for each pair $i$, a positive integer $q_i$ (the number of $i$-paths) and a nonnegative budget $n_i$; with $q=\sum_i q_i$ and $N=\max_i n_i$,
--   5. for each non-terminal $v$ and pair $i$, a nonnegative integer $n_i(v)\le N+1$ (the $i$-rounded demand).
--
--   A **feasible solution** consists of exactly $q_i$ paths from $s_i$ to $t_i$ for each $i$ such that every non-terminal lies on exactly one path, and for each $i$ the non-terminals $V_i$ covered by the $i$-paths satisfy
--
--   $$\sum_{v\in V_i}n_i(v)=n_i.$$
--
--   The cost of a solution is the sum of the Euclidean lengths of all paths; the goal is a feasible solution of minimum cost.
--
--   An **$\alpha$-approximation algorithm with parameter $\varepsilon$ and running time polynomial in $n$, $q$, $N$** (for instances with at most $\sigma_0$ pairs) is a machine as in the CVRP definitions, polynomial in the length of an encoding that begins with $q+N$ in unary, whose output on every feasible instance encodes a feasible solution of cost at most $\alpha$ times that of every feasible solution.
--
--   Theorems 11 and 12 are stated with this problem.
--
--   **Formalization Note** Points and the box have rational coordinates. An $i$-path is the list of the non-terminals it visits in order; its length is that of the polygon $s_i\to\dots\to t_i$. Rounded demands are nonnegative, as in Definition 10 (§4 restates the problem with positive ones). The unary prefix makes "polynomial in $n$, $q$ and $N$" (the numbers, not their bit lengths) polynomial time in the encoding length. On infeasible instances the output of an algorithm is unconstrained.
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), Definition 10, p. 13; §4, p. 23 (restatement)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine

set_option autoImplicit false

namespace EuclidCVRP.Main

/-!
# The (Euclidean) Unsplittable q-path problem (Definition 10)

Blauth, Grandoni, Mátravölgyi, Mousavi, Ren, Salavatipour, STOC 2027 submission #1236 (October 2026),
Definition 10, p. 13; the parameter `ε` is `1/m` with `m ∈ ℕ` (the sides of `B` are cut into `1/ε`
segments).
-/

/-- **An instance of Unsplittable q-path with parameter `ε = 1/m`** (Definition 10, p. 13): a square
bounding box `B` (lower-left corner, side `L`), `n` non-terminal points, and `σ` terminal pairs
`(s_i, t_i)` of anchor points, given by their anchor indices, with the number `q_i` of `i`-paths,
the budget `n_i`, and the `i`-rounded demands `n_i(v)`. -/
structure QPathInstance where
  /-- `m = 1/ε`: each side of `B` is cut into `m` segments of equal length -/
  m : ℕ
  /-- the lower-left corner of `B` -/
  corner : ℚ × ℚ
  /-- the side length `L` of `B` -/
  L : ℚ
  /-- number of non-terminals -/
  n : ℕ
  /-- the non-terminal points -/
  pt : Fin n → ℚ × ℚ
  /-- number of terminal pairs -/
  σ : ℕ
  /-- anchor index of `s_i` -/
  s : Fin σ → ℕ
  /-- anchor index of `t_i` -/
  t : Fin σ → ℕ
  /-- the number `q_i` of `i`-paths -/
  q : Fin σ → ℕ
  /-- the budget `n_i` -/
  budget : Fin σ → ℕ
  /-- the `i`-rounded demand `n_i(v)` -/
  rdem : Fin σ → Fin n → ℕ

namespace QPathInstance

variable (J : QPathInstance)

/-- The anchor point with index `k ∈ {0, …, 4m−1}`: the endpoints of the `m` equal segments of each
side of `B`, numbered counterclockwise from the lower-left corner. -/
noncomputable def anchor (k : ℕ) : Pt :=
  let x0 : ℝ := J.corner.1
  let y0 : ℝ := J.corner.2
  let L : ℝ := J.L
  let r : ℝ := ((k % J.m : ℕ) : ℝ) * L / J.m
  match k / J.m with
  | 0 => !₂[x0 + r, y0]
  | 1 => !₂[x0 + L, y0 + r]
  | 2 => !₂[x0 + L - r, y0 + L]
  | _ => !₂[x0, y0 + L - r]

/-- `q = ∑ q_i`. -/
def qTotal : ℕ := ∑ i, J.q i

/-- `N = max_i n_i` (`0` when `σ = 0`). -/
def N : ℕ := Finset.univ.sup J.budget

/-- The data of Definition 10 are well formed: `m ≥ 1`, `L > 0`, the non-terminals lie in `B`, each
terminal pair consists of two distinct anchor points, `q_i ≥ 1`, and `n_i(v) ≤ N + 1`. -/
def Valid : Prop :=
  0 < J.m ∧ 0 < J.L ∧
  (∀ v, J.corner.1 ≤ (J.pt v).1 ∧ (J.pt v).1 ≤ J.corner.1 + J.L ∧
        J.corner.2 ≤ (J.pt v).2 ∧ (J.pt v).2 ≤ J.corner.2 + J.L) ∧
  (∀ i, J.s i < 4 * J.m ∧ J.t i < 4 * J.m ∧ J.s i ≠ J.t i) ∧
  (∀ i, 1 ≤ J.q i) ∧
  (∀ i v, J.rdem i v ≤ J.N + 1)

/-- The length of an `s_i`–`t_i` path visiting the non-terminals of `P` in order. -/
noncomputable def pathLen (i : Fin J.σ) (P : List (Fin J.n)) : ℝ :=
  let pts : List Pt := J.anchor (J.s i) :: (P.map (fun v => toPt (J.pt v)) ++ [J.anchor (J.t i)])
  ((pts.zip pts.tail).map (fun e => dist e.1 e.2)).sum

/-- A candidate solution: for each pair `i`, a list of `i`-paths, each the list of the non-terminals
it visits, in order. -/
abbrev Sol := Fin J.σ → List (List (Fin J.n))

/-- **Feasibility** (Definition 10): exactly `q_i` paths for each pair `i`; every non-terminal is
contained in exactly one path (once); and the `i`-rounded demand of the non-terminals `V_i`
covered by the `i`-paths is exactly the budget `n_i`. -/
def Feasible (x : J.Sol) : Prop := by
  classical
  exact (∀ i, (x i).length = J.q i) ∧
    (∀ v, (((List.finRange J.σ).map (fun i => (x i).flatten)).flatten).count v = 1) ∧
    (∀ i, ∑ v ∈ ((x i).flatten).toFinset, J.rdem i v = J.budget i)

/-- The cost: the sum of the Euclidean lengths of all paths. -/
noncomputable def cost (x : J.Sol) : ℝ := ∑ i, ((x i).map (J.pathLen i)).sum

/-- A solution written with indices as natural numbers, pair by pair. -/
def rawSol (x : J.Sol) : List (List (List ℕ)) :=
  (List.finRange J.σ).map (fun i => (x i).map (fun P => P.map Fin.val))

/-- `out` encodes a feasible solution of cost at most `α` times that of every feasible solution. -/
def IsApproxOutput (α : ℝ) (out : List (List (List ℕ))) : Prop :=
  ∃ x : J.Sol, J.Feasible x ∧ J.rawSol x = out ∧ ∀ x' : J.Sol, J.Feasible x' → J.cost x ≤ α * J.cost x'

end QPathInstance

/-- The binary encoding of a q-path instance. It begins with `q + N` in unary, so that "running time
polynomial in `n`, `q` and `N`" (the numbers, not their bit lengths) is polynomial time in the length of
this encoding; then `m`, the box, the non-terminals, and the terminal pairs with `q_i`, `n_i` and the
rounded demands. -/
def encQP (J : QPathInstance) : List Bool :=
  unaryBits (J.qTotal + J.N) ++ natBits J.m ++ ptBits J.corner ++ ratBits J.L ++
    listBits (fun v : Fin J.n => ptBits (J.pt v)) (List.finRange J.n) ++
    listBits (fun i : Fin J.σ => natBits (J.s i) ++ natBits (J.t i) ++ natBits (J.q i) ++
      natBits (J.budget i) ++ listBits (fun v : Fin J.n => natBits (J.rdem i v)) (List.finRange J.n))
      (List.finRange J.σ)

/-- The binary encoding of a q-path solution. -/
def qsolBits : List (List (List ℕ)) → List Bool := listBits (listBits (listBits natBits))

/-- **An `α`-approximation algorithm for Unsplittable q-path with parameter `ε = 1/m`, on instances
with at most `σ₀` terminal pairs, with running time polynomial in `n`, `q` and `N`**: a machine,
polynomial-time in the length of `encQP` (which contains `q + N` in unary), whose output on every
valid feasible instance with parameter `1/m` and `σ ≤ σ₀` is a feasible solution of cost at most `α`
times that of every feasible solution. On infeasible instances the output is unconstrained. -/
def IsQPathApproxAlg (m σ₀ : ℕ) (α : ℝ) (alg : List Bool → List (List (List ℕ))) : Prop :=
  PolyTimeFn qsolBits alg ∧
    ∀ J : QPathInstance, J.Valid → J.m = m → J.σ ≤ σ₀ → (∃ x : J.Sol, J.Feasible x) →
      J.IsApproxOutput α (alg (encQP J))

end EuclidCVRP.Main


