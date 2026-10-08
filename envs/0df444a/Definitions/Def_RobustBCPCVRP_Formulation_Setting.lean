-- Prove2me | Definitions.Def_RobustBCPCVRP_Formulation_Setting
-- name    : RobustBCPCVRP_Formulation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:38:51.073034+00:00
-- url     : https://prove2.me/theorems/1a379eb5-583e-4f45-a0c7-5b6848c23fda
-- title:
--   §1–§2, pp. 1–4 — CVRP walks, routes, q-routes without 2-cycles, solutions, edge incidence and columns
-- statement:
--   Let $G=(V,E)$ be an undirected graph on the vertices $V=\{0,1,\dots,n\}$; vertex $0$ is the **depot** and $V_+=\{1,\dots,n\}$ are the **clients**, each with a demand $d_i$. There are $K$ vehicles of capacity $C$.
--
--   A list of clients $r=(r_1,\dots,r_m)$, $m\ge 1$, describes the closed walk
--   $$0\to r_1\to r_2\to\cdots\to r_m\to 0 .$$
--   Its **edge incidence vector** $q^e(r)$ counts how many times this walk traverses the edge $e=\{u,v\}$ (a one-client walk $0\to j\to 0$ traverses $\{0,j\}$ twice), and its **load** is $d_{r_1}+\cdots+d_{r_m}$, counted with multiplicity. The list is a *walk in $G$* if it is nonempty, contains no depot and every traversed edge lies in $E$.
--
--   1. A **CVRP route** is a walk in $G$ whose clients are pairwise distinct and whose load is at most $C$ (§1, p. 1, conditions (i)–(iii)).
--   2. A **q-route without 2-cycles** is a walk in $G$ with load at most $C$ in which clients may repeat, but no subpath $i\to j\to i$ with $i\neq 0$ occurs, i.e. $r_k\neq r_{k+2}$ for all $k$ (§1, p. 2 and §2, p. 4).
--   3. A **CVRP solution** is a family $R=(R_1,\dots,R_K)$ of $K$ CVRP routes such that every client is visited exactly once by exactly one vehicle. Its **edge vector** is $\chi(R)_e=\sum_{k}q^e(R_k)$ and its **cost** is the total length $\sum_k\sum_{e\text{ on }R_k}\ell_e$ of its walks.
--   4. A **family of columns** is a finitely supported weight $\lambda$ on client lists whose support consists of q-routes without 2-cycles, with $\lambda_r\ge 0$. It defines $(Q\lambda)_e=\sum_r q^e(r)\,\lambda_r$ and $\sum_r\lambda_r$; these are the left-hand sides of constraints (5) and (6) of the paper.
--   5. A vector $x$ is **integer** if every coordinate is an integer.
--
--   These are the combinatorial objects in terms of which the polytopes $P_1$, $P_2$, $P_3$ and the Dantzig–Wolfe master of the paper are written.
--
--   **Formalization Note** Vertices are `Fin (n+1)` with depot `0`, edges are unordered pairs `Sym2 (Fin (n+1))`, demands are natural numbers, and $K, C$ are natural numbers. The paper's matrix $Q$ of all $p$ q-routes is replaced by a finitely supported weight `lam : List (Fin (n+1)) →₀ ℝ` ranging over **all** q-routes without 2-cycles (no fixed column list); a column $j$ with $\lambda_j=0$ is simply absent from the support. The paper's 2-cycle condition "$i\to j\to i$, $i\ne 0$" is a pattern on the client list: the one-client walk $0\to j\to 0$ is a q-route.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 1 (§1, CVRP definition), p. 2 (§1, q-routes), p. 4 (§2, q-routes without 2-cycles, matrix Q)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_demand
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound

namespace RobustBCPCVRP.Formulation

/-! Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, *Robust
branch-and-cut-and-price for the capacitated vehicle routing problem*, §1, pp. 1–2 and §2, p. 4:
the CVRP on a graph `G = (V, E)` with `V = {0, …, n}` (depot `0`), walks from the depot, CVRP
routes, q-routes without 2-cycles, CVRP solutions with `K` routes, and columns of q-routes. -/

variable {n : ℕ}

/-- The closed walk `0 → r₁ → ⋯ → r_m → 0` described by the client list `r`. -/
def walk (r : List (Fin (n + 1))) : List (Fin (n + 1)) :=
  0 :: (r ++ [0])

/-- The edges traversed by the walk of `r`, in order, with repetitions. -/
def edges (r : List (Fin (n + 1))) : List (Sym2 (Fin (n + 1))) :=
  ((walk r).zip (walk r).tail).map (fun p => s(p.1, p.2))

/-- Edge incidence `q^e`: the number of times the walk of `r` traverses the edge `e`. -/
def inc (r : List (Fin (n + 1))) (e : Sym2 (Fin (n + 1))) : ℕ :=
  (edges r).count e

/-- Total demand of the clients of `r`, counted with multiplicity. -/
def load (d : Fin (n + 1) → ℕ) (r : List (Fin (n + 1))) : ℕ :=
  (r.map d).sum

/-- `r` is a nonempty list of clients whose walk from the depot back to the depot uses only
edges of `E`. -/
def IsWalkIn (E : Finset (Sym2 (Fin (n + 1)))) (r : List (Fin (n + 1))) : Prop :=
  r ≠ [] ∧ (0 : Fin (n + 1)) ∉ r ∧ ∀ e ∈ edges r, e ∈ E

/-- No 2-cycle: the client list has no subpath `i → j → i`. -/
def NoTwoCycle (r : List (Fin (n + 1))) : Prop :=
  ∀ k (hk : k + 2 < r.length), r[k] ≠ r[k + 2]

/-- A CVRP route (p. 1, (i)–(iii)): a walk from the depot back to the depot that visits each of
its clients once, with total demand at most `C`. -/
def IsRoute (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (C : ℕ)
    (r : List (Fin (n + 1))) : Prop :=
  IsWalkIn E r ∧ r.Nodup ∧ load d r ≤ C

/-- A q-route without 2-cycles (pp. 2 and 4): a walk from the depot back to the depot whose
clients (repetitions allowed) have total demand at most `C`, with no subpath `i → j → i`. -/
def IsQRoute (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (C : ℕ)
    (r : List (Fin (n + 1))) : Prop :=
  IsWalkIn E r ∧ NoTwoCycle r ∧ load d r ≤ C

/-- A feasible CVRP solution (p. 1): `K` CVRP routes such that every client is visited by
exactly one vehicle, exactly once. -/
def IsCVRPSolution (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (R : Fin K → List (Fin (n + 1))) : Prop :=
  (∀ k, IsRoute E d C (R k)) ∧ ∀ i : Fin (n + 1), i ≠ 0 → ∑ k, (R k).count i = 1

/-- The edge vector `x` of a solution: `x_e` is the number of times the routes traverse `e`. -/
def chi {K : ℕ} (R : Fin K → List (Fin (n + 1))) (e : Sym2 (Fin (n + 1))) : ℝ :=
  ∑ k, (inc (R k) e : ℝ)

/-- The total length of the routes of a solution. -/
def cost (ℓ : Sym2 (Fin (n + 1)) → ℝ) {K : ℕ} (R : Fin K → List (Fin (n + 1))) : ℝ :=
  ∑ k, ((edges (R k)).map ℓ).sum

/-- A family of columns: a finitely supported weight `λ_r` on client lists whose support
consists of q-routes without 2-cycles, with nonnegative weights. -/
def IsColumns (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (C : ℕ)
    (lam : List (Fin (n + 1)) →₀ ℝ) : Prop :=
  ∀ r ∈ lam.support, IsQRoute E d C r ∧ 0 ≤ lam r

/-- `(Qλ)_e = ∑_j q^e_j λ_j`, the left-hand side of (5) without `x_e`. -/
noncomputable def colSum (lam : List (Fin (n + 1)) →₀ ℝ) (e : Sym2 (Fin (n + 1))) : ℝ :=
  ∑ r ∈ lam.support, lam r * (inc r e : ℝ)

/-- `∑_j λ_j`, the left-hand side of (6). -/
noncomputable def colCount (lam : List (Fin (n + 1)) →₀ ℝ) : ℝ :=
  ∑ r ∈ lam.support, lam r

/-- An integer vector. -/
def IsIntegerVec (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  ∀ e, ∃ z : ℤ, x e = z

end RobustBCPCVRP.Formulation


