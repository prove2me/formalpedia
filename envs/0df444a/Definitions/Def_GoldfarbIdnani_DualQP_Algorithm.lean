-- Prove2me | Definitions.Def_GoldfarbIdnani_DualQP_Algorithm
-- name    : GoldfarbIdnani_DualQP_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:14:38.602801+00:00
-- url     : https://prove2.me/theorems/224ead9d-ff8c-4eeb-93ad-8cd74511868d
-- title:
--   The dual algorithm (Section 3, pp. 6–7) as a nondeterministic step relation
-- statement:
--   This module states the dual algorithm of Goldfarb and Idnani for the quadratic program (1.1), minimize $f(x) = a^{\mathsf T}x + \tfrac12x^{\mathsf T}Gx$ subject to $s(x) = C^{\mathsf T}x - b \ge 0$, as a transition relation on algorithm states. The notation ($n_i$, $s_i$, $g$, $N^*$, $H$, $u$, $r$, the dual update $u^+ + t(-r;1)$) is that of the module `GoldfarbIdnani.DualQP.QP`.
--
--   **States.** A state is one of
--   1. *Step 1* with current point $x$, active set $A$ and stored multiplier vector $u$;
--   2. *Step 2(a)* with current point $x$, active set $A$, violated constraint $p$ (so $n^+ = n_p$) and dual vector $u^+$ on $A \cup \{p\}$;
--   3. *STOP, optimal*, with the point $x$;
--   4. *STOP, infeasible*.
--
--   **Step 0.** The initial state is Step 1 with $x = x^0 = -G^{-1}a$, $A = \emptyset$ and $u$ empty.
--
--   **Step 1.** Let $V = \{j \in K \setminus A : s_j(x) < 0\}$. If $V = \emptyset$, STOP: $x$ is reported feasible and optimal. Otherwise, for **any** $p \in V$, move to Step 2(a) with $u^+ = (u; 0)$ ($u$ on $A$, $0$ at $p$; $u^+ = 0$ if $A = \emptyset$).
--
--   **Step 2.** With $q = |A|$, compute $z = Hn^+$ and $r = N^*n^+$ ($r$ empty if $q = 0$). Set $t_1 = +\infty$ if $r \le 0$ or $q = 0$, and otherwise
--
--   $$
--   t_1 = \min_{j \in A,\ r_j > 0} \frac{u^+_j}{r_j},
--   $$
--
--   attained at some $k \in A$; set $t_2 = +\infty$ if $z = 0$ and otherwise $t_2 = -s_p(x)/z^{\mathsf T}n^+$; let $t = \min(t_1, t_2)$.
--   1. If $t = \infty$: STOP, the subproblem $P(A \cup \{p\})$ and hence the QPP are infeasible.
--   2. If $t_2 = \infty > t_1$: for **any** minimizing $k$, $u^+ \leftarrow u^+ + t_1(-r; 1)$, drop $k$ ($A \leftarrow A \setminus \{k\}$), keep $x$, and return to Step 2(a).
--   3. If $t_2 < \infty$: $x \leftarrow x + tz$ and $u^+ \leftarrow u^+ + t(-r;1)$. If $t = t_2$ (full step), set $u \leftarrow u^+$, add $p$ ($A \leftarrow A \cup \{p\}$) and go to Step 1. If $t = t_1 < t_2$ (partial step), for **any** minimizing $k$, drop $k$ and return to Step 2(a).
--
--   The choices of $p \in V$ and of the minimizing index $k$ are left free, as in the paper: the relation has one transition for each admissible choice, so a statement about every run of the relation is a statement about every implementation of the algorithm. The algorithm's running value of $f$ and the matrices $J$, $R$ of Section 4 are bookkeeping and are not part of the state.
--
--   **Formalization Note.** Infinite step lengths are encoded by separate transitions rather than by a value $\infty$: "$t_1 = \infty$" is "$r_j \le 0$ for all $j \in A$", "$t_2 = \infty$" is "$z = 0$" (the paper's $|z| = 0$), and "$t = t_2$" is "$t_2 \le u^+_j/r_j$ for every $j \in A$ with $r_j > 0$", so a tie $t_1 = t_2$ takes the full step, as the paper tests $t = t_2$ first. After a drop, the dual vector is restricted to $(A \setminus\{k\}) \cup \{p\}$. Vectors indexed by constraints are functions `Fin m → ℝ`, zero off the current index set. The operators $H$ and $N^*$ are recomputed from the current active set rather than updated, which is what the paper's "update $H$ and $N^*$" amounts to in exact arithmetic.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), pp. 6–7, Section 3, Dual algorithm (Steps 0–2)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_QP

namespace GoldfarbIdnani.DualQP

open Matrix

/-- The states of the dual algorithm (Section 3, pp. 6–7).
* `step1 x A u`: about to execute Step 1 with current point `x`, active set `A` and stored
  multiplier vector `u` (indexed by `K`, supported on `A`);
* `step2 x A p u⁺`: about to execute Step 2(a) with current point `x`, active set `A`,
  violated constraint `p` (`n⁺ = n_p`) and dual vector `u⁺` (indexed by `K`, supported on
  `A ∪ {p}`; its entry at `p` is the paper's `u⁺_{q+1}`);
* `stopOptimal x`: STOP in Step 1, `x` reported feasible and optimal;
* `stopInfeasible`: STOP in Step 2(c)(i), the QPP reported infeasible. -/
inductive State (n m : ℕ) where
  | step1 (x : Fin n → ℝ) (A : Finset (Fin m)) (u : Fin m → ℝ)
  | step2 (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (uplus : Fin m → ℝ)
  | stopOptimal (x : Fin n → ℝ)
  | stopInfeasible

variable {n m : ℕ}

/-- Step 0: `x ← −G⁻¹a`, `A ← ∅`, `q ← 0`; the stored multiplier vector is empty (`0`). -/
noncomputable def initState (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) : State n m :=
  State.step1 (-(G⁻¹ *ᵥ a)) ∅ 0

/-- `k` attains the minimum in the partial step length `t₁` (Step 2(b)(i), (3.13)):
`k ∈ A`, `r_k > 0`, and `u_k / r_k ≤ u_j / r_j` for every `j ∈ A` with `r_j > 0`. -/
def IsT1Argmin (A : Finset (Fin m)) (u r : Fin m → ℝ) (k : Fin m) : Prop :=
  k ∈ A ∧ 0 < r k ∧ ∀ j ∈ A, 0 < r j → u k / r k ≤ u j / r j

/-- One step of the dual algorithm (Section 3, pp. 6–7), as a nondeterministic relation:
the choice of the violated constraint `p ∈ V` in Step 1 and of a minimizing index `k` in
Step 2(b)(i) is free. In Step 2, with `q = |A|`, `z = Hn⁺` and `r = N*n⁺` (Step 2(a); `r = 0`
when `q = 0`), `t₁ = ∞` iff no `r_j`, `j ∈ A`, is positive, `t₂ = ∞` iff `z = 0`, and
otherwise `t₂ = −s_p(x)/zᵀn⁺`. -/
inductive Step (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) : State n m → State n m → Prop where
  /-- Step 1, `V = {j ∈ K ∖ A | s_j(x) < 0} = ∅`: STOP, `x` is feasible and optimal. -/
  | step1_stop (x : Fin n → ℝ) (A : Finset (Fin m)) (u : Fin m → ℝ)
      (hV : ∀ j, j ∉ A → 0 ≤ slack C b x j) :
      Step a G C b (State.step1 x A u) (State.stopOptimal x)
  /-- Step 1, choose any `p ∈ V`; `n⁺ ← n_p`, `u⁺ ← (u; 0)` (`u ← 0` if `q = 0`). -/
  | step1_choose (x : Fin n → ℝ) (A : Finset (Fin m)) (u : Fin m → ℝ) (p : Fin m)
      (hpA : p ∉ A) (hp : slack C b x p < 0) :
      Step a G C b (State.step1 x A u) (State.step2 x A p (restrict A u))
  /-- Step 2(c)(i): `t₁ = t₂ = ∞`: STOP, `P(A⁺)` and hence the QPP are infeasible. -/
  | step2_infeasible (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (u : Fin m → ℝ)
      (hr : ∀ j ∈ A, multVec G C A (normal C p) j ≤ 0)
      (hz : Hmat G C A *ᵥ normal C p = 0) :
      Step a G C b (State.step2 x A p u) State.stopInfeasible
  /-- Step 2(c)(ii): `t₂ = ∞`, `t₁ < ∞` attained at `k`: `u⁺ ← u⁺ + t₁(−r; 1)`,
  `A ← A ∖ {k}`, `x` unchanged, go to Step 2(a). -/
  | step2_dual (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (u : Fin m → ℝ) (k : Fin m)
      (hz : Hmat G C A *ᵥ normal C p = 0)
      (hk : IsT1Argmin A u (multVec G C A (normal C p)) k) :
      Step a G C b (State.step2 x A p u)
        (State.step2 x (A.erase k) p
          (restrict (insert p (A.erase k))
            (dualStep u (multVec G C A (normal C p)) p
              (u k / multVec G C A (normal C p) k))))
  /-- Step 2(c)(iii), full step: `t₂ < ∞` and `t = t₂` (i.e. `t₂ ≤ t₁`):
  `x ← x + t₂z`, `u ← u⁺ + t₂(−r; 1)`, `A ← A ∪ {p}`, go to Step 1. -/
  | step2_full (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (u : Fin m → ℝ)
      (hz : Hmat G C A *ᵥ normal C p ≠ 0)
      (ht : ∀ j ∈ A, 0 < multVec G C A (normal C p) j →
        -slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p) ≤
          u j / multVec G C A (normal C p) j) :
      Step a G C b (State.step2 x A p u)
        (State.step1
          (x + (-slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p)) •
            (Hmat G C A *ᵥ normal C p))
          (insert p A)
          (dualStep u (multVec G C A (normal C p)) p
            (-slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p))))
  /-- Step 2(c)(iii), partial step: `t₂ < ∞` and `t = t₁ < t₂`, attained at `k`:
  `x ← x + t₁z`, `u⁺ ← u⁺ + t₁(−r; 1)`, `A ← A ∖ {k}`, go to Step 2(a). -/
  | step2_partial (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (u : Fin m → ℝ) (k : Fin m)
      (hz : Hmat G C A *ᵥ normal C p ≠ 0)
      (hk : IsT1Argmin A u (multVec G C A (normal C p)) k)
      (ht : u k / multVec G C A (normal C p) k <
        -slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p)) :
      Step a G C b (State.step2 x A p u)
        (State.step2
          (x + (u k / multVec G C A (normal C p) k) • (Hmat G C A *ᵥ normal C p))
          (A.erase k) p
          (restrict (insert p (A.erase k))
            (dualStep u (multVec G C A (normal C p)) p
              (u k / multVec G C A (normal C p) k))))

end GoldfarbIdnani.DualQP


