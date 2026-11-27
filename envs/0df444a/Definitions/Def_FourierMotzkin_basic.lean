-- Prove2me | Definitions.Def_FourierMotzkin_basic
-- name    : FourierMotzkin_basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:42:22.069884+00:00
-- url     : https://prove2.me/theorems/ef5fa858-ed69-57f1-a840-1b77c391416e
-- title:
--   Fourier–Motzkin elimination and an exact LP solver
-- statement:
--   An exact linear programming solver by Fourier–Motzkin elimination, over the reals.
--
--   A **constraint** is a pair $(a,b)$ with $a=(a_0,a_1,\dots)$ a finite list of reals, read as $\sum_j a_jx_j\le b$ for $x:\mathbb N\to\mathbb R$ (missing coefficients are $0$); a **system** is a finite list of constraints, and `Sat sys x` says that $x$ satisfies all of them.
--
--   1. `elim j sys` eliminates the variable $x_j$: it keeps the constraints with $a_j=0$ and adds, for every pair $P$ with $a^P_j>0$ and $N$ with $a^N_j<0$, the positive combination $(-a^N_j)P+a^P_jN$, in which $x_j$ cancels.
--   2. `pick j sys x` is a value for $x_j$ compatible with all constraints given the other coordinates (the largest lower bound, else the smallest upper bound, else $0$); `stages`/`backSubst` undo a sequence of eliminations.
--   3. `lpMax c sys` maximizes $c\cdot x$ subject to `sys`: it adds a variable $z$ with $z\le c\cdot x$, eliminates all original variables, and reads off the remaining one-variable constraints $\alpha z\le\beta$; the result is `infeasible`, `unbounded`, or `opt v`.
--   4. `argmax c sys` recovers an optimal point by back-substitution.
--
--   The size of the systems may grow doubly exponentially, but every step uses only additions, multiplications, divisions and comparisons of reals, so the solver can be run on a real RAM. It is used to compute exactly the local linear programs (cut LP values, dominated Steiner trees and fragment shortenings) in an untimed implementation of the sublinear metric TSP estimator.
-- source:
--   J. B. J. Fourier (1827), T. S. Motzkin (1936); A. Schrijver, Theory of Linear and Integer Programming (1986), §12.2 (Fourier–Motzkin elimination). Context: Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §9.4 p.42 ('we can use standard polynomial-time LP solvers').

import Mathlib

/-! # Fourier–Motzkin elimination and an exact LP solver -/


namespace FourierMotzkin

def dot : List ℝ → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | a :: as, x => a * x 0 + dot as (fun i => x (i + 1))

def lc (s t : ℝ) : List ℝ → List ℝ → List ℝ
  | [], [] => []
  | a :: as, [] => s * a :: lc s t as []
  | [], b :: bs => t * b :: lc s t [] bs
  | a :: as, b :: bs => (s * a + t * b) :: lc s t as bs

abbrev Constraint := List ℝ × ℝ
abbrev System := List Constraint

def Sat (sys : System) (x : ℕ → ℝ) : Prop := ∀ c ∈ sys, dot c.1 x ≤ c.2

def coef (j : ℕ) (c : Constraint) : ℝ := c.1.getD j 0


def lmax (m : ℝ) (l : List ℝ) : ℝ := l.foldr max m
def lmin (m : ℝ) (l : List ℝ) : ℝ := l.foldr min m

noncomputable def combine (j : ℕ) (P N : Constraint) : Constraint :=
  (lc (-coef j N) (coef j P) P.1 N.1, (-coef j N) * P.2 + coef j P * N.2)

noncomputable def elim (j : ℕ) (sys : System) : System :=
  sys.filter (fun c => decide (coef j c = 0)) ++
    (sys.filter (fun c => decide (0 < coef j c))).flatMap (fun P =>
      (sys.filter (fun c => decide (coef j c < 0))).map (fun N => combine j P N))

noncomputable def resid (j : ℕ) (x : ℕ → ℝ) (c : Constraint) : ℝ :=
  c.2 - dot c.1 x + coef j c * x j

noncomputable def pick (j : ℕ) (sys : System) (x : ℕ → ℝ) : ℝ :=
  match (sys.filter (fun c => decide (coef j c < 0))).map (fun c => resid j x c / coef j c),
        (sys.filter (fun c => decide (0 < coef j c))).map (fun c => resid j x c / coef j c) with
  | l :: ls, _ => lmax l ls
  | [], u :: us => lmin u us
  | [], [] => 0

noncomputable def elimSeq : List ℕ → System → System
  | [], s => s
  | j :: js, s => elimSeq js (elim j s)

noncomputable def stages : List ℕ → System → List (ℕ × System)
  | [], _ => []
  | j :: js, s => (j, s) :: stages js (elim j s)

noncomputable def backSubst : List (ℕ × System) → (ℕ → ℝ) → (ℕ → ℝ)
  | [], p => p
  | (j, s) :: rest, p =>
    let p' := backSubst rest p
    Function.update p' j (pick j s p')

inductive LPResult
  | infeasible
  | unbounded
  | opt (v : ℝ)

def lift (c : List ℝ) (sys : System) : System :=
  (1 :: c.map (fun r => -r), 0) :: sys.map (fun p => (0 :: p.1, p.2))

def nvars (c : List ℝ) (sys : System) : ℕ :=
  (c :: sys.map Prod.fst).foldr (fun a m => max a.length m) 0

def elimOrder (c : List ℝ) (sys : System) : List ℕ := List.range' 1 (nvars c sys)

noncomputable def finalSys (c : List ℝ) (sys : System) : System :=
  elimSeq (elimOrder c sys) (lift c sys)

def zcons (z : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => z
  | i + 1 => x i

noncomputable def bounds (c : List ℝ) (sys : System) : List (ℝ × ℝ) :=
  (finalSys c sys).map (fun p => (p.1.headD 0, p.2))

noncomputable def recover (c : List ℝ) (sys : System) (z : ℝ) : ℕ → ℝ :=
  fun i => backSubst (stages (elimOrder c sys) (lift c sys)) (zcons z (fun _ => 0)) (i + 1)

noncomputable def lpMax (c : List ℝ) (sys : System) : LPResult :=
  let L := bounds c sys
  if L.all (fun p => decide (0 < p.1 ∨ (p.1 = 0 ∧ 0 ≤ p.2))) then
    match (L.filter (fun p => decide (0 < p.1))).map (fun p => p.2 / p.1) with
    | [] => .unbounded
    | u :: us => .opt (lmin u us)
  else .infeasible

noncomputable def argmax (c : List ℝ) (sys : System) : ℕ → ℝ :=
  match lpMax c sys with
  | .opt v => recover c sys v
  | _ => fun _ => 0



def objValues (c : List ℝ) (sys : System) : Set ℝ := {r | ∃ x, Sat sys x ∧ dot c x = r}

end FourierMotzkin


