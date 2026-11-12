-- Prove2me | Definitions.Def_PQNormIPM1352_Main_Algorithm1
-- name    : PQNormIPM1352_Main_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:27.87921+00:00
-- url     : https://prove2.me/theorems/2df69316-01de-4fb7-8fd5-650901ad665a
-- title:
--   Algorithm 1 (pqNormIPM), preprocessing, the $q=1$ closed form and the full algorithm of Theorem 1
-- statement:
--   The full algorithm of Theorem 1, written as a program of the cost model, on the list of non-zero entries $(i,j,A(i,j))$ and real parameters $p \ge q \ge 1$, $\varepsilon > 0$:
--
--   1. If the list is empty ($A = 0$), return $0$.
--   2. **Preprocessing** (Step 2 of Algorithm 1): relabel the rows and columns that occur to $0,1,\dots$ (sort the entries by row and by column with a charged merge sort, then scan), which removes all-zero rows and columns.
--   3. If $q = 1$ (tested as $q \le 1$), return the closed form $\|A\|_{p\to1} = \|A^\top\mathbf 1\|_{p^*}$ (proof of Theorem 1): with column sums $w(j)$, $\max_j w(j)$ if $p = 1$ and $(\sum_j w(j)^{p^*})^{1/p^*}$ if $p > 1$.
--   4. Otherwise run **Algorithm 1 (pqNormIPM)**: $A_{\max} = \max_S A(i,j)$, $A' = A/A_{\max}$; $\delta = 1/6$; $\nu = 3s+2$; $\eta_0 = \sqrt2/(10\sqrt s)$; $T = \max(\lceil 100\sqrt s\log(s/\varepsilon)\rceil, \lceil 21\sqrt\nu\log(7\nu/(6\varepsilon\eta_0))\rceil)$ by two counting loops; $x_0$ by Steps 5–6 (degrees and the analytic center of Lemma 7, program `initProg`); then $T$ times $x \leftarrow x + \mathrm{NewtonSolve}(A', \delta, x, \eta)$ and $\eta \leftarrow (1 + 1/(20\sqrt{3s+2}))\eta$; finally $u = (y_T/Y_T)^{1/p}$ and the returned value is $\|Au\|_q/\|u\|_p$.
--
--   The value $\|Au\|_q/\|u\|_p$ of the vector $u$ of Step 12 is the approximation of $\|A\|_{p\to q}$ that Theorem 1 asserts.
--
--   **Formalization Note** Algorithm 1 as printed returns the vector $u$; the program returns the value $\|Au\|_q/\|u\|_p$, computed from $u$ in $O(s)$ operations. For $A = 0$ it returns $0 = \|A\|_{p\to q}$ directly, instead of writing the vector $n^{-1/p}\mathbf 1_n$ of Step 1, which would cost $\Theta(n)$. The second term of $T$ is the reading of footnote 4 explained in the barrier definition. Reading and sorting the input costs $O(s\log s)$, and nothing is charged for the dimensions $m, n$.
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Algorithm 1, p. 9; §4.1, p. 9; proof of Theorem 1, p. 19

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_NewtonSolve

/-!
# Algorithm 1 (`pqNormIPM`), its preprocessing, the `q = 1` closed form, and the full algorithm

Pirazzini–Spielman, STOC 2027 submission #1352, Algorithm 1 (p. 9), §4.1 (p. 9), and the proof of
Theorem 1 (p. 19: for `q = 1`, `‖A‖_{p→1} = ‖Aᵀ1‖_{p*}`, computed exactly).

All programs are written in the cost model of `Def_PQNormIPM1352_Main_Prog` for an abstract real
carrier `R`. Index bookkeeping (sorting, relabelling) is done by explicit charged loops and a
charged merge sort, so reading and preprocessing the input costs `O(s log s)` and nothing is
charged for the dimensions `m, n` themselves.
-/

namespace PQNormIPM1352.Main

open Prog

variable {R : Type}

local notation "v" => Ex.var

/-- Merge two lists of pairs sorted by their first component; one charged unit per comparison. -/
def mergeKeys : List (ℕ × ℕ) → List (ℕ × ℕ) → Prog R (List (ℕ × ℕ))
  | [], ys => ret ys
  | x :: xs, [] => ret (x :: xs)
  | x :: xs, y :: ys =>
      Prog.bind step fun _ =>
        if x.1 ≤ y.1 then Prog.bind (mergeKeys xs (y :: ys)) fun l => ret (x :: l)
        else Prog.bind (mergeKeys (x :: xs) ys) fun l => ret (y :: l)
termination_by xs ys => xs.length + ys.length

/-- Merge sort by first component; splitting a list of length `ℓ` is charged `ℓ` units. -/
def sortKeys (l : List (ℕ × ℕ)) : Prog R (List (ℕ × ℕ)) :=
  if h : l.length ≤ 1 then ret l
  else
    Prog.bind (forLoop l.length () fun _ _ => ret ()) fun _ =>
    Prog.bind (sortKeys (l.take (l.length / 2))) fun l₁ =>
    Prog.bind (sortKeys (l.drop (l.length / 2))) fun l₂ =>
    mergeKeys l₁ l₂
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-- Compact relabelling: given the pairs `(key, k)` sorted by key, assign to each `k` the rank of
its key among the distinct keys (`0, 1, …`); returns the number of distinct keys and the label
array. One charged unit per pair. -/
def relabel (sorted : List (ℕ × ℕ)) : Prog R (ℕ × (ℕ → ℕ)) :=
  Prog.bind (forLoop sorted.length ((none : Option ℕ), 0, (fun _ => 0 : ℕ → ℕ)) fun t st =>
      let e := sorted.getD t (0, 0)
      match st.1 with
      | none => ret (some e.1, 1, Function.update st.2.2 e.2 0)
      | some prev =>
          if e.1 = prev then ret (some prev, st.2.1, Function.update st.2.2 e.2 (st.2.1 - 1))
          else ret (some e.1, st.2.1 + 1, Function.update st.2.2 e.2 st.2.1)) fun st =>
  ret (st.2.1, st.2.2)

/-- The preprocessed instance handed to the main loop (Step 2 of Algorithm 1). -/
structure PreInst (R : Type) where
  m : ℕ
  n : ℕ
  s : ℕ
  row : ℕ → ℕ
  col : ℕ → ℕ
  a : ℕ → R

/-- Step 2 of Algorithm 1: from the entry list `(i, j, A(i,j))`, remove all-zero rows and columns
by relabelling the rows and the columns that occur to `0, 1, …` (sort, then scan). `a₀` is a
default value for out-of-range reads. -/
def preprocess (entries : List (ℕ × ℕ × R)) (a₀ : R) : Prog R (PreInst R) :=
  Prog.bind (forLoop entries.length ([] : List (ℕ × ℕ)) fun k acc =>
      ret (acc ++ [((entries.getD k (0, 0, a₀)).1, k)])) fun rk =>
  Prog.bind (forLoop entries.length ([] : List (ℕ × ℕ)) fun k acc =>
      ret (acc ++ [((entries.getD k (0, 0, a₀)).2.1, k)])) fun ck =>
  Prog.bind (forLoop entries.length (fun _ => a₀) fun k f =>
      ret (upd f k (entries.getD k (0, 0, a₀)).2.2)) fun a =>
  Prog.bind (sortKeys rk) fun rs =>
  Prog.bind (sortKeys ck) fun cs =>
  Prog.bind (relabel rs) fun rl =>
  Prog.bind (relabel cs) fun cl =>
  ret ⟨rl.1, cl.1, entries.length, rl.2, cl.2, a⟩

/-- Steps 5–6 of Algorithm 1 (Lemma 7): the degrees `dᵢ`, `eⱼ` and the analytic center
`z₀(i) = (1 + 1/q*) dᵢ / (1 + (1 + 1/q*) s)`, `y₀(j) = (1 + 1/p) eⱼ / (1 + (1 + 1/p) s)`, `γ₀ = 0`,
returned as an array of length `m + n + s`. -/
def initProg (m n s : ℕ) (row col : ℕ → ℕ) (p q : R) : Prog R (ℕ → R) :=
  Prog.bind (cst 0) fun zero =>
  Prog.bind (forLoop s zero fun _ acc => (v acc + 1).eval) fun sR =>
  Prog.bind (v q / (v q - 1)).eval fun qs =>
  Prog.bind (forLoop s ((fun _ => zero : ℕ → R), (fun _ => zero : ℕ → R)) fun k st =>
    Prog.bind (v (st.1 (row k)) + 1).eval fun dz =>
    Prog.bind (v (st.2 (col k)) + 1).eval fun dy =>
    ret (upd st.1 (row k) dz, upd st.2 (col k) dy)) fun deg =>
  Prog.bind (forLoop m (fun _ => zero) fun i f =>
    Prog.bind ((1 + 1 / v qs) * v (deg.1 i) / (1 + (1 + 1 / v qs) * v sR)).eval fun t =>
      ret (upd f i t)) fun x₁ =>
  Prog.bind (forLoop n x₁ fun j f =>
    Prog.bind ((1 + 1 / v p) * v (deg.2 j) / (1 + (1 + 1 / v p) * v sR)).eval fun t =>
      ret (upd f (m + j) t)) fun x₂ =>
  forLoop s x₂ fun k f => ret (upd f (m + n + k) zero)

/-- Algorithm 1 (`pqNormIPM`, p. 9) on a preprocessed instance with `s ≥ 1`, `p ≥ q > 1`, `ε > 0`,
returning the value `‖Au‖_q / ‖u‖_p` of the returned vector `u`:
3. `A_max = max_S A(i,j)`, `A' = A / A_max`;
4. `δ = 1/6`, `T = max(⌈100 √s log(s/ε)⌉, ⌈21 √ν log(7ν/(6 ε η₀))⌉)`, `ν = 3s + 2` (the printed
   `T` is the first term; the second is the reading of footnote 4, see `iterCount`);
5.–6. `x₀` by `initProg`, `η₀ = √2 / (10 √s)`;
7.–10. `T` times: `x ← x + NewtonSolve(A', δ, x, η)`, `η ← (1 + 1/(20 √(3s+2))) η`;
11.–12. `Y_T = ∑ y_T(j)`, `u = (y_T / Y_T)^{1/p}`; the output is `‖Au‖_q / ‖u‖_p` (entries of
`u` and `Au` are non-negative). -/
def pqNormIPM (I : PreInst R) (p q ε : R) : Prog R R :=
  Prog.bind (cst 0) fun zero =>
  -- Step 3
  Prog.bind (forLoop I.s (I.a 0) fun k acc =>
    Prog.bind (leq acc (I.a k)) fun b => ret (if b then I.a k else acc)) fun amax =>
  Prog.bind (forLoop I.s (fun _ => zero) fun k f =>
    Prog.bind (v (I.a k) / v amax).eval fun t => ret (upd f k t)) fun a' =>
  -- Step 4
  Prog.bind (cst (1 / 6)) fun δ =>
  Prog.bind (forLoop I.s zero fun _ acc => (v acc + 1).eval) fun sR =>
  Prog.bind (3 * v sR + 2).eval fun ν =>
  Prog.bind (2 ^ (Ex.lit (1 / 2) : Ex R) / (10 * v sR ^ (Ex.lit (1 / 2) : Ex R))).eval fun η₀ =>
  Prog.bind (100 * v sR ^ (Ex.lit (1 / 2) : Ex R) * Ex.log (v sR / v ε)).eval fun T₁x =>
  Prog.bind (countUp T₁x) fun T₁ =>
  Prog.bind (21 * v ν ^ (Ex.lit (1 / 2) : Ex R) * Ex.log (7 * v ν / (6 * v ε * v η₀))).eval fun T₂x =>
  Prog.bind (countUp T₂x) fun T₂ =>
  Prog.bind step fun _ =>
  -- Steps 5–6
  Prog.bind (initProg I.m I.n I.s I.row I.col p q) fun x₀ =>
  Prog.bind (1 + 1 / (20 * v ν ^ (Ex.lit (1 / 2) : Ex R))).eval fun growth =>
  -- Steps 7–10
  Prog.bind (forLoop (max T₁ T₂) (x₀, η₀) fun _ st =>
    Prog.bind (newtonSolve I.m I.n I.s I.row I.col a' p q δ st.2 st.1) fun Δ =>
    Prog.bind (forLoop (I.m + I.n + I.s) st.1 fun i f =>
      Prog.bind (v (st.1 i) + v (Δ i)).eval fun t => ret (upd f i t)) fun x' =>
    Prog.bind (v growth * v st.2).eval fun η' => ret (x', η')) fun fin =>
  -- Steps 11–12
  Prog.bind (forLoop I.n zero fun j acc => (v acc + v (fin.1 (I.m + j))).eval) fun YT =>
  Prog.bind (forLoop I.n (fun _ => zero) fun j f =>
    Prog.bind ((v (fin.1 (I.m + j)) / v YT) ^ (1 / v p)).eval fun t => ret (upd f j t)) fun u =>
  -- the value `‖Au‖_q / ‖u‖_p` (with the original entries of `A`)
  Prog.bind (forLoop I.s (fun _ => zero) fun k f =>
    Prog.bind (v (f (I.row k)) + v (I.a k) * v (u (I.col k))).eval fun t =>
      ret (upd f (I.row k) t)) fun Au =>
  Prog.bind (forLoop I.m zero fun i acc => (v acc + v (Au i) ^ v q).eval) fun sAu =>
  Prog.bind (forLoop I.n zero fun j acc => (v acc + v (u j) ^ v p).eval) fun su =>
  (v sAu ^ (1 / v q) / v su ^ (1 / v p)).eval

/-- The `q = 1` branch (proof of Theorem 1, p. 19): `‖A‖_{p→1} = ‖Aᵀ 1‖_{p*}`. With column sums
`w(j) = ∑ᵢ A(i,j)`, return `max_j w(j)` if `p = 1` (`p* = ∞`), and `(∑ⱼ w(j)^{p*})^{1/p*}` with
`p* = p/(p−1)` if `p > 1`. -/
def closedFormQ1 (I : PreInst R) (p : R) : Prog R R :=
  Prog.bind (cst 0) fun zero =>
  Prog.bind (forLoop I.s (fun _ => zero) fun k f =>
    Prog.bind (v (f (I.col k)) + v (I.a k)).eval fun t => ret (upd f (I.col k) t)) fun w =>
  Prog.bind (cst 1) fun one =>
  Prog.bind (leq p one) fun pIsOne =>
  if pIsOne then
    forLoop I.n zero fun j acc =>
      Prog.bind (leq acc (w j)) fun b => ret (if b then w j else acc)
  else
    Prog.bind (v p / (v p - 1)).eval fun ps =>
    Prog.bind (forLoop I.n zero fun j acc => (v acc + v (w j) ^ v ps).eval) fun t =>
    (v t ^ (1 / v ps)).eval

/-- The full algorithm of Theorem 1 on the sparse input `(i, j, A(i,j))` (all listed values
positive), exponents `p ≥ q ≥ 1` and accuracy `ε > 0`: if `A = 0` (empty list) return `0`;
otherwise preprocess (Step 2), and return the exact closed form if `q = 1` (tested as `q ≤ 1`,
given `q ≥ 1`) and Algorithm 1's value `‖Au‖_q / ‖u‖_p` if `q > 1`. -/
def pqNorm (entries : List (ℕ × ℕ × R)) (p q ε : R) : Prog R R :=
  match entries with
  | [] => Prog.bind step fun _ => cst 0
  | e₀ :: rest =>
      Prog.bind (preprocess (e₀ :: rest) e₀.2.2) fun I =>
      Prog.bind (cst 1) fun one =>
      Prog.bind (leq q one) fun qIsOne =>
      if qIsOne then closedFormQ1 I p else pqNormIPM I p q ε

end PQNormIPM1352.Main


