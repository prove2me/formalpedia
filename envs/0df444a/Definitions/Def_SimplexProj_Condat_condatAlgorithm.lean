-- Prove2me | Definitions.Def_SimplexProj_Condat_condatAlgorithm
-- name    : SimplexProj_Condat_condatAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T23:06:53.013157+00:00
-- url     : https://prove2.me/theorems/34f374f7-b655-40c5-af52-4bf67520b93a
-- title:
--   Condat's Proposed Algorithm for projecting onto the simplex (Fig. 2)
-- statement:
--   Condat's **Proposed Algorithm** (Fig. 2) takes $N \ge 1$, $y = (y_1, \dots, y_N) \in \mathbb{R}^N$ and $a > 0$. It maintains a list $v$, an auxiliary list $\tilde v$ and a real number $\rho$ (lists keep repeated values; "add" appends at the end; $|v|$ is the length of $v$):
--
--   1. Set $v := (y_1)$, $\tilde v$ as an empty list, $\rho := y_1 - a$.
--   2. For $n = 2, \dots, N$: if $y_n > \rho$, then (2.1) set $\rho := \rho + (y_n - \rho)/(|v| + 1)$; (2.2) if $\rho > y_n - a$, add $y_n$ to $v$; (2.3) else, add $v$ to $\tilde v$, set $v := (y_n)$ and $\rho := y_n - a$.
--   3. For every element $y$ of $\tilde v$ (in order): (3.1) if $y > \rho$, add $y$ to $v$ and set $\rho := \rho + (y - \rho)/|v|$.
--   4. Do, while $|v|$ changes: for every element $y$ of $v$ (in order), (4.1) if $y \le \rho$, remove $y$ from $v$ and set $\rho := \rho + (\rho - y)/|v|$.
--   5. Set $\tau := \rho$ and $K := |v|$.
--
--   Step 6 of the paper then sets $x_n := \max\{y_n - \tau, 0\}$; it is not part of this definition but appears in the correctness theorem. The definition returns the pair $(\tau, K)$:
--
--   $$\texttt{condatAlgorithm}\ a\ (y_1, \dots, y_N) = (\tau, K).$$
--
--   **Formalization Note.** The input is the list $(y_1, \dots, y_N)$. In step 2.1, $|v|$ is the length before $y_n$ is added; in step 3.1 it is the length after $y$ is added; in step 4.1 it is the length of the whole current $v$ after the removal (elements already kept in this pass plus those not yet read). Step 4 reads a pass over the list $v$ as it stood at the start of the pass, with $\rho$ updated after each removal; "while $|v|$ changes" is a do-while loop (at least one pass, stop after the first pass that removes nothing), encoded by well-founded recursion on $|v|$, so the function is total with no iteration bound. The empty input ($N = 0$), which the paper excludes, returns the placeholder $(0, 0)$. No guard is added for division by zero: in Lean $t/0 = 0$, and the paper's invariant keeps $|v| \ge 1$ at every division.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 6, Sect. 3, Fig. 2

import Mathlib

namespace SimplexProj.Condat

/-- Step 2 of the Proposed Algorithm (Condat, Fig. 2) on one element `yn`, for `n = 2, …, N`.
The state is `(ṽ, v, ρ)`; lists keep their elements with multiplicity, "add" appends. -/
noncomputable def firstPassStep (a : ℝ) (s : List ℝ × List ℝ × ℝ) (yn : ℝ) :
    List ℝ × List ℝ × ℝ :=
  let vt := s.1
  let v := s.2.1
  let ρ := s.2.2
  if yn > ρ then
    -- 2.1. Set ρ := ρ + (yn − ρ)/(|v| + 1)   (|v| is the size before yn is added)
    let ρ' := ρ + (yn - ρ) / ((v.length : ℝ) + 1)
    -- 2.2. If ρ > yn − a, add yn to v.
    if ρ' > yn - a then (vt, v ++ [yn], ρ')
    -- 2.3. Else, add v to ṽ, set v := (yn), ρ := yn − a.
    else (vt ++ v, [yn], yn - a)
  else (vt, v, ρ)

/-- Step 3.1 of Fig. 2 on one element `y` of `ṽ`; the state is `(v, ρ)`.
If `y > ρ`, add `y` to `v` and set `ρ := ρ + (y − ρ)/|v|` (|v| is the size after adding `y`). -/
noncomputable def cleanupStep (s : List ℝ × ℝ) (y : ℝ) : List ℝ × ℝ :=
  let v := s.1
  let ρ := s.2
  if y > ρ then
    let v' := v ++ [y]
    (v', ρ + (y - ρ) / (v'.length : ℝ))
  else (v, ρ)

/-- One pass of step 4 of Fig. 2 ("for every element y of v, do 4.1"), reading the elements
`ys` of `v` in order. `c` is the current size `|v|` of the whole list `v` (the elements kept so
far plus those not yet read). Step 4.1: if `y ≤ ρ`, remove `y` from `v` and set
`ρ := ρ + (ρ − y)/|v|`, where `|v| = c − 1` is the size after the removal. Returns the list of
kept elements (in their order) and the final `ρ`. -/
noncomputable def removalPass : List ℝ → ℕ → ℝ → List ℝ × ℝ
  | [], _, ρ => ([], ρ)
  | y :: ys, c, ρ =>
    if y ≤ ρ then
      removalPass ys (c - 1) (ρ + (ρ - y) / ((c - 1 : ℕ) : ℝ))
    else
      let r := removalPass ys c ρ
      (y :: r.1, r.2)

/-- Structural: a pass of step 4 never lengthens `v`. -/
theorem removalPass_length_le (ys : List ℝ) (c : ℕ) (ρ : ℝ) :
    (removalPass ys c ρ).1.length ≤ ys.length := by
  induction ys generalizing c ρ with
  | nil => simp [removalPass]
  | cons y ys ih =>
    unfold removalPass
    split_ifs
    · exact (ih _ _).trans (Nat.le_succ _)
    · simpa using ih c ρ

/-- Step 4 of Fig. 2: "Do, while |v| changes, [a pass]". At least one pass is made; the loop
stops after the first pass that leaves `|v|` unchanged. Returns the final `(v, ρ)`. -/
noncomputable def removalLoop (v : List ℝ) (ρ : ℝ) : List ℝ × ℝ :=
  let r := removalPass v v.length ρ
  if r.1.length = v.length then r
  else removalLoop r.1 r.2
termination_by v.length
decreasing_by exact lt_of_le_of_ne (removalPass_length_le _ _ _) ‹_›

/-- The Proposed Algorithm of Condat, Fig. 2 (Sect. 3, p. 6), run on the list
`(y₁, …, y_N)` with radius `a`; it returns `(τ, K)` of step 5. Step 6, `x_n := max{y_n − τ, 0}`,
is applied by the caller. The empty list (`N = 0`) is outside the paper (`N ≥ 1`) and gets the
placeholder value `(0, 0)`. -/
noncomputable def condatAlgorithm (a : ℝ) : List ℝ → ℝ × ℕ
  | [] => (0, 0)
  | y1 :: ys =>
    -- 1. Set v := (y1), ṽ as an empty list, ρ := y1 − a.   2. For n = 2, …, N, do …
    let s2 := ys.foldl (firstPassStep a) ([], [y1], y1 - a)
    -- 3. If ṽ is not empty, for every element y of ṽ, do 3.1.
    let s3 := s2.1.foldl cleanupStep (s2.2.1, s2.2.2)
    -- 4. Do, while |v| changes, …
    let s4 := removalLoop s3.1 s3.2
    -- 5. Set τ := ρ, K = |v|.
    (s4.2, s4.1.length)

end SimplexProj.Condat


