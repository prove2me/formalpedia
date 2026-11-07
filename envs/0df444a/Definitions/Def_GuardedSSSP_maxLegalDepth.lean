-- Prove2me | Definitions.Def_GuardedSSSP_maxLegalDepth
-- name    : GuardedSSSP_maxLegalDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:03.142659+00:00
-- url     : https://prove2.me/theorems/1ee6c299-7f5c-40fa-b8e8-2fac5160d276
-- title:
--   Algorithm 2, $\mathrm{MaxLegalDepth}(x)$, instrumented
-- statement:
--   For an integer scale $x$ and base threshold $T_4$, Algorithm 2 runs as follows. If $x<T_4$ it returns Small. Otherwise it sets $L\leftarrow\lfloor\log_2x\rfloor$, $u\leftarrow T_4$, $d\leftarrow3$, and while $u<x$ it sets $a\leftarrow u+1$, stops if $a>\lfloor\lfloor L/64\rfloor/a\rfloor$, and otherwise sets $e\leftarrow64a^2$, $u\leftarrow2^e$, $d\leftarrow d+1$. At the end it returns Small if $d<4$ and $d$ otherwise.
--
--   The instrumented procedure returns three things:
--
--   1. the result (Small or $d$);
--   2. the number of threshold tests, i.e. executions of the guard $a>\lfloor\lfloor L/64\rfloor/a\rfloor$;
--   3. the largest integer it materializes other than its fixed code constants $T_4,3,4,64$.
--
--   The procedure selects the generation $D_*(x)$ without ever writing down a threshold larger than $x$.
--
--   **Formalization Note** The loop is written by well-founded recursion on $x-u$ and keeps the fixed state $(L,u,d)$ and two counters. $\lfloor\log_2x\rfloor$ is `Nat.log 2 x`.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §8.1, Algorithm 2, p.17 (PDF p.18)

import Mathlib

namespace GuardedSSSP

/-!
# Algorithm 2, `MaxLegalDepth(x)`, instrumented

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §8.1, Algorithm 2, p.17 (PDF p.18):

```
1: if x < T₄ then return Small
4: L ← ⌊log₂ x⌋, u ← T₄, d ← 3
5: while u < x do
6:   a ← u + 1
7:   if a > ⌊⌊L/64⌋/a⌋ then break
10:  e ← 64a², u ← 2^e, d ← d + 1
11: end while
12: if d < 4 then return Small
15: return d
```

`maxLegalDepth T4 x` follows the listing line by line and returns a triple:
1. the result, `none` for `Small` and `some d` for `d`;
2. the number of threshold tests, i.e. executions of the guard on line 7;
3. the largest integer the procedure materializes other than its fixed code constants (`T₄`, `3`, `4`,
   `64`): every value assigned to `L`, `a`, `⌊L/64⌋`, `⌊⌊L/64⌋/a⌋`, `a²`, `e = 64a²`, `u = 2^e` and the
   incremented `d`, or `0` if none is assigned.

**Formalization Note.** The live state is the fixed tuple `(L, u, d)` plus the two counters, which is the
paper's "O(1) live scalar metadata". The loop is written by well-founded recursion on `x − u`: a
successful step replaces `u` by `2^{64(u+1)²} > u`. `⌊log₂ x⌋` is `Nat.log 2 x`.
-/

/-- The `while` loop of Algorithm 2 (lines 5–11) from the state `(u, d)`, with `tests` guard tests made
and largest materialized value `mx` so far. Returns `(d, tests, mx)` at loop exit. -/
def mldLoop (x L : ℕ) (u d tests mx : ℕ) : ℕ × ℕ × ℕ :=
  if u < x then
    let a := u + 1
    let q1 := L / 64
    let q2 := q1 / a
    let mx1 := max mx (max a (max q1 q2))
    if q2 < a then (d, tests + 1, mx1)
    else
      let a2 := a * a
      let e := 64 * a2
      mldLoop x L (2 ^ e) (d + 1) (tests + 1) (max mx1 (max a2 (max e (max (2 ^ e) (d + 1)))))
  else (d, tests, mx)
termination_by x - u
decreasing_by
  have h1 : u < 2 ^ u := Nat.lt_two_pow_self
  have h2 : 2 ^ u ≤ 2 ^ (64 * ((u + 1) * (u + 1))) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

/-- `MaxLegalDepth(x)` (Algorithm 2) with base threshold `T4`: `(result, threshold tests, largest
materialized integer)`, where `result = none` is `Small`. -/
def maxLegalDepth (T4 x : ℕ) : Option ℕ × ℕ × ℕ :=
  if x < T4 then (none, 0, 0)
  else
    let L := Nat.log 2 x
    let r := mldLoop x L T4 3 0 L
    if r.1 < 4 then (none, r.2.1, r.2.2) else (some r.1, r.2.1, r.2.2)

end GuardedSSSP


