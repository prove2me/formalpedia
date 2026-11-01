-- Prove2me | Definitions.Def_CleveDiVincenzo_Schumacher_finalProg
-- name    : CleveDiVincenzo_Schumacher_finalProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:23.649641+00:00
-- url     : https://prove2.me/theorems/c9021b00-fcfc-4f8a-9676-7f4218502ace
-- title:
--   The programs TRY_INVERSE, FINAL_SCHUMACHER_INVERSE and FINAL_SCHUMACHER (restore loop corrected)
-- statement:
--   A program is a straight-line list of statements on integer registers, run from an initial state by executing the statements in order; its classical `for` loops (both ends included) are unrolled, one list element per pseudocode line. The three programs of the paper, with $\binom ab$ the binomial coefficient ($\binom ab=0$ for $b>a$):
--
--   **TRY_INVERSE** (p.16), on registers $(X,Y,S)$:
--   ```
--   for m = 0 to n do
--       Y ← Y − C(n,m)
--       if Y ≥ 0 then S ← S + 1
--   for m = 0 to n do
--       if S ≤ m then Y ← Y + C(n,m)
--   for p = 0 to n − 1 do
--       for i = 0 to n − p do
--           if S = i and Y ≥ C(n−p−1, i) then X_{n−p−1} ← X_{n−p−1} ⊕ 1
--           if S = i and X_{n−p−1} = 1 then Y ← Y − C(n−p−1, i)
--       if X_{n−p−1} = 1 then S ← S − 1
--   ```
--
--   **FINAL_SCHUMACHER_INVERSE** (p.18), on registers $(X,S)$: the same program with $Y$ merged into $X$,
--   ```
--   for m = 0 to n do
--       X ← X − C(n,m)
--       if X ≥ 0 then S ← S + 1
--   for m = 0 to n do
--       if S ≤ m then X ← X + C(n,m)
--   for p = 0 to n − 1 do
--       for i = 0 to n − p do
--           if S = i and TRUNC_{n−p−1}(X) ≥ C(n−p−1, i) then X_{n−p−1} ← X_{n−p−1} ⊕ 1
--           if S = i and X_{n−p−1} = 1 then X ← X − C(n−p−1, i)
--       if X_{n−p−1} = 1 then S ← S − 1
--   ```
--
--   **FINAL_SCHUMACHER** (p.19), on registers $(X,S)$, its time-reverse:
--   ```
--   for p = n − 1 down to 0 do
--       if X_{n−p−1} = 1 then S ← S + 1
--       for i = n − p down to 0 do
--           if S = i and X_{n−p−1} = 1 then X ← X + C(n−p−1, i)
--           if S = i and TRUNC_{n−p−1}(X) ≥ C(n−p−1, i) then X_{n−p−1} ← X_{n−p−1} ⊕ 1
--   for m = n down to 0 do
--       if S ≤ m then X ← X − C(n,m)
--   for m = n down to 0 do
--       if X ≥ 0 then S ← S − 1
--       X ← X + C(n,m)
--   ```
--
--   These are the paper's reversible programs for Schumacher's coding function and its inverse; the mission's goal is that they compute $f$ and $f^{-1}$ in place.
--
--   **Formalization Note** The restore loop is printed with `if S ≥ m` in all three programs; it is corrected to `if S ≤ m`. After the counting loop, $S$ is the weight $m$ and the data register holds $y-\sum_{i=0}^{n}\binom ni$; the restore loop must add back $\binom ni$ for $i\ge S$ to leave $I[x,n,m]$, as the text says (p.17). With the printed condition the programs fail already for $n=1$, $y=0$. Registers are integers ($S$'s printed $\lceil\log n\rceil$-bit width cannot hold $S=n$ and is dropped); bits, flips and $\mathrm{TRUNC}_j$ are those of the `trunc` definition. Everything else, loop bounds and statement order included, is as printed.
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III C: TRY INVERSE p.16, FINAL SCHUMACHER INVERSE p.18, FINAL SCHUMACHER p.19; pseudocode conventions §III A, pp.10–11; unrolling of loops p.20

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_trunc

namespace CleveDiVincenzo.Schumacher

/-- The register state `(X, S)` of FINAL_SCHUMACHER_INVERSE and FINAL_SCHUMACHER (Cleve,
DiVincenzo, *Schumacher's quantum data compression as a quantum computation*,
arXiv:quant-ph/9603009v1, §III C, pp.18–19).

**Formalization Note** Both registers are integers (arithmetic registers of the high-level
pseudocode, p.11). The paper declares `X` an `n`-bit signed register and `S` a `⌈log n⌉`-bit
register; `S` reaches the weight `m ≤ n`, which `⌈log n⌉` bits cannot hold (for `n = 1`, `0`
bits cannot hold `S = 1`), so the printed widths are dropped. A basis state of the quantum
registers is a pair of integers; the unitary of a classical reversible program is its
permutation of basis states (p.7, p.33). -/
abbrev State := ℤ × ℤ

/-- The register state `(X, Y, S)` of TRY_INVERSE (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1,
§III C, p.16). All three registers are integers (see `State`). -/
abbrev TState := ℤ × ℤ × ℤ

/-- Run a straight-line program, given as the list of its statements in execution order, from
the initial state `s`.

**Formalization Note** The paper's pseudocode (§III A, pp.10–11) has only classical `for` loops
over constant ranges and conditional assignments. A program is unrolled ("the first step … is
to 'unravel' the for loops", p.20) into the list of its statements: each pseudocode line (one
assignment, or one `if … then …`) is one list element, and `for a = s to t` / `for a = t down
to s` include both ends. -/
def run {σ : Type} (prog : List (σ → σ)) (s : σ) : σ :=
  prog.foldl (fun s g => g s) s

/-- **Program TRY_INVERSE** (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §III C, p.16), on the
registers `(X, Y, S)`, with the restore loop corrected:

```
for m = 0 to n do
    Y ← Y − C(n,m)
    if Y ≥ 0 then S ← S + 1
for m = 0 to n do
    if S ≤ m then Y ← Y + C(n,m)          -- printed: if S ≥ m
for p = 0 to n − 1 do
    for i = 0 to n − p do
        if S = i and Y ≥ C(n−p−1, i) then X_{n−p−1} ← X_{n−p−1} ⊕ 1
        if S = i and X_{n−p−1} = 1 then Y ← Y − C(n−p−1, i)
    if X_{n−p−1} = 1 then S ← S − 1
```

**Formalization Note** Correction: the second loop is printed with `if S ≥ m`. After the first
loop `S = m` (the weight of `x`) and `Y = y − Σ_{i=0}^{n} C(n,i)`; the text requires that "at
the end of the second loop, `Y` has the desired value of `I[x, n, m]`" (p.17), i.e. the loop
adds back `C(n,i)` for `i ≥ S`, which is `if S ≤ m`. With the printed condition the program
fails already for `n = 1`, `y = 0`. In `for p = 0 to n − 1`, `p ≤ n − 1`, so the natural-number
subtraction `n - p - 1` is the paper's `n − p − 1`. -/
def tryInverseProg (n : ℕ) : List (TState → TState) :=
  let mLoopCount : List (TState → TState) :=
    (List.range (n + 1)).flatMap fun (m : ℕ) =>
      [fun ((X, Y, S) : TState) => (X, Y - (n.choose m : ℤ), S),
       fun ((X, Y, S) : TState) => if Y ≥ 0 then (X, Y, S + 1) else (X, Y, S)]
  let mLoopRestore : List (TState → TState) :=
    (List.range (n + 1)).map fun (m : ℕ) =>
      fun ((X, Y, S) : TState) => if S ≤ (m : ℤ) then (X, Y + (n.choose m : ℤ), S) else (X, Y, S)
  let pLoop : List (TState → TState) :=
    (List.range n).flatMap fun (p : ℕ) =>
      ((List.range (n - p + 1)).flatMap fun (i : ℕ) =>
        [fun ((X, Y, S) : TState) =>
            if S = (i : ℤ) ∧ Y ≥ ((n - p - 1).choose i : ℤ) then (flip (n - p - 1) X, Y, S)
            else (X, Y, S),
         fun ((X, Y, S) : TState) =>
            if S = (i : ℤ) ∧ bit (n - p - 1) X = true then (X, Y - ((n - p - 1).choose i : ℤ), S)
            else (X, Y, S)]) ++
      [fun ((X, Y, S) : TState) => if bit (n - p - 1) X = true then (X, Y, S - 1) else (X, Y, S)]
  mLoopCount ++ mLoopRestore ++ pLoop

/-- **Program FINAL_SCHUMACHER_INVERSE** (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §III C,
p.18), on the registers `(X, S)`, with the restore loop corrected:

```
for m = 0 to n do
    X ← X − C(n,m)
    if X ≥ 0 then S ← S + 1
for m = 0 to n do
    if S ≤ m then X ← X + C(n,m)          -- printed: if S ≥ m
for p = 0 to n − 1 do
    for i = 0 to n − p do
        if S = i and TRUNC_{n−p−1}(X) ≥ C(n−p−1, i) then X_{n−p−1} ← X_{n−p−1} ⊕ 1
        if S = i and X_{n−p−1} = 1 then X ← X − C(n−p−1, i)
    if X_{n−p−1} = 1 then S ← S − 1
```

**Formalization Note** The same correction as in `tryInverseProg` (printed `if S ≥ m`). The
comparison uses `TRUNC_{n−p−1}(X) = X mod 2^{n−p−1}` (`trunc`), also in the final pass
`p = n − 1`, where `TRUNC_0(X) = 0`. -/
def finalInverseProg (n : ℕ) : List (State → State) :=
  let mLoopCount : List (State → State) :=
    (List.range (n + 1)).flatMap fun (m : ℕ) =>
      [fun ((X, S) : State) => (X - (n.choose m : ℤ), S),
       fun ((X, S) : State) => if X ≥ 0 then (X, S + 1) else (X, S)]
  let mLoopRestore : List (State → State) :=
    (List.range (n + 1)).map fun (m : ℕ) =>
      fun ((X, S) : State) => if S ≤ (m : ℤ) then (X + (n.choose m : ℤ), S) else (X, S)
  let pLoop : List (State → State) :=
    (List.range n).flatMap fun (p : ℕ) =>
      ((List.range (n - p + 1)).flatMap fun (i : ℕ) =>
        [fun ((X, S) : State) =>
            if S = (i : ℤ) ∧ trunc (n - p - 1) X ≥ ((n - p - 1).choose i : ℤ) then
              (flip (n - p - 1) X, S)
            else (X, S),
         fun ((X, S) : State) =>
            if S = (i : ℤ) ∧ bit (n - p - 1) X = true then (X - ((n - p - 1).choose i : ℤ), S)
            else (X, S)]) ++
      [fun ((X, S) : State) => if bit (n - p - 1) X = true then (X, S - 1) else (X, S)]
  mLoopCount ++ mLoopRestore ++ pLoop

/-- **Program FINAL_SCHUMACHER** (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §III C, p.19),
"literally just the time-reverse" of FINAL_SCHUMACHER_INVERSE, on the registers `(X, S)`, with
the restore loop corrected:

```
for p = n − 1 down to 0 do
    if X_{n−p−1} = 1 then S ← S + 1
    for i = n − p down to 0 do
        if S = i and X_{n−p−1} = 1 then X ← X + C(n−p−1, i)
        if S = i and TRUNC_{n−p−1}(X) ≥ C(n−p−1, i) then X_{n−p−1} ← X_{n−p−1} ⊕ 1
for m = n down to 0 do
    if S ≤ m then X ← X − C(n,m)          -- printed: if S ≥ m
for m = n down to 0 do
    if X ≥ 0 then S ← S − 1
    X ← X + C(n,m)
```

**Formalization Note** The same correction as in `finalInverseProg` (printed `if S ≥ m`).
`for a = t down to s` runs `a = t, t − 1, …, s`, i.e. `(List.range (t + 1)).reverse` for
`s = 0`; for `n = 0` the `p`-loop is empty. The statement order inside each loop body is the
printed one. -/
def finalProg (n : ℕ) : List (State → State) :=
  let pLoop : List (State → State) :=
    (List.range n).reverse.flatMap fun (p : ℕ) =>
      (fun ((X, S) : State) => if bit (n - p - 1) X = true then (X, S + 1) else (X, S)) ::
      (List.range (n - p + 1)).reverse.flatMap fun (i : ℕ) =>
        [fun ((X, S) : State) =>
            if S = (i : ℤ) ∧ bit (n - p - 1) X = true then (X + ((n - p - 1).choose i : ℤ), S)
            else (X, S),
         fun ((X, S) : State) =>
            if S = (i : ℤ) ∧ trunc (n - p - 1) X ≥ ((n - p - 1).choose i : ℤ) then
              (flip (n - p - 1) X, S)
            else (X, S)]
  let mLoopRestore : List (State → State) :=
    (List.range (n + 1)).reverse.map fun (m : ℕ) =>
      fun ((X, S) : State) => if S ≤ (m : ℤ) then (X - (n.choose m : ℤ), S) else (X, S)
  let mLoopCount : List (State → State) :=
    (List.range (n + 1)).reverse.flatMap fun (m : ℕ) =>
      [fun ((X, S) : State) => if X ≥ 0 then (X, S - 1) else (X, S),
       fun ((X, S) : State) => (X + (n.choose m : ℤ), S)]
  pLoop ++ mLoopRestore ++ mLoopCount

end CleveDiVincenzo.Schumacher


