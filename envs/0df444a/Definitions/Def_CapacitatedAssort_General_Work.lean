-- Prove2me | Definitions.Def_CapacitatedAssort_General_Work
-- name    : CapacitatedAssort_General_Work
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:19.046313+00:00
-- url     : https://prove2.me/theorems/b331d5f1-48a3-4cf7-9914-cd3367018ef9
-- title:
--   Counted real-arithmetic operations, finite arrays and witness traceback
-- statement:
--   An instrumented computation returns a value and a natural operation count, accumulated by a state monad starting at zero. Scalar arithmetic, comparisons, integer rounding, random-access array reads and writes, amortized array pushes, persistent-list cons, and one objective value-oracle call are unit operations. Fixed instruction blocks are charged the number of operations specified at their execution sites; this is a real-RAM/oracle convention, not a bit-complexity model.
--
--   The generic utilities tabulate an array by a finite loop with separately counted callbacks, traverse a persistent witness list, compute the size of a rectangular integer box, and encode or decode mixed-radix addresses with coordinate zero least significant. Enumeration charges include index construction, tests and increments. Decode and encode explicitly traverse every coordinate; array access is not an uncounted search. Empty arrays and lists have their specified base costs. These total utilities allow zero radices, where natural division/remainder follow Lean's defaults; the assortment algorithm only constructs positive radices. This module supplies no optimization guarantee or asymptotic cost assumption.
-- source:
--   Désir, Goyal and Zhang (2021), Technical Note—Capacitated Assortment Optimization: Hardness and Approximation, https://doi.org/10.1287/opre.2021.2142, held source.pdf, Algorithm 1 and runtime discussion, PDF/printed pp. 12–14; explicit real-RAM/oracle computation reading

import Mathlib

namespace CapacitatedAssort.General

/-- Writer-style instrumented real-RAM computations. The state counts operations.
Arrays have unit read/write and amortized push, persistent list cons is unit,
and scalar arithmetic/comparison/rounding and one value-oracle call are unit.
Charges below group a fixed number of these instructions, never an asymptotic bound. -/
abbrev Work (α : Type) := StateM ℕ α

def charge (k : ℕ) : Work Unit := modify (· + k)

/-- Materialize a finite index loop: test, increment and index construction,
then one loop dispatch per element. Callback operations are charged separately. -/
def tabulate {α : Type} (n : ℕ) (f : Fin n → Work α) : Work (Array α) := do
  charge (3*n+1)
  let mut out := #[]
  for i in List.finRange n do
    charge 1
    let x ← f i
    charge 1
    out := out.push x
  return out

/-- Copy a persistent witness spine into an output list (traceback). -/
def trace {α : Type} : List α → Work (List α)
  | [] => do charge 1; return []
  | x :: xs => do
      charge 2
      let tail ← trace xs
      charge 1
      return x :: tail

/-- Mixed-radix decoding, coordinate zero least significant. -/
def decode (bases : Array ℕ) (j : ℕ) : Work (Array ℤ) := do
  charge (3*bases.size+1)
  let mut q := j
  let mut out := #[]
  for m in List.finRange bases.size do
    charge 6 -- dispatch, read, remainder, integer conversion, quotient, push
    let b := bases[m.val]!
    let r : ℤ := (q % b : ℕ)
    q := q / b
    out := out.push r
  return out

/-- Mixed-radix addressing. Called only on canonical residuals. -/
def encode (bases : Array ℕ) (r : Array ℤ) : Work ℕ := do
  charge (3*bases.size+1)
  let mut stride := 1
  let mut j := 0
  for m in List.finRange bases.size do
    charge 7 -- dispatch, two reads, toNat, two multiplies, addition
    j := j + (r[m.val]!).toNat * stride
    stride := stride * bases[m.val]!
  return j

def boxSize (bases : Array ℕ) : Work ℕ := do
  charge (3*bases.size+1)
  let mut size := 1
  for m in List.finRange bases.size do
    charge 3 -- dispatch, read, multiplication
    size := size * bases[m.val]!
  return size

end CapacitatedAssort.General


