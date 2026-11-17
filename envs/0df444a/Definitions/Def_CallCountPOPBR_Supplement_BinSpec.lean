-- Prove2me | Definitions.Def_CallCountPOPBR_Supplement_BinSpec
-- name    : CallCountPOPBR_Supplement_BinSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:03:39.318253+00:00
-- url     : https://prove2.me/theorems/7464653f-59d9-42db-a574-b0f56fdb44a4
-- title:
--   Full-binary decreasing specifications and compatible child pairs
-- statement:
--   Fix $\beta\ge1$. A **full-binary specification** assigns to every $n\ge\beta$ an unordered pair of child indices $\{i,j\}$ with $i,j<n$, allowing $i=j$. Inputs below $\beta$ are base cases. Its invocation counts satisfy
--
--   $$
--   c_n=1\quad(n<\beta),\qquad c_n=1+c_i+c_j\quad(n\ge\beta).
--   $$
--
--   For any numerical sequence $c$, $P_n$ is the finite set of unordered pairs below $n$ satisfying $c_i+c_j+1=c_n$. The latter equation is equivalent to the paper's $c_i+c_j=c_n-1$ without using truncated natural-number subtraction.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Section 7.1, pp.12–13

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **A full-binary specification with base set `{0, …, β − 1}`** (§7.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §7.1, p.12:
"Throughout this subsection we use the full-binary model with base set {0, . . . , β − 1}, for a
fixed β ≥ 1: inputs n < β are base cases with c_n = 1, and every input n ≥ β makes exactly two
calls to strictly smaller inputs."

A specification assigns to every input `n ≥ β` the unordered pair `{i, j}` (repetition allowed) of
its two children, `i, j < n`. This is exactly the unordered dependency multigraph (§7.1, p.12:
"unordered dependency multisets").

**Formalization Note.** Base inputs carry no data, so two specifications are equal iff they choose
the same unordered pair at every `n ≥ β`. -/
def BinSpec (β : ℕ) : Type := ∀ n : ℕ, β ≤ n → Sym2 (Fin n)

/-- **The call counts of a full-binary specification** (§7.1, p.12): `c_n = 1` for `n < β`, and
`c_n = 1 + c_i + c_j` for `n ≥ β` with child pair `{i, j}`, by strong recursion on `n`. -/
def BinSpec.count {β : ℕ} (s : BinSpec β) : ℕ → ℕ :=
  Nat.strongRec fun n IH =>
    if h : β ≤ n then
      1 + Sym2.lift ⟨fun i j : Fin n => IH i i.2 + IH j j.2, fun _ _ => Nat.add_comm _ _⟩ (s n h)
    else 1

/-- **The set `P_n` of compatible child pairs** (§7.1, p.13): "P_n = {{i, j} : 0 ≤ i ≤ j < n,
c_i + c_j = c_n − 1}, where {i, j} denotes an unordered pair with repetition permitted."

**Formalization Note.** Unordered pairs `{i, j}` with `i ≤ j < n` are the elements of
`Sym2 (Fin n)`. The condition `c_i + c_j = c_n − 1` is written `c_i + c_j + 1 = c_n`, which is the
integer equation without truncated subtraction (for `c_n = 0` the integer equation has no solution,
and neither has this one). -/
def pairSet (c : ℕ → ℕ) (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun z =>
    Sym2.lift ⟨fun i j : Fin n => c i + c j, fun _ _ => Nat.add_comm _ _⟩ z + 1 = c n

end CallCountPOPBR.Supplement


