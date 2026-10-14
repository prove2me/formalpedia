-- Prove2me | Definitions.Def_IntMul_HvdH_SliceTensor
-- name    : IntMul_HvdH_SliceTensor
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T23:03:14.51897+00:00
-- url     : https://prove2.me/theorems/31756e1b-6ecd-489d-8e9a-979f06202ea2
-- title:
--   Slice-wise tensor products of one-dimensional maps (Harvey–van der Hoeven §2.7)
-- statement:
--   A $d$-dimensional array is a function $x:\mathbb N^d\to\mathbb C$, and a one-dimensional map is any function $A:(\mathbb N\to\mathbb C)\to(\mathbb N\to\mathbb C)$.
--
--   * `sliceMap i A x` applies $A$ to every $i$-slice of $x$: $(B_ix)_j=A\bigl(k\mapsto x_{j[i\mapsto k]}\bigr)_{j_i}$.
--   * `sliceComp A l` applies $B_i$ for the axes $i$ in the list $l$, in order.
--   * `tensorMap A` $=B_d\cdots B_1$ is the tensor product $\bigotimes_iA_i$, computed slice by slice as in the proof of Lemma 2.11.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.7, Lemma 2.11 (tensor products)

import Mathlib

/-! Tensor products of maps acting slice by slice (Harvey–van der Hoeven §2.7, Lemma 2.11).
A `d`-dimensional array is a function `(Fin d → ℕ) → ℂ`; a one-dimensional map is any function
`(ℕ → ℂ) → (ℕ → ℂ)`. -/

namespace IntMul.HvdH

/-- Apply a one-dimensional map `A` to every `i`-slice of a `d`-dimensional array. -/
def sliceMap {d : ℕ} (i : Fin d) (A : (ℕ → ℂ) → (ℕ → ℂ)) (x : (Fin d → ℕ) → ℂ) :
    (Fin d → ℕ) → ℂ :=
  fun j => A (fun k => x (Function.update j i k)) (j i)

/-- Apply the maps `A i` slice by slice, for the axes listed in `l`, first axis first. -/
def sliceComp {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) :
    List (Fin d) → ((Fin d → ℕ) → ℂ) → ((Fin d → ℕ) → ℂ)
  | [] => id
  | i :: l => sliceComp A l ∘ sliceMap i (A i)

/-- The tensor product `⊗ᵢ Aᵢ = B_d ⋯ B₁` with `Bᵢ` acting on `i`-slices. -/
def tensorMap {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) :
    ((Fin d → ℕ) → ℂ) → ((Fin d → ℕ) → ℂ) :=
  sliceComp A (List.finRange d)

end IntMul.HvdH


