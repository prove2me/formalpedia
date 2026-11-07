-- Prove2me | Definitions.Def_GraphTensorCP_polyMulTensor
-- name    : GraphTensorCP_polyMulTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:14.999519+00:00
-- url     : https://prove2.me/theorems/00f15215-07d6-48d8-ad5e-88b537e58e9e
-- title:
--   Polynomial multiplication tensor $\mathcal C_n(a_1,\dots,a_{n-1})$
-- statement:
--   Let $n\ge2$ and let $a_1,\dots,a_{n-1}$ be positive integers. Put $D=1+\sum_{j=1}^{n-1}(a_j-1)$. The **polynomial multiplication tensor** is the $n$-th order tensor
--
--   $$\mathcal C_n(a_1,\dots,a_{n-1})=\sum_{i_1=0}^{a_1-1}\cdots\sum_{i_{n-1}=0}^{a_{n-1}-1}e^{(a_1)}_{i_1}\otimes\cdots\otimes e^{(a_{n-1})}_{i_{n-1}}\otimes e^{(D)}_{i_1+\cdots+i_{n-1}}$$
--
--   of dimension vector $(a_1,\dots,a_{n-1},D)$. Its first $n-1$ legs are the input legs and its last leg is the output leg: contracting the input legs against the coefficient vectors of polynomials $f_1,\dots,f_{n-1}$ of degrees $<a_j$ gives the coefficient vector of their product.
--
--   It is the interpolation resource of the complete-graph argument: its asymptotic rank is exactly $D$ over every field.
--
--   **Formalization Note** The input lengths are a vector $a:\mathrm{Fin}(n-1)\to\mathbb N$; legs are 0-based, with the output leg at index $n-1$. The definition typechecks for every $a$; positivity of the $a_j$ is a hypothesis of each theorem.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 3.1, p.29

import Mathlib
import Definitions.Def_mme_tensor

universe u

namespace GraphTensorCP

open PiTensorProduct

/-- The dimension vector `(a₁, …, a_{n−1}, D)` of the polynomial multiplication tensor, with
`D = 1 + Σ_{j=1}^{n−1} (a_j − 1)` (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definition 3.1, p.29). Legs `0, …, n−2` (0-based) are the input legs, leg `n−1` is the output
leg. -/
def polyDims {n : ℕ} (a : Fin (n - 1) → ℕ) (d : Fin n) : ℕ :=
  if h : d.val < n - 1 then a ⟨d.val, h⟩ else 1 + ∑ j, (a j - 1)

/-- The basis index of the term `e^{(a₁)}_{i₁} ⊗ ⋯ ⊗ e^{(a_{n−1})}_{i_{n−1}} ⊗ e^{(D)}_{i₁+⋯+i_{n−1}}`
on leg `d`: the input index `i_d` on an input leg, and `i₁ + ⋯ + i_{n−1}` on the output leg. -/
def polyIdx {n : ℕ} (a : Fin (n - 1) → ℕ) (i : (j : Fin (n - 1)) → Fin (a j)) (d : Fin n) :
    Fin (polyDims a d) :=
  ⟨if h : d.val < n - 1 then (i ⟨d.val, h⟩ : ℕ) else ∑ j, (i j : ℕ), by
    unfold polyDims
    split_ifs with h
    · exact (i ⟨d.val, h⟩).isLt
    · have hj : ∀ j, (i j : ℕ) ≤ a j - 1 := fun j => Nat.le_sub_one_of_lt (i j).isLt
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
      omega⟩

/-- **Polynomial multiplication tensor** `C_n(a₁, …, a_{n−1})` (Zhou, *Asymptotic Rank of Weighted
Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03),
Definition 3.1, p.29): "Put D = 1 + Σ_{j=1}^{n−1}(a_j − 1). The polynomial multiplication tensor
is the n-th order tensor C_n(a₁, . . . , a_{n−1}) = Σ_{i₁=0}^{a₁−1} ⋯ Σ_{i_{n−1}=0}^{a_{n−1}−1}
e^{(a₁)}_{i₁} ⊗_C ⋯ ⊗_C e^{(a_{n−1})}_{i_{n−1}} ⊗_C e^{(D)}_{i₁+⋯+i_{n−1}}."

**Formalization Note.** The input lengths are a vector `a : Fin (n−1) → ℕ` (the paper's
`a₁, …, a_{n−1}` are `a 0, …, a (n−2)`); leg `d` is `Fin (polyDims a d) → K`. The definition
typechecks for every `a`; the paper's positivity `a_j ≥ 1` (and `n ≥ 2`) is a hypothesis of each
theorem. -/
noncomputable def polyMulTensor (K : Type u) [Field K] (n : ℕ) (a : Fin (n - 1) → ℕ) :
    MME.TensorObj K n where
  V d := Fin (polyDims a d) → K
  t := ∑ i : ((j : Fin (n - 1)) → Fin (a j)),
    tprod K (fun d => (Pi.single (polyIdx a i d) (1 : K) : Fin (polyDims a d) → K))

end GraphTensorCP


