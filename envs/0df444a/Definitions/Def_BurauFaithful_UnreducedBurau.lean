-- Prove2me | Definitions.Def_BurauFaithful_UnreducedBurau
-- name    : BurauFaithful_UnreducedBurau
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T19:54:35.078461+00:00
-- url     : https://prove2.me/theorems/f48b08a7-f41a-46ee-90a3-3db8033f7fdd
-- title:
--   The unreduced Burau representation $\rho_n : B_n \to \mathrm{GL}_n(\mathbb{Z}[t,t^{-1}])$
-- statement:
--   The unreduced Burau representation of the braid group.
--
--   Let $R=\mathbb{Z}[t,t^{-1}]$ be the ring of Laurent polynomials with integer coefficients, and let $B_n$ be the braid group on $n$ strands in Artin's presentation, with generators $\sigma_1,\dots,\sigma_{n-1}$ (indexed here by $\mathrm{Fin}(n-1)$, the index $i$ standing for $\sigma_{i+1}$).
--
--   For each generator index $i$ this file defines the $n\times n$ matrix
--
--   $$B_i \;=\; I_n \;+\; u_i v_i^{\mathsf T}, \qquad u_i = -t\,e_i + e_{i+1}, \qquad v_i = e_i - e_{i+1},$$
--
--   that is, the identity matrix altered only in the rows and columns $i$, $i+1$, where it carries the block
--
--   $$\begin{pmatrix} 1-t & t \\ 1 & 0 \end{pmatrix}.$$
--
--   The entries are recorded explicitly: the four block entries are $1-t$, $t$, $1$ and $0$, and every entry in a row or column outside $\{i,i+1\}$ agrees with the identity matrix.
--
--   Each $B_i$ is invertible over $R$, with inverse the identity matrix carrying the block $\begin{pmatrix} 0 & 1 \\ t^{-1} & 1-t^{-1} \end{pmatrix}$ in the same rows and columns, so $B_i$ defines an element of $\mathrm{GL}_n(R)$. The matrices $B_i$ satisfy Artin's relations — $B_iB_j = B_jB_i$ for $|i-j|\ge 2$ and $B_iB_{i+1}B_i = B_{i+1}B_iB_{i+1}$ — and this is proved here, so the assignment $\sigma_{i+1}\mapsto B_i$ descends to a genuine group homomorphism
--
--   $$\rho_n : B_n \longrightarrow \mathrm{GL}_n(\mathbb{Z}[t,t^{-1}]),$$
--
--   the unreduced Burau representation.
--
--   This is the representation whose faithfulness is the subject of the mission; it is the linear-algebra model of the action of the mapping class group of the $n$-punctured disk on the relative homology of its infinite cyclic cover.
--
--   **Formalization Note.** The braid group used is the published definition `BraidsLinksMCG.ArtinBraidGroup`. Invertibility is packaged by giving the inverse matrix explicitly, and the well-definedness of $\rho_n$ comes from the universal property of the presentation.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v1 (6 July 2026), https://arxiv.org/abs/2607.05283, Section 2 (definition of $\rho_n$)

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

/-!
# The unreduced Burau representation `ρ_n : B_n → GL_n(ℤ[t, t⁻¹])`

The Burau representation sends the Artin generator `σ_{i+1}` of the braid group on `n`
strands to the identity matrix of size `n`, modified in the rows and columns `i`, `i + 1`
by the block

```
  1 - t   t
  1       0
```

Here the braid group is `BraidsLinksMCG.ArtinBraidGroup n`, presented by generators
indexed by `Fin (n - 1)` (the index `i` standing for `σ_{i+1}`) and the braid relations,
and the coefficient ring is the ring `ℤ[t, t⁻¹]` of Laurent polynomials over `ℤ`.
-/

namespace BurauFaithful

open LaurentPolynomial Matrix BraidsLinksMCG

/-- The index `i` viewed inside `Fin n`. -/
def loIdx {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i, by have := i.isLt; omega⟩

/-- The index `i + 1` viewed inside `Fin n`. -/
def hiIdx {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i + 1, by have := i.isLt; omega⟩

/-- Column vector of the rank-one part of the `i`-th Burau matrix. -/
noncomputable def burauU {n : ℕ} (i : Fin (n - 1)) : Fin n → LaurentPolynomial ℤ :=
  Pi.single (loIdx i) (-T 1) + Pi.single (hiIdx i) 1

/-- Row vector of the rank-one part of the `i`-th Burau matrix. -/
noncomputable def burauV {n : ℕ} (i : Fin (n - 1)) : Fin n → LaurentPolynomial ℤ :=
  Pi.single (loIdx i) 1 + Pi.single (hiIdx i) (-1)

/-- The rank-one matrix with column `burauU i` and row `burauV j`. -/
noncomputable def burauQ {n : ℕ} (i j : Fin (n - 1)) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ) :=
  vecMulVec (burauU i) (burauV j)

/-- The unreduced Burau matrix of the Artin generator `σ_{i+1}`: the identity matrix of size
`n`, except for the block `!![1 - t, t; 1, 0]` in the rows and columns `i`, `i + 1`. -/
noncomputable def burauMatrix {n : ℕ} (i : Fin (n - 1)) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ) :=
  1 + burauQ i i

/-- The unreduced Burau matrix of `σ_{i+1}⁻¹`: the identity matrix of size `n`, except for the
block `!![0, 1; t⁻¹, 1 - t⁻¹]` in the rows and columns `i`, `i + 1`. -/
noncomputable def burauMatrixInv {n : ℕ} (i : Fin (n - 1)) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ) :=
  1 + (T (-1) : LaurentPolynomial ℤ) • burauQ i i

section Computations

variable {n : ℕ}

lemma T_one_mul_T_neg_one : (T 1 : LaurentPolynomial ℤ) * T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; norm_num

lemma burauQ_mul (i j k l : Fin (n - 1)) :
    (burauQ i j : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauQ k l =
      (burauV j ⬝ᵥ burauU k) • burauQ i l := by
  simp [burauQ, vecMulVec_mul_vecMulVec]

lemma burauV_apply (i : Fin (n - 1)) (a : Fin n) :
    burauV i a =
      (if (a : ℕ) = (i : ℕ) then 1 else 0) + (if (a : ℕ) = (i : ℕ) + 1 then -1 else 0) := by
  simp [burauV, Pi.single_apply, loIdx, hiIdx, Fin.ext_iff]

lemma dot_burau (i j : Fin (n - 1)) :
    burauV i ⬝ᵥ burauU j = burauV i (loIdx j) * (-T 1) + burauV i (hiIdx j) := by
  simp [burauU, dotProduct_add, dotProduct_single]

lemma loIdx_coe (j : Fin (n - 1)) : ((loIdx j : Fin n) : ℕ) = (j : ℕ) := rfl

lemma hiIdx_coe (j : Fin (n - 1)) : ((hiIdx j : Fin n) : ℕ) = (j : ℕ) + 1 := rfl

lemma dot_burau_self (i : Fin (n - 1)) : burauV i ⬝ᵥ burauU i = -T 1 - 1 := by
  rw [dot_burau, burauV_apply, burauV_apply, loIdx_coe, hiIdx_coe]
  rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl]
  ring

lemma dot_burau_succ (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
    burauV i ⬝ᵥ burauU j = T 1 := by
  rw [dot_burau, burauV_apply, burauV_apply, loIdx_coe, hiIdx_coe]
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
  ring

lemma dot_burau_pred (i j : Fin (n - 1)) (h : (i : ℕ) = (j : ℕ) + 1) :
    burauV i ⬝ᵥ burauU j = 1 := by
  rw [dot_burau, burauV_apply, burauV_apply, loIdx_coe, hiIdx_coe]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
  ring

lemma dot_burau_far (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    burauV i ⬝ᵥ burauU j = 0 := by
  rw [dot_burau, burauV_apply, burauV_apply, loIdx_coe, hiIdx_coe]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

lemma burauMatrix_mul_inv (i : Fin (n - 1)) :
    (burauMatrix i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauMatrixInv i = 1 := by
  have hQ : (burauQ i i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauQ i i =
      ((-T 1 - 1 : LaurentPolynomial ℤ)) • burauQ i i := by
    rw [burauQ_mul, dot_burau_self]
  have key : (burauQ i i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) +
      (T (-1) : LaurentPolynomial ℤ) • (burauQ i i + ((-T 1 - 1 : LaurentPolynomial ℤ)) •
        burauQ i i) = 0 := by
    match_scalars
    linear_combination -T_one_mul_T_neg_one
  simp only [burauMatrix, burauMatrixInv, add_mul, mul_add, one_mul, mul_one,
    mul_smul_comm, hQ, add_assoc]
  rw [key, add_zero]

lemma burauMatrixInv_mul (i : Fin (n - 1)) :
    (burauMatrixInv i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauMatrix i = 1 := by
  have hQ : (burauQ i i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauQ i i =
      ((-T 1 - 1 : LaurentPolynomial ℤ)) • burauQ i i := by
    rw [burauQ_mul, dot_burau_self]
  have key : (T (-1) : LaurentPolynomial ℤ) • burauQ i i +
      ((burauQ i i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) +
        (T (-1) : LaurentPolynomial ℤ) • ((-T 1 - 1 : LaurentPolynomial ℤ) • burauQ i i)) = 0 := by
    match_scalars
    linear_combination -T_one_mul_T_neg_one
  simp only [burauMatrix, burauMatrixInv, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, hQ, add_assoc]
  rw [key, add_zero]

end Computations

/-- The unreduced Burau matrix of `σ_{i+1}`, as an element of `GL_n(ℤ[t, t⁻¹])`. -/
noncomputable def burauGen {n : ℕ} (i : Fin (n - 1)) : GL (Fin n) (LaurentPolynomial ℤ) :=
  ⟨burauMatrix i, burauMatrixInv i, burauMatrix_mul_inv i, burauMatrixInv_mul i⟩

section Entries

variable {n : ℕ}

/-- Entrywise description of the unreduced Burau matrix of `σ_{i+1}`. -/
lemma burauMatrix_apply (i : Fin (n - 1)) (a b : Fin n) :
    burauMatrix i a b = (if (a : ℕ) = (b : ℕ) then 1 else 0) +
      ((if (a : ℕ) = (i : ℕ) then -T 1 else 0) + (if (a : ℕ) = (i : ℕ) + 1 then 1 else 0)) *
      ((if (b : ℕ) = (i : ℕ) then 1 else 0) + (if (b : ℕ) = (i : ℕ) + 1 then -1 else 0)) := by
  simp [burauMatrix, burauQ, vecMulVec_apply, burauU, burauV, Matrix.one_apply,
    Pi.single_apply, loIdx, hiIdx, Fin.ext_iff]

lemma burauMatrix_lo_lo (i : Fin (n - 1)) : burauMatrix i (loIdx i) (loIdx i) = 1 - T 1 := by
  rw [burauMatrix_apply, loIdx_coe]
  split_ifs <;> first | ring1 | (exfalso; omega)

lemma burauMatrix_lo_hi (i : Fin (n - 1)) : burauMatrix i (loIdx i) (hiIdx i) = T 1 := by
  rw [burauMatrix_apply, loIdx_coe, hiIdx_coe]
  split_ifs <;> first | ring1 | (exfalso; omega)

lemma burauMatrix_hi_lo (i : Fin (n - 1)) : burauMatrix i (hiIdx i) (loIdx i) = 1 := by
  rw [burauMatrix_apply, loIdx_coe, hiIdx_coe]
  split_ifs <;> first | ring1 | (exfalso; omega)

lemma burauMatrix_hi_hi (i : Fin (n - 1)) : burauMatrix i (hiIdx i) (hiIdx i) = 0 := by
  rw [burauMatrix_apply, hiIdx_coe]
  split_ifs <;> first | ring1 | (exfalso; omega)

/-- Outside the rows `i`, `i + 1` the Burau matrix of `σ_{i+1}` agrees with the identity. -/
lemma burauMatrix_of_row_ne (i : Fin (n - 1)) (a b : Fin n)
    (ha : (a : ℕ) ≠ (i : ℕ)) (ha' : (a : ℕ) ≠ (i : ℕ) + 1) :
    burauMatrix i a b = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  rw [burauMatrix_apply, if_neg ha, if_neg ha']
  ring

/-- Outside the columns `i`, `i + 1` the Burau matrix of `σ_{i+1}` agrees with the identity. -/
lemma burauMatrix_of_col_ne (i : Fin (n - 1)) (a b : Fin n)
    (hb : (b : ℕ) ≠ (i : ℕ)) (hb' : (b : ℕ) ≠ (i : ℕ) + 1) :
    burauMatrix i a b = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  rw [burauMatrix_apply, if_neg hb, if_neg hb']
  ring

end Entries

section Relations

variable {n : ℕ}

lemma burauGen_comm (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    (burauGen i : GL (Fin n) (LaurentPolynomial ℤ)) * burauGen j = burauGen j * burauGen i := by
  have h1 : burauV i ⬝ᵥ burauU j = 0 := dot_burau_far i j h
  have h2 : burauV j ⬝ᵥ burauU i = 0 := dot_burau_far j i (by omega)
  apply Units.ext
  show (burauMatrix i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauMatrix j =
    burauMatrix j * burauMatrix i
  simp [burauMatrix, add_mul, mul_add, burauQ_mul, h1, h2]
  abel

lemma burauGen_braid (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
    (burauGen i : GL (Fin n) (LaurentPolynomial ℤ)) * burauGen j * burauGen i =
      burauGen j * burauGen i * burauGen j := by
  have hij : burauV i ⬝ᵥ burauU j = T 1 := dot_burau_succ i j h
  have hji : burauV j ⬝ᵥ burauU i = 1 := dot_burau_pred j i h
  have hii : burauV i ⬝ᵥ burauU i = -T 1 - 1 := dot_burau_self i
  have hjj : burauV j ⬝ᵥ burauU j = -T 1 - 1 := dot_burau_self j
  apply Units.ext
  show (burauMatrix i : Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ)) * burauMatrix j *
      burauMatrix i = burauMatrix j * burauMatrix i * burauMatrix j
  simp only [burauMatrix, add_mul, mul_add, one_mul, mul_one, burauQ_mul, hij, hji, hii, hjj,
    smul_smul, smul_mul_assoc]
  match_scalars <;> ring

/-- The unreduced Burau matrices of the Artin generators satisfy the braid relations, so they
define a representation of the braid group. -/
lemma burauGen_relations (n : ℕ) :
    ∀ r ∈ braidRels n, (FreeGroup.lift (burauGen (n := n))) r = 1 := by
  intro r hr
  simp only [braidRels, Set.mem_union] at hr
  rcases hr with ⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩
  · have hij : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ) := by omega
    have hcomm := burauGen_comm i j hij
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hcomm]
    group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]
    exact burauGen_braid i j h

end Relations

/-- The unreduced Burau representation `ρ_n : B_n → GL_n(ℤ[t, t⁻¹])`, sending the Artin
generator `σ_{i+1}` to `burauMatrix i`. -/
noncomputable def burauRep (n : ℕ) :
    ArtinBraidGroup n →* GL (Fin n) (LaurentPolynomial ℤ) :=
  PresentedGroup.toGroup (burauGen_relations n)

end BurauFaithful


