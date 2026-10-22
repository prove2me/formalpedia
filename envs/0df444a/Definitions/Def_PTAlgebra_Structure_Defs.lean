-- Prove2me | Definitions.Def_PTAlgebra_Structure_Defs
-- name    : PTAlgebra_Structure_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:33.674311+00:00
-- url     : https://prove2.me/theorems/0ed9cc3c-f125-4159-8e2f-7ca7c8882bb4
-- title:
--   Definitions 29 and 40 and Theorem 30 — Q(α), u(α), U(α), occurrence, matrix ideals, tableau count
-- statement:
--   The operator space is $(\mathbb C^d)^{\otimes n}$, with $n=m+2$ and $d\ge1$. The published model supplies the permutation operators $V(\sigma)$, partial transposition $t_n$ on the last factor, their span $A=A_n^{t_n}(d)$, and the ideal candidate $M$ spanned by the partially transposed permutations that move the last position.
--
--   For a complete family $\varphi^\alpha$ of irreducible representations of $S(n-2)$, this file defines the block matrix of Definition 29,
--   $$Q^{ab}_{ij}(\alpha)=d^{\delta_{ab}}\varphi^\alpha_{ij}((a\ n-1)(ab)(b\ n-1)),$$
--   and the operators of Definition 40,
--   $$u^{ab}_{ij}(\alpha)=\frac{w^\alpha}{(n-2)!}V(an)^{t_n}\sum_{\sigma\in S(n-2)}\varphi^\alpha_{ji}(\sigma^{-1})V((a\ n-1)\sigma(b\ n-1)).$$
--   Here $w^\alpha=\dim\varphi^\alpha$. Their complex span is $U(\alpha)$. An irrep *occurs* when it has a nonzero intertwiner into the permutation action on $(\mathbb C^d)^{\otimes(n-2)}$.
--
--   The auxiliary ideal predicate means a subspace of $A$ closed under multiplication by $A$ on either side. A matrix ideal of order $r$ has $r^2$ independent matrix units spanning it and obeying $e_{kl}e_{k'l'}=\delta_{lk'}e_{kl'}$. For a partition $\nu$ of $n-1$, $h(\nu)$ is its number of rows and $f^\nu$ is its number of standard Young tableaux, used for $\dim\psi^\nu$.
--
--   These definitions are the common language for the structure theorem and its milestones.
--
--   **Formalization Note** Labels $a,b$ are 0-based `Fin (m+1)`; their final value denotes the paper’s $n-1$. The irreducible matrices are real orthogonal, hence unitary over $\mathbb C$. `qPerm` implements the paper’s printed case split: if $a,b<n-1$, use $(ab)$; otherwise use the identity. The diagonal blocks retain the factor $d$.
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, pp. 8, 15, Definitions 29 and 40; p. 5, Proposition 13; pp. 8–9, Theorem 30

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

noncomputable section

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis QAlgorithms.Schur
open scoped BigOperators

/-- The permutation `(a n−1)(ab)(b n−1)` restricted to the first `n−2` sites,
with the paper's labels shifted from 1-based to 0-based. -/
def qPerm (m : ℕ) (a b : Fin (m + 1)) : Equiv.Perm (Fin m) :=
  if ha : a.val < m then
    if hb : b.val < m then
      Equiv.swap (⟨a.val, ha⟩ : Fin m) ⟨b.val, hb⟩
    else 1
  else 1

/-- Definition 29: the block matrix `Q(α)`, indexed by a site label and an irrep index.
The diagonal blocks are `d` times the identity, including the final block. -/
def Qmat {m : ℕ} (d : ℕ) (F : IrrepFamily m) (α : F.ι) :
    Matrix (Fin (m + 1) × Fin (F.dim α))
      (Fin (m + 1) × Fin (F.dim α)) ℂ :=
  Matrix.of fun ai bj =>
    (if ai.1 = bj.1 then (d : ℂ) else 1) *
      ((F.rep α (qPerm m ai.1 bj.1) ai.2 bj.2 : ℝ) : ℂ)

/-- Definition 40: `u^{ab}_{ij}(α)` from the partially transposed swap `(a n)` and
the matrix coefficients of `ϕ^α` on `S(n−2)`. -/
def uOp {m : ℕ} (d : ℕ) (F : IrrepFamily m) (α : F.ι)
    (a b : Fin (m + 1)) (i j : Fin (F.dim α)) : Op d (m + 2) :=
  ((F.dim α : ℂ) / (m.factorial : ℂ)) •
    (ptLast (tensorPermutation d (m + 2)
      (Equiv.swap (Fin.castSucc a) (Fin.last (m + 1)))) *
      ∑ σ : Equiv.Perm (Fin m),
        (((F.rep α σ⁻¹ j i : ℝ) : ℂ) •
          tensorPermutation d (m + 2)
            (liftPerm (m + 1) 1 (Equiv.swap a (Fin.last m)) *
              liftPerm m 2 σ *
              liftPerm (m + 1) 1 (Equiv.swap b (Fin.last m)))))

/-- The irrep `ϕ^α` occurs in the permutation representation on
`(ℂ^d)^{⊗(n−2)}` precisely when it has a nonzero intertwiner into that space. -/
def Occurs {m : ℕ} (d : ℕ) (F : IrrepFamily m) (α : F.ι) : Prop :=
  ∃ T : Matrix (Site d m) (Fin (F.dim α)) ℂ,
    T ≠ 0 ∧ ∀ σ : Equiv.Perm (Fin m),
      tensorPermutation d m σ * T = T * (F.rep α σ).map Complex.ofReal

/-- The ideal `U(α)` of Theorem 30(a), spanned by Definition 40's operators. -/
def Uideal {m : ℕ} (d : ℕ) (F : IrrepFamily m) (α : F.ι) :
    Submodule ℂ (Op d (m + 2)) :=
  Submodule.span ℂ {x | ∃ a b i j, x = uOp d F α a b i j}

/-- An ideal in the represented algebra `A` (the latter is a complex subspace of matrices). -/
def IsIdealOf {d m : ℕ} (I A : Submodule ℂ (Op d (m + 2))) : Prop :=
  I ≤ A ∧ ∀ x ∈ A, ∀ y ∈ I, x * y ∈ I ∧ y * x ∈ I

/-- A matrix ideal of order `r`: independent matrix units span the ideal and obey
the full matrix-unit multiplication law. For `r = 0` this forces the zero ideal. -/
def IsMatrixIdeal {d m : ℕ} (I : Submodule ℂ (Op d (m + 2))) (r : ℕ) : Prop :=
  ∃ e : Fin r → Fin r → Op d (m + 2),
    LinearIndependent ℂ (fun t : Fin r × Fin r => e t.1 t.2) ∧
    Submodule.span ℂ (Set.range (fun t : Fin r × Fin r => e t.1 t.2)) = I ∧
    ∀ k l k' l', e k l * e k' l' = if l = k' then e k l' else 0

/-- The corner subspace `eAe`, used for the complementary ideals of Proposition 27. -/
def corner {d m : ℕ} (e : Op d (m + 2)) (A : Submodule ℂ (Op d (m + 2))) :
    Submodule ℂ (Op d (m + 2)) :=
  Submodule.span ℂ {x | ∃ a ∈ A, x = e * a * e}

/-- The height `h(ν)` of a partition: its number of nonzero rows (Proposition 13). -/
def hgt {n : ℕ} (ν : Nat.Partition n) : ℕ := ν.parts.card

/-- The number of standard Young tableaux of partition shape `ν`. The cells are
coordinates in the rows of the weakly decreasing list of parts; a tableau is a
bijection to `Fin n` increasing along rows and down columns. -/
def numSYT {n : ℕ} (ν : Nat.Partition n) : ℕ :=
  let rows := ν.parts.sort (· ≥ ·)
  Fintype.card
    {t : ((Σ i : Fin rows.length, Fin rows[i.val]) → Fin n) //
      Function.Bijective t ∧
      ∀ c c',
        ((c.1 = c'.1 ∧ c.2.val < c'.2.val) ∨
          (c.2.val = c'.2.val ∧ c.1.val < c'.1.val)) → t c < t c'}

end PTAlgebra.Structure


