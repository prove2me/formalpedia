-- Prove2me | Definitions.Def_MatMulDS_IsEnlargement
-- name    : MatMulDS_IsEnlargement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:10.145938+00:00
-- url     : https://prove2.me/theorems/1f75eed5-0c6c-41a1-8ff7-13dee0bf1f82
-- title:
--   Enlargement of an identity
-- statement:
--   An identity $(T',D')$ is an **enlargement** of $(T,D)$ at a central block $\beta_0$ with central output $w_0$ if, writing $d=|K_{\beta_0}|$, $r=|P|$, $n_A,n_B$ for the numbers of left and right variables and $d^*=r-(n_A-d)-(n_B-d)$:
--
--   1. it has the same outputs and blocks, and every block other than $\beta_0$ keeps its middle indices, so every other output computes the same bilinear form;
--   2. it is $\varepsilon$-homogeneous and has central block $\beta_0$ with central output $w_0$, now of length $d^*$;
--   3. it computes $T'$ with the same products $P$, and every output has the same relevant products;
--   4. it has $n_A-d+d^*$ left and $n_B-d+d^*$ right variables.
--
--   This is what Lemma 6.1 constructs, and Theorem 6.2 and Proposition 7.1 work with any identities so related. The predicate `HasStrictWeight` says that an identity has a private map with a compatible strict weight.
--
--   **Formalization Note** New middle indices are the right summand of $K\oplus\mathrm{Fin}\,n$: they are used by no other block.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma 6.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **The identity `(T', D')` is an enlargement of `(T, D)` at the central block `β₀` with central output `w₀`**:
properties (a), (b), (c) of Lemma 6.1, p.40 (STOC 2027 submission, held file sha256 6c5a1c16…), with `d` the
length of `w₀`, `r = |P|`, `n_A`, `n_B` the numbers of variables, and `d∗ = r − (n_A − d) − (n_B − d)`.

* (a) It has the same outputs (`rows` and `cols` are unchanged), and it computes the same bilinear forms at all
  of them except `w₀` (every other block keeps its middle indices, `inl`).
* (b) It is ε-homogeneous and has a central block with the central output `w₀`, now of length `d∗`.
* (c) It computes a block tensor whose blocks consist of the same outputs, and indexing its products by `P` every
  output has the same relevant products.
* It has `r` products (the same `P`), `n_A − d + d∗` left variables and `n_B − d + d∗` right variables.

**Formalization Note** New middle indices are `inr`: "a new middle index, which no other block uses" (p.41). The
number of variables and `d∗` are stated in `ℤ`, since `r − (n_A − d) − (n_B − d)` is a difference. -/
structure IsEnlargement (T : BlockTensor I K J B) (D : IdentityData I K J P) (β₀ : B) (w₀ : I × J)
    {n : ℕ} (T' : BlockTensor I (K ⊕ Fin n) J B) (D' : IdentityData I (K ⊕ Fin n) J P) : Prop where
  rows_eq : T'.rows = T.rows
  cols_eq : T'.cols = T.cols
  mids_eq : ∀ β, β ≠ β₀ → T'.mids β = (T.mids β).map ⟨Sum.inl, Sum.inl_injective⟩
  computes : D'.Computes T'
  homogeneous : D'.IsHomogeneous T'
  central : D'.IsCentralBlock T' β₀ w₀
  length_eq : ((T'.mids β₀).card : ℤ) =
    (Fintype.card P : ℤ) - ((T.leftVars.card : ℤ) - (T.mids β₀).card) -
      ((T.rightVars.card : ℤ) - (T.mids β₀).card)
  left_card : (T'.leftVars.card : ℤ) = (T.leftVars.card : ℤ) - (T.mids β₀).card + (T'.mids β₀).card
  right_card : (T'.rightVars.card : ℤ) = (T.rightVars.card : ℤ) - (T.mids β₀).card + (T'.mids β₀).card
  prel_eq : ∀ o ∈ T.outputs, D'.Prel o = D.Prel o

/-- The identity has a private map with a compatible strict weight function. -/
def HasStrictWeight (T : BlockTensor I K J B) (D : IdentityData I K J P) : Prop :=
  ∃ (ρ : T.Out → P) (wt : P → ℝ),
    D.IsPrivateMap T ρ ∧ D.IsCompatible T ρ wt ∧ D.IsStrict T ρ wt

end MatMulDS


