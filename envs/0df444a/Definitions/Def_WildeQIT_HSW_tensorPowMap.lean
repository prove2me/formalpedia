-- Prove2me | Definitions.Def_WildeQIT_HSW_tensorPowMap
-- name    : WildeQIT_HSW_tensorPowMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:02.729763+00:00
-- url     : https://prove2.me/theorems/4d7b17ee-2dc7-4c16-a99b-38bfa4567de3
-- title:
--   Tensor-power channel $\mathcal N^{\otimes n}$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel with Kraus operators $\{K_l\}_{l}$, so that $\mathcal N(X) = \sum_l K_l X K_l^\dagger$. The channel $\mathcal N^{\otimes n}$ models $n$ independent uses of $\mathcal N$: it acts on operators on $\mathcal H_{A'}^{\otimes n}$ by
--
--   $$
--   \mathcal N^{\otimes n}(X) = \sum_{l_1,\dots,l_n} (K_{l_1}\otimes\cdots\otimes K_{l_n})\,X\,(K_{l_1}\otimes\cdots\otimes K_{l_n})^\dagger .
--   $$
--
--   Codes for classical communication feed a state $\rho^m_{A'^n}$, possibly entangled across the $n$ inputs, into $\mathcal N^{\otimes n}$; the regularized Holevo information is built from $\chi(\mathcal N^{\otimes k})$.
--
--   **Formalization Note** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form). $\mathcal H_A^{\otimes n}$ is indexed by functions $\{1,\dots,n\}\to A$, and the matrix entries of $K_{l_1}\otimes\cdots\otimes K_{l_n}$ are the products $\prod_i K_{l_i}(b_i,a_i)$. For $n = 0$ the space is one-dimensional and the map is the identity.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, (20.10), p. 562; (20.23), p. 564

import Mathlib
import Definitions.Def_WildeQIT_QChannel

open Matrix

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (20.10), p. 562:
the **tensor-power channel** `N^⊗n`, `n` independent uses of the channel `N_{A′→B}`, acting on
operators on `H_{A′}^{⊗n}` and returning operators on `H_B^{⊗n}`.

**Formalization Note.** `N` is a published `WildeQIT.QChannel A B` with Kraus operators
`K_l`. `H_A^{⊗n}` is indexed by `Fin n → A` (the `i`-th coordinate is the `i`-th system), and
`N^⊗n` is given by its Kraus operators `K_{l₁} ⊗ ⋯ ⊗ K_{lₙ}`, indexed by `l : Fin n → ι`, whose
matrix entries are `∏ᵢ K_{lᵢ}(bᵢ, aᵢ)`: `N^⊗n(X) = Σ_l K_l X K_l†`. These are the Kraus operators
of the tensor product of channels. At `n = 0` it is the identity of the one-dimensional space. -/
noncomputable def tensorPowMap {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : WildeQIT.QChannel A B) (n : ℕ) (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    Matrix (Fin n → B) (Fin n → B) ℂ :=
  ∑ l : Fin n → N.ι,
    (Matrix.of fun (b : Fin n → B) (a : Fin n → A) => ∏ i, N.K (l i) (b i) (a i)) * X *
      (Matrix.of fun (b : Fin n → B) (a : Fin n → A) => ∏ i, N.K (l i) (b i) (a i))ᴴ

end WildeQIT.HSW


