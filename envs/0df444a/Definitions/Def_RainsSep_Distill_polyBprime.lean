-- Prove2me | Definitions.Def_RainsSep_Distill_polyBprime
-- name    : RainsSep_Distill_polyBprime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:59:06.840928+00:00
-- url     : https://prove2.me/theorems/cf4da987-053f-4420-bbb9-498edfbf6821
-- title:
--   The polynomial $B'(u,v,x,y)$
-- statement:
--   For a product Kraus representation of $\mathcal P$,
--
--   $$
--   B'(u,v,x,y)=\sum_{i=0}^n x^{n-i}y^i\sum_{S\subset\{1,\dots,n\},\ |S|=i}\Big(u\,B'_S(\mathcal P)+v\,B'_{\{0\}\cup S}(\mathcal P)\Big),
--   $$
--
--   a polynomial in four variables with real coefficients; $S$ runs over the sets of qubits of size $i$ (the empty set included), and $\{0\}\cup S$ adds $W$.
--
--   **Formalization Note** A formal polynomial in the variables $u,v,x,y$. Qubits are numbered $0,\dots,n-1$ and $W$ carries the separate label `none`.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (24), p. 2

import Mathlib
import Definitions.Def_RainsSep_Distill_enumBprime

namespace RainsSep.Distill

/-- **The polynomial `B′(u, v, x, y)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (24), p. 2: "We can then define a polynomial
B′(u, v, x, y) = Σ_i x^{n−i} y^i Σ_{S⊂{1,2,...n}, |S|=i} (u B′_S(P) + v B′_{0}∪S(P)). (24)"

A polynomial in `u, v, x, y` = `X 0, X 1, X 2, X 3`, for a product Kraus representation
`(P₁, P₂)`.

**Formalization Note.** The qubits are `Fin n` (the paper's `1, …, n`) and `W` is `none` (the
paper's `0`); `S` ranges over all subsets of the qubits of size `i`, the empty set included,
and `{0} ∪ S` is `insert none (S.map some)`. -/
noncomputable def polyBprime {n K m : ℕ}
    (P₁ P₂ : Fin m → Matrix (Fin K) (QAlgorithms.Qubits n) ℂ) : MvPolynomial (Fin 4) ℝ :=
  ∑ i ∈ Finset.range (n + 1), MvPolynomial.X 2 ^ (n - i) * MvPolynomial.X 3 ^ i *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      (MvPolynomial.C (enumBprime P₁ P₂ (S.map Function.Embedding.some)) * MvPolynomial.X 0 +
        MvPolynomial.C (enumBprime P₁ P₂ (insert none (S.map Function.Embedding.some))) *
          MvPolynomial.X 1)

end RainsSep.Distill


