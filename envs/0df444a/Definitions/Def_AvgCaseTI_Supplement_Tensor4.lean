-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_Tensor4
-- name    : AvgCaseTI_Supplement_Tensor4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:27:51.246929+00:00
-- url     : https://prove2.me/theorems/65c06172-2170-4b82-93fd-f143f40aee7f
-- title:
--   4-way arrays and their isomorphism under $\mathrm{GL}(n,q)^4$
-- statement:
--   A **4-way array** over a field $\mathbb F$ is $A=(a_{i,j,k,\ell})_{i,j,k,\ell\in[n]}$, an element of $\mathbb F^n\otimes\mathbb F^n\otimes\mathbb F^n\otimes\mathbb F^n$.
--
--   Two 4-way arrays $A,B$ are **isomorphic** when there are invertible $L,R,S,T\in\mathrm{GL}(n,\mathbb F)$ with $B=(L\otimes R\otimes S\otimes T)\cdot A$, that is,
--   $$
--   b_{i,j,k,\ell}=\sum_{i',j',k',\ell'} L_{ii'}\,R_{jj'}\,S_{kk'}\,T_{\ell\ell'}\,a_{i',j',k',\ell'}\qquad\text{for all }i,j,k,\ell.
--   $$
--   This is the isomorphism problem of $U\otimes V\otimes W\otimes X$ solved on average in Theorem 1.3.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §4.1, p.25 (PDF p.27); Theorem 1.3, p.6 (PDF p.8)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI.Supplement

/-- **4-way arrays**, `Tensor4 K n = (Fin n → Fin n → Fin n → Fin n → K)`, `A i j k l = a_{i,j,k,ℓ}`.

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), §4.1, p.25 (PDF p.27): "A is represented by a 4-way array A = (a_{i,j,k,ℓ}) ∈
F_q^n ⊗ F_q^n ⊗ F_q^n ⊗ F_q^n". -/
abbrev Tensor4 (K : Type*) (n : ℕ) := Fin n → Fin n → Fin n → Fin n → K

/-- **Isomorphism of 4-tensors under `GL(n, q)^4`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.3, p.6 (PDF p.8) and §4.1, p.25 (PDF p.27): "The goal is to determine whether
there exist invertible matrices L, R, S, T ∈ GL(n, q) such that: B = (L ⊗ R ⊗ S ⊗ T) · A."

`TensorIso4 A B`: there are invertible `L, R, S, T` with
`b_{i,j,k,ℓ} = Σ_{i',j',k',ℓ'} L_{i i'} R_{j j'} S_{k k'} T_{ℓ ℓ'} a_{i',j',k',ℓ'}`.

**Formalization Note.** The action is the four-factor version of the §2.3 convention (p.15, PDF p.17)
for 3-way arrays. -/
def TensorIso4 {K : Type*} [Field K] {n : ℕ} (A B : Tensor4 K n) : Prop :=
  ∃ L R S T : GL (Fin n) K, ∀ i j k l : Fin n,
    B i j k l = ∑ i' : Fin n, ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n,
      (L : Matrix (Fin n) (Fin n) K) i i' * (R : Matrix (Fin n) (Fin n) K) j j' *
        (S : Matrix (Fin n) (Fin n) K) k k' * (T : Matrix (Fin n) (Fin n) K) l l' * A i' j' k' l'

end AvgCaseTI.Supplement


