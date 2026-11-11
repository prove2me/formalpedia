-- Prove2me | Definitions.Def_SparseTensorInj_Certify_EvenCertificate
-- name    : SparseTensorInj_Certify_EvenCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:37:19.399694+00:00
-- url     : https://prove2.me/theorems/c3a7a7e8-dbd4-4552-8b91-3b26f092f27c
-- title:
--   The balanced flattening $A(T)$ and the even-order certificate $\|A(T)\|_{\mathrm{op}}$ (Definition 37)
-- statement:
--   Let $k=2q$. The **balanced flattening** of an order-$2q$ tensor $T$ is the $n^q\times n^q$ matrix indexed by ordered $q$-tuples $i,j\in[n]^q$,
--   $$A(T)_{i,j}=T_{i_1,\dots,i_q,j_1,\dots,j_q}.$$
--   The **even-order certificate** is $u(T)=\|A(T)\|_{\mathrm{op}}$, the $\ell_2$ operator norm (largest singular value) of the flattening. Claim 38 shows $u(T)\ge\|T\|_{\mathrm{inj}}$ for symmetric $T$; Proposition 36 bounds it for random tensors.
--
--   **Formalization Note.** Ordered $q$-tuples are functions `Fin q → Fin n`; the concatenation $(i,j)$ is `Fin.append i j : Fin (q + q) → Fin n`, so the tensor has type `Tensor (q + q) n`.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 22, Definition 37 and Claim 38

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_Tensor

namespace SparseTensorInj.Certify

/-- The balanced flattening (Definition 37, p. 22) of an order-`2q` tensor: the `n^q × n^q`
matrix indexed by ordered `q`-tuples `i, j ∈ [n]^q`, `A(T)_{i,j} = T_{i_1, …, i_q, j_1, …, j_q}`. -/
def flattening {q n : ℕ} (T : Tensor (q + q) n) : Matrix (Fin q → Fin n) (Fin q → Fin n) ℝ :=
  fun i j => T (Fin.append i j)

/-- The even-order certificate (Definition 37 and Claim 38, p. 22): `u(T) = ‖A(T)‖_op`, the
`ℓ2` operator norm of the balanced flattening. -/
noncomputable def evenCert {q n : ℕ} (T : Tensor (q + q) n) : ℝ :=
  opNorm (flattening T)

end SparseTensorInj.Certify


