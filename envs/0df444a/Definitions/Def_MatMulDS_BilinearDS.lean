-- Prove2me | Definitions.Def_MatMulDS_BilinearDS
-- name    : MatMulDS_BilinearDS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:07.67521+00:00
-- url     : https://prove2.me/theorems/0ca2cef2-09f1-4e18-b475-2245b3221487
-- title:
--   Bilinear data structure
-- statement:
--   A **bilinear data structure** for multiplying $N\times D$ and $D\times N$ matrices consists of linear encoding circuits $\Phi,\Psi$ of $A,B$; a positive number $P_{\mathrm{pre}}$ of precomputed products $C_{\mathrm{pre}}[p]=\Phi(A)[a_p]\cdot\Psi(B)[b_p]$; a storage circuit $C_{\mathrm{box}}$, linear in those products; and for each query $(I,J)\in[N]^2$, linear circuits $C^A_{\mathrm{new}},C^B_{\mathrm{new}}$ of the outputs of $\Phi(A),\Psi(B)$ and a linear combination $C_{\mathrm{rel}}$ of outputs of $C_{\mathrm{box}}$. They satisfy, for all $A,B,I,J$,
--   $$(AB)[I,J]=C_{\mathrm{rel}}(C_{\mathrm{box}}(C_{\mathrm{pre}}))+\sum_{p=1}^{P_{\mathrm{new}}}C^A_{\mathrm{new}}(\Phi(A))[p]\cdot C^B_{\mathrm{new}}(\Psi(B))[p].$$
--
--   Here $T_{\mathrm{enc}}$ is the sum of the sizes of $\Phi,\Psi$; $T_{\mathrm{box}}$ is the size of $C_{\mathrm{box}}$; $P_{\mathrm{new}}$ is the maximum over queries of the sum of the sizes of $C^A_{\mathrm{new}},C^B_{\mathrm{new}}$; $T_{\mathrm{rel}}$ is the maximum over queries of the number of outputs of $C_{\mathrm{box}}$ combined. The times are $T_{\mathrm{pre}}=T_{\mathrm{enc}}+P_{\mathrm{pre}}+T_{\mathrm{box}}$ and $T_{\mathrm{query}}=P_{\mathrm{new}}+T_{\mathrm{rel}}$.
--
--   **Formalization Note** $C_{\mathrm{rel}}$ is a sparse linear form, a list of (coefficient, index) pairs, whose length is the charge $T_{\mathrm{rel}}$. Correctness on all matrices over a field of characteristic zero is the same as correctness on indeterminates.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Definition 4.1, pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_MatMulDS_LinCircuit

set_option autoImplicit false

namespace MatMulDS

/-- **Bilinear data structure** for multiplying `N × D` and `D × N` matrices (Definition 4.1, STOC 2027
submission, held file sha256 6c5a1c16…, pp.15–16).
* `Φ`, `Ψ`: the linear encoding circuits, fed `A` and `B` in row-major order.
* `Ppre > 0`, `a`, `b`: the precomputed products `Cpre[p] = Φ(A)[a p] · Ψ(B)[b p]` of (4.1).
* `Cbox`: the storage circuit, whose outputs are the stored values.
* `CAnew I J`, `CBnew I J`: the decoding circuits of the query `(I, J)`, fed the outputs of `Φ(A)` and `Ψ(B)`.
* `Crel I J`: the linear combination of outputs of `Cbox` of the query `(I, J)`, as a list of pairs
  (coefficient, index of an output of `Cbox`).
* `correct`: (4.3) for all `A`, `B` and all queries.

**Formalization Note.**
* The paper's `Crel` is "a linear circuit", charged only "the number of outputs of Cbox that Crel combines",
  and "Trel also bounds the maximum circuit size of Crel" (p.16). A sparse linear form is that object, and
  its length is that charge.
* The paper's `A`, `B` are matrices of indeterminates. Correctness on all matrices over `F` is the same
  statement, since a field of characteristic zero is infinite and the identity is a polynomial one.
* `Ppre` is "a positive integer" (p.15). Keeping this makes a structure without products carry a dummy one. -/
structure BilinearDS (F : Type) [Field F] (N D : ℕ) where
  Φ : LinCircuit F
  Ψ : LinCircuit F
  Ppre : ℕ
  Ppre_pos : 0 < Ppre
  a : Fin Ppre → ℕ
  b : Fin Ppre → ℕ
  Cbox : LinCircuit F
  CAnew : Fin N → Fin N → LinCircuit F
  CBnew : Fin N → Fin N → LinCircuit F
  Crel : Fin N → Fin N → List (F × ℕ)
  correct : ∀ (A : Matrix (Fin N) (Fin D) F) (B : Matrix (Fin D) (Fin N) F) (I J : Fin N),
    (A * B) I J =
      ((Crel I J).map fun t =>
        t.1 * Cbox.out (productInput Φ Ψ a b (matInput A) (matInput B)) t.2).sum +
      ∑ p ∈ Finset.range ((Finset.univ : Finset (Fin N × Fin N)).sup fun q =>
          (CAnew q.1 q.2).size + (CBnew q.1 q.2).size),
        (CAnew I J).out (Φ.out (matInput A)) p * (CBnew I J).out (Ψ.out (matInput B)) p

namespace BilinearDS

variable {F : Type} [Field F] {N D : ℕ} (S : BilinearDS F N D)

/-- The encoding complexity `Tenc`: the sum of the sizes of `Φ` and `Ψ`. -/
def Tenc : ℕ := S.Φ.size + S.Ψ.size

/-- The storage complexity `Tbox`: the size of `Cbox`. -/
def Tbox : ℕ := S.Cbox.size

/-- The number of new products `Pnew`: the maximum over all queries of the sum of the sizes of `CAnew` and
`CBnew`. -/
def Pnew : ℕ :=
  (Finset.univ : Finset (Fin N × Fin N)).sup fun q => (S.CAnew q.1 q.2).size + (S.CBnew q.1 q.2).size

/-- The relevant contribution `Trel`: the maximum over all queries of the number of outputs of `Cbox` that
`Crel` combines. -/
def Trel : ℕ := (Finset.univ : Finset (Fin N × Fin N)).sup fun q => (S.Crel q.1 q.2).length

/-- The preprocessing time, (4.2): `Tpre = Tenc + Ppre + Tbox`. -/
def Tpre : ℕ := S.Tenc + S.Ppre + S.Tbox

/-- The query time, (4.2): `Tquery = Pnew + Trel`. -/
def Tquery : ℕ := S.Pnew + S.Trel

/-- The size of the circuits of one query. -/
def querySize (I J : Fin N) : ℕ := (S.CAnew I J).size + (S.CBnew I J).size + (S.Crel I J).length

end BilinearDS

end MatMulDS


