-- Prove2me | Definitions.Def_GroupIsoPoly_encTransInst
-- name    : GroupIsoPoly_encTransInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:20.885402+00:00
-- url     : https://prove2.me/theorems/72606208-79ea-4195-a60a-fb4fb54bdcbd
-- title:
--   Binary input of complete 3-tensor isomorphism
-- statement:
--   An instance of Theorem 8.1 consists of a presented field $\mathbb F_q$, dimensions $n_1,n_2,n_3$, tensors $T,T'\in U_1\otimes U_2\otimes U_3$ and a list of generators $(g_1,g_2,g_3)$ of $\Gamma_{\mathrm{in}}$. Its **code** is $n_1,n_2,n_3$, the field, the entries of $T$ and $T'$, the number of generators, and each generator as the entries of its three matrices. Its length is the paper's $\mathrm{InSize}$.
--
--   An element of $\mathrm{GL}(U_1)\times\mathrm{GL}(U_2)\times\mathrm{GL}(U_3)$ in an answer is written as the coordinates of its three matrices (`gl3Nats`).
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 8.1, p.71 (PDF p.75)

import Mathlib
import Definitions.Def_GroupIsoPoly_enc3TI
import Definitions.Def_GroupIsoPoly_transIn

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)
open AvgCaseTI (FieldPres)

/-- An element `(g₁, g₂, g₃)` of `GL(U₁) × GL(U₂) × GL(U₃)`, written as the coordinates of the
entries of `g₁`, `g₂`, `g₃`. -/
noncomputable def gl3Nats (P : FieldPres) {n₁ n₂ n₃ : ℕ} (g : GL3 P.F n₁ n₂ n₃) : List ℕ :=
  matNats P (g.1 : Matrix (Fin n₁) (Fin n₁) P.F) ++ matNats P (g.2.1 : Matrix (Fin n₂) (Fin n₂) P.F) ++
    matNats P (g.2.2 : Matrix (Fin n₃) (Fin n₃) P.F)

/-- **The binary input of complete 3-tensor isomorphism** (Theorem 8.1).

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 8.1, p.71 (PDF p.75): "Given T, T′ ∈
U1 ⊗Fq U2 ⊗Fq U3 and generators of Γin ≤ ∏_{i=1}^3 GL(Ui) … where InSize is the total input bit
length."

The code is `n₁`, `n₂`, `n₃`, the field, the entries of `T` and `T′`, the number of generators, then
each generator by the coordinates of its three matrices. Its length is `InSize`. -/
noncomputable def encTransInst (P : FieldPres) (n₁ n₂ n₃ : ℕ) (T T' : Array3 P.F n₁ n₂ n₃)
    (gens : List (GL3 P.F n₁ n₂ n₃)) : List Bool :=
  encodeNat n₁ ++ encodeNat n₂ ++ encodeNat n₃ ++ encField P ++
    ((arrayNats P T).map encodeNat).flatten ++ ((arrayNats P T').map encodeNat).flatten ++
    encodeNat gens.length ++ (gens.map fun g => ((gl3Nats P g).map encodeNat).flatten).flatten

end GroupIsoPoly


