-- Prove2me | Definitions.Def_NondetConn_Supplement_ippc
-- name    : NondetConn_Supplement_ippc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:07:32.24007+00:00
-- url     : https://prove2.me/theorems/d4a6422c-4a4d-4cf8-9eb3-de3370d3a28e
-- title:
--   The function $\mathsf{IP\circ PC}_{n,r}$
-- statement:
--   Given $X,Y\in\{0,1\}^n$ and alternatingly owned permutations $A_1,\ldots,A_r,B_1,\ldots,B_r$ of $[n]$, define
--   $$
--   \mathsf{IP\circ PC}_{n,r}=\left\langle A_r\cdots A_1X,\,B_r\cdots B_1Y\right\rangle\pmod 2.
--   $$
--
--   Permutations act as permutation matrices: $(\sigma x)_j=x_{\sigma^{-1}(j)}$. This is the communication problem of Theorems 7.1 and C.1.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.1, pp.2–3 (PDF pp.4–5), and Theorem 7.1, p.22 (PDF p.24)

import Definitions.Def_NondetConn_Supplement_IPPCAliceInput
import Definitions.Def_NondetConn_Supplement_IPPCBobInput

set_option autoImplicit false

namespace NondetConn.Supplement

/-- The Boolean function `IP∘PC_{n,r}`. Alice supplies the odd-numbered permutation layers,
Bob supplies the even-numbered layers and `X,Y`, and the output is the binary inner product
`<A_r⋯A_1 X, B_r⋯B_1 Y>`.

The paper's `[n]={1,…,n}` is `Fin n`; a permutation matrix sends a vector `x` to
`j ↦ x(σ⁻¹(j))`. Lean layer index `i` represents paper layer `i+1`, so Alice owns
exactly the even-valued Lean indices. -/
def ippc (n r : ℕ) (alice : IPPCAliceInput n r) (bob : IPPCBobInput n r) : Bool :=
  let fullA : Fin r → Equiv.Perm (Fin n) :=
    fun i ↦ if Even i.val then alice.A i else bob.layers.A i
  let fullB : Fin r → Equiv.Perm (Fin n) :=
    fun i ↦ if Even i.val then alice.B i else bob.layers.B i
  let act (x : Fin n → Bool) (p : Equiv.Perm (Fin n)) : Fin n → Bool :=
    fun j ↦ x (p.symm j)
  let xFinal := (List.ofFn fullA).foldl act bob.vectors.1
  let yFinal := (List.ofFn fullB).foldl act bob.vectors.2
  decide (Odd ((Finset.univ.filter fun j ↦ xFinal j && yFinal j).card))

end NondetConn.Supplement


