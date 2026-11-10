-- Prove2me | Definitions.Def_PPSLattice_gadget
-- name    : PPSLattice_gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:12.862211+00:00
-- url     : https://prove2.me/theorems/0ca953c9-e706-49f1-a05f-f66a040854ef
-- title:
--   Gadget matrix $\mathbf G=\mathbf I_n\otimes\mathbf g^\top$
-- statement:
--   With $k=\lceil\log_2q\rceil$ and $\mathbf g=(1,2,4,\dots,2^{k-1})$, the gadget matrix $\mathbf G\in\mathbb Z_q^{n\times m}$ has, in column $j=ik+t$ ($i<n$, $t<k$), the entry $2^t$ in row $i$ and zeros elsewhere; the columns $j\ge nk$, present when $m>n\lceil\log q\rceil$, are zero.
--
--   **Formalization Note** The paper defines $\mathbf G$ for $m=n\lceil\log q\rceil$ and uses it with $m\ge n\lceil\log q\rceil$, padding with zeros.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Gadget Matrix, p.16

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The **gadget matrix** `G = I_n ⊗ g^⊤ ∈ Z_q^{n×m}`, `g = (1, 2, 4, …, 2^{⌈log q⌉−1})`: with
`k = ⌈log₂ q⌉`, column `j = i·k + t` (`t < k`, `i < n`) has the entry `2^t` in row `i` and zeros elsewhere;
the columns `j ≥ n·k` (present when `m > n⌈log q⌉`) are zero.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Gadget Matrix, p.16 ("G = (I_n ⊗ g^⊤), g = [1 2 2² … 2^{⌈log q⌉−1}]^⊤"); Homomorphic
Computation, p.16 ("m ≥ n⌈log q⌉").

**Formalization Note.** The paper defines `G` for `m = n⌈log q⌉` and uses it with `m ≥ n⌈log q⌉`;
the extra columns are zero, matching "Output of G^{-1} is padded with 0s to match the dimensions". -/
def gadget (q n m : ℕ) : Matrix (Fin n) (Fin m) (ZMod q) :=
  Matrix.of fun i j =>
    if j.val < Nat.clog 2 q * n ∧ j.val / Nat.clog 2 q = i.val then
      (2 : ZMod q) ^ (j.val % Nat.clog 2 q)
    else 0

end PPSLattice


