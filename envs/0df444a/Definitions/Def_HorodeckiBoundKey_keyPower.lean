-- Prove2me | Definitions.Def_HorodeckiBoundKey_keyPower
-- name    : HorodeckiBoundKey_keyPower
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:47.670823+00:00
-- url     : https://prove2.me/theorems/b6217842-282a-4d7e-b4b6-08803f013ca4
-- title:
--   $n$ copies $\rho^{\otimes n}$ of a key-and-shield state, regrouped by register
-- statement:
--   Let $\rho$ be a state on $A B A' B'$ (key qubits $A$, $B$; shields $A'$, $B'$) and $n\ge 0$. The $n$-fold tensor power $\rho^{\otimes n}$ is written with its registers regrouped as (the $n$ key pairs) $\otimes$ (Alice's $n$ shields) $\otimes$ (Bob's $n$ shields):
--   $$
--   \rho^{\otimes n}\big((x,s,t),(y,u,v)\big) = \prod_{i=1}^{n}\rho\big((x_i,s_i,t_i),(y_i,u_i,v_i)\big),
--   $$
--   where $x_i = (x_i^A, x_i^B)$ is the $i$-th key pair. Alice holds $(x^A_1,\dots,x^A_n)$ and $s$, Bob holds $(x^B_1,\dots,x^B_n)$ and $t$.
--
--   This is the input of the recurrence step on $n$ copies (p.3, "Now, we take n copies").
--
--   **Formalization Note** The regrouping is a fixed permutation of tensor factors that keeps each register with its owner.
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3 ("Now, we take n copies")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3 ("Now, we take n
copies"): the `n`-fold tensor power `ρ^{⊗n}` of a state `ρ` on `A B A′ B′`, with its registers
regrouped as (the `n` key pairs) × ((Alice's `n` shields) × (Bob's `n` shields)):
`ρ^{⊗n}((x, s, t), (y, u, v)) = ∏ᵢ ρ((xᵢ, sᵢ, tᵢ), (yᵢ, uᵢ, vᵢ))`.

**Formalization Note.** Copy `i` of the key pair is `x i : Key 2 = Fin 2 × Fin 2`, so Alice's
`n` key qubits are `fun i => (x i).1` and Bob's are `fun i => (x i).2`. The regrouping is a
fixed relabelling of the tensor factors; no party's register moves to the other party. -/
def keyPower {S T : Type*} (ρ : Op (Key 2 × (S × T))) (n : ℕ) :
    Op ((Fin n → Key 2) × ((Fin n → S) × (Fin n → T))) :=
  fun x y => ∏ i, ρ (x.1 i, (x.2.1 i, x.2.2 i)) (y.1 i, (y.2.1 i, y.2.2 i))

end HorodeckiBoundKey


