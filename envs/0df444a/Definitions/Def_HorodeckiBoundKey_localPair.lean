-- Prove2me | Definitions.Def_HorodeckiBoundKey_localPair
-- name    : HorodeckiBoundKey_localPair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:36.370797+00:00
-- url     : https://prove2.me/theorems/90c95aef-68a0-4500-8787-b5f8eebdad77
-- title:
--   Product $F_A\otimes F_B$ of local operators acting on $n$ copies
-- statement:
--   Let $F_A$ be an operator from Alice's part of $n$ copies of a key-and-shield state, i.e. her $n$ key qubits and her $n$ shields, to one key qubit and a shield $S'$; and let $F_B$ be an operator of the same kind for Bob, with output shield $T'$. Their product acts from $n$ copies (in the layout of $\rho^{\otimes n}$ above) to one key pair with shields $S'$, $T'$:
--   $$
--   (F_A\otimes F_B)\big((a,s',t'),(x,s,t)\big) = F_A\big((a^A,s'),(x^A,s)\big)\; F_B\big((a^B,t'),(x^B,t)\big).
--   $$
--
--   It is used to describe local filtering, in particular the successful branch of the recurrence protocol (p.3).
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3 ("apply the recurrence distillation protocol of [23] without the twirling step")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3 ("apply the
recurrence distillation protocol … without the twirling step"): the product `F_A ⊗ F_B` of a
local operator `F_A` of Alice and a local operator `F_B` of Bob, acting on `n` copies of a
key-and-shield state (the layout of `keyPower`) and producing one key pair with shields
`S′`, `T′`.

Alice's input is her `n` key qubits and her `n` shields, `(Fin n → Fin 2) × (Fin n → S)`; her
output is one key qubit and a shield, `Fin 2 × S′`. Bob's likewise. The entry is
`(F_A ⊗ F_B)((a, s′, t′), (x, s, t)) = F_A((a₁, s′), (x·₁, s)) · F_B((a₂, t′), (x·₂, t))`.

**Formalization Note.** Output key pair `a : Key 2` has Alice's bit `a.1` and Bob's `a.2`. -/
def localPair {S T S' T' : Type*} {n : ℕ}
    (FA : Matrix (Fin 2 × S') ((Fin n → Fin 2) × (Fin n → S)) ℂ)
    (FB : Matrix (Fin 2 × T') ((Fin n → Fin 2) × (Fin n → T)) ℂ) :
    Matrix (Key 2 × (S' × T')) ((Fin n → Key 2) × ((Fin n → S) × (Fin n → T))) ℂ :=
  fun a x => FA (a.1.1, a.2.1) (fun i => (x.1 i).1, x.2.1) *
    FB (a.1.2, a.2.2) (fun i => (x.1 i).2, x.2.2)

end HorodeckiBoundKey


