-- Prove2me | Definitions.Def_QiOPoQ_Supplement_fig9Gen
-- name    : QiOPoQ_Supplement_fig9Gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:54:26.559252+00:00
-- url     : https://prove2.me/theorems/549b9025-85e7-4d9f-b9aa-d89b7cc5272d
-- title:
--   Figure 9: Gen of the publicly verifiable verification protocol
-- statement:
--   Gen$(1^\lambda,C)$ of Figure 9 samples $b,c\in\{0,1\}^\lambda$ uniformly and independently, sets $s_0:=b$, $s_1:=b\oplus c$, and computes with independent coins
--
--   $$\hat C_i\leftarrow\begin{cases}\mathrm{qiO}(1^\lambda,X_{b_i}),& c_i=0,\\ \mathrm{qiO}(1^\lambda,X_{b_i}\circ C),& c_i=1,\end{cases}\qquad y_0:=g_\lambda(s_0),\ y_1:=g_\lambda(s_1).$$
--
--   The challenge is $((\hat C_i)_{i\in[\lambda]},y_0,y_1)$ and the state is empty.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 9, p.28

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_Supplement_postX
import Definitions.Def_QiOPoQ_Supplement_cvqcBlock

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

variable {G : GateSet}

/-- The ranges of the uniform draws of Figure 9's Gen on `(1^λ, C)`: `λ` bits `b`, `λ` bits `c`,
then `λ` obfuscation tapes of `cvqcBlock` bits. -/
def fig9Rad (Obf : UPPT) (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (n : ℕ) (C : Circ G) : List ℕ :=
  List.replicate (n + n + n * cvqcBlock Obf Xp n C) 2

/-- **Figure 9, Gen.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Figure 9,
p.28: "Gen(1^λ, C): Sample b = (b_i)_{i∈[λ]} and c = (c_i)_{i∈[λ]} independently and uniformly from
{0, 1}^λ. Let s_0 := b and s_1 := b ⊕ c. For every i ∈ [λ], independently generate
Ĉ_i ← qiO(1^λ, X_{b_i}) if c_i = 0, qiO(1^λ, X_{b_i} ∘ C) if c_i = 1. Set y_0 := g_λ(s_0) and
y_1 := g_λ(s_1). Output chall := ((Ĉ_i)_{i∈[λ]}, y_0, y_1)."

On bits `ω` (ranges `fig9Rad`): `b_i = ω_i`, `c_i = ω_{λ+i}`, entry `i` obfuscated with the tape
`ω_{2λ+i·B}, …` (`B = cvqcBlock`). The challenge is `tup [Ĉ_0, …, Ĉ_{λ−1}, y_0, y_1]`; the state is
empty (Definition 3.6: "A setup algorithm that returns only a public challenge fits this syntax by
taking state to be the empty string"). -/
def fig9Gen (Obf : UPPT) (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (g : Str → Str) (n : ℕ) (C : Circ G)
    (ω : List ℕ) : Str × Str :=
  let B := cvqcBlock Obf Xp n C
  let bit : ℕ → Bool := fun k => decide (ω.getD k 0 = 1)
  let s0 : Str := List.ofFn fun i : Fin n => bit i.val
  let s1 : Str := List.ofFn fun i : Fin n => bit i.val ^^ bit (n + i.val)
  let circ : ℕ → Circ G := fun i => if bit (n + i) then postX (bit i) C else Xp (bit i) (shape C)
  let tape : ℕ → Str := fun i => List.ofFn fun u : Fin B => bit (n + n + i * B + u.val)
  (tup (List.ofFn (fun i : Fin n => Obf.runWith (pair (unary n) (encCirc (circ i.val))) (tape i.val)) ++
      [g s0, g s1]), [])

end QiOPoQ.Supplement


