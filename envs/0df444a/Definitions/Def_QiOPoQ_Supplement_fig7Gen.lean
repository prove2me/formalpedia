-- Prove2me | Definitions.Def_QiOPoQ_Supplement_fig7Gen
-- name    : QiOPoQ_Supplement_fig7Gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:52:37.371032+00:00
-- url     : https://prove2.me/theorems/fb7598ce-00c9-4b58-a8de-e283bdd8a2d6
-- title:
--   Figure 7: Gen of the privately verifiable, blind verification protocol
-- statement:
--   Gen$(1^\lambda,C)$ of Figure 7. It samples independent uniform mask bits $b_{i,j}$ ($i\in[\mathrm{rows}],j\in[\mathrm{cols}]$) and independent uniform planted locations $j^*_i\leftarrow[\mathrm{cols}]$, and computes with independent coins
--
--   $$\hat C_{i,j}\leftarrow\begin{cases}\mathrm{qiO}(1^\lambda,X_{b_{i,j}}),& j\ne j^*_i,\\ \mathrm{qiO}(1^\lambda,X_{b_{i,j}}\circ C),& j=j^*_i.\end{cases}$$
--
--   The challenge is $(\hat C_{i,j})_{i,j}$ and the private state is $(J^*,b)$ with $J^*=\{(i,j^*_i)\}$.
--
--   **Formalization Note** The draws are, in order, the mask bits, the planted locations (each uniform in $[\mathrm{cols}]$ exactly) and the tapes; entries are indexed row-major from $0$. `fig7Rad` lists the ranges of the draws.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 7, p.23

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

/-- The ranges of the uniform draws of Figure 7's Gen on `(1^λ, C)`: `rows·cols` mask bits, then
`rows` planted locations in `[cols]`, then `rows·cols` obfuscation tapes of `cvqcBlock` bits. -/
def fig7Rad (Obf : UPPT) (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (rows cols : ℕ → ℕ) (n : ℕ)
    (C : Circ G) : List ℕ :=
  List.replicate (rows n * cols n) 2 ++ List.replicate (rows n) (cols n) ++
    List.replicate (rows n * cols n * cvqcBlock Obf Xp n C) 2

/-- **Figure 7, Gen.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Figure 7,
p.23: "Gen(1^λ, C): Sample independent uniform mask bits b = (b_{i,j})_{i∈[rows], j∈[cols]}.
Independently sample planted locations j*_i ← [cols] for every row i ∈ [rows], and let
J* = {(i, j*_i) : i ∈ [rows]}. For every i ∈ [rows] and j ∈ [cols], independently compute
Ĉ_{i,j} ← qiO(1^λ, X_{b_{i,j}}) if j ≠ j*_i, qiO(1^λ, X_{b_{i,j}} ∘ C) if j = j*_i. Output the
challenge chall = (Ĉ_{i,j})_{i,j} and retain the private state state = (J*, b)."

On draws `ω` (ranges `fig7Rad`): entry `k = i·cols + j` (row-major, `0`-based) has mask bit
`b_{i,j} = [ω_k = 1]`, row `i` has planted location `j*_i = ω_{rows·cols+i}`, and entry `k` is
obfuscated with the tape of bits `ω_{rows·cols+rows+k·B}, …` (`B = cvqcBlock`). The challenge is
`tup [Ĉ_0, …, Ĉ_{rows·cols−1}]`; the state is `(tup [j*_0, …] in unary, b_0 ⋯ b_{rows·cols−1})`.
`X_b` is `Xp b (shape C)` (Notation 5.1) and `X_b ∘ C` is `postX b C`. -/
def fig7Gen (Obf : UPPT) (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (rows cols : ℕ → ℕ) (n : ℕ)
    (C : Circ G) (ω : List ℕ) : Str × Str :=
  let R := rows n
  let K := cols n
  let B := cvqcBlock Obf Xp n C
  let mask : ℕ → Bool := fun k => decide (ω.getD k 0 = 1)
  let jstar : ℕ → ℕ := fun i => ω.getD (R * K + i) 0
  let tape : ℕ → Str := fun k => List.ofFn fun u : Fin B => decide (ω.getD (R * K + R + k * B + u.val) 0 = 1)
  let circ : ℕ → Circ G := fun k =>
    if k % K = jstar (k / K) then postX (mask k) C else Xp (mask k) (shape C)
  (tup (List.ofFn fun k : Fin (R * K) => Obf.runWith (pair (unary n) (encCirc (circ k.val))) (tape k.val)),
    pair (tup (List.ofFn fun i : Fin R => encNat (jstar i.val))) (List.ofFn fun k : Fin (R * K) => mask k.val))

end QiOPoQ.Supplement


