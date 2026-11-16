-- Prove2me | Definitions.Def_QiOPoQ_Supplement_refExpect
-- name    : QiOPoQ_Supplement_refExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:09:29.686361+00:00
-- url     : https://prove2.me/theorems/088187fa-c7ca-4d47-ab38-8ccc71d63cbb
-- title:
--   Definition 6.4: the reference distribution of an ancilla-free circuit
-- statement:
--   For an $m$-gate, $n$-qubit circuit $C$ with $m\ge1$: set $M_m:=mN(\lambda,n,2s+1)+(m-1)N(\lambda,n,2s)$, sample independent $L,R\leftarrow\mathcal C_{n,s}$ and $D\leftarrow\mathcal E_{L^\dagger\|C\|R,M_m}$, parse $D=D_1\|\cdots\|D_{2m-1}$ with $|D_{2i-1}|=N(\lambda,n,2s+1)$ and $|D_{2i}|=N(\lambda,n,2s)$, and output
--
--   $$\mathrm{RIO}(1^\lambda,L)\,\|\,\mathrm{Encode}(1^\lambda,D_1)\,\|\cdots\|\,\mathrm{Encode}(1^\lambda,D_{2m-1})\,\|\,\mathrm{RIO}(1^\lambda,R^\dagger)$$
--
--   with fresh coins for each call. `refExpect` is the expectation of a function of the output description.
--
--   **Formalization Note** The output pieces are read as ancilla-free $n$-qubit circuits and concatenated; if a piece describes no such circuit the output is the empty string.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 6.4, p.31

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_Supplement_Placement
import Definitions.Def_QiOPoQ_Supplement_avgRand
import Definitions.Def_QiOPoQ_Supplement_expectRuns

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

/-- **Definition 6.4 (Reference distribution for an ancilla-free circuit).** Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Definition 6.4, p.31: "For an m-gate, n-qubit circuit C with
m ≥ 1, define its reference distribution as follows. Set M_m := mN(λ, n, 2s + 1) +
(m − 1)N(λ, n, 2s), sample independent L, R ← C_{n,s}, and then sample D ← E_{L†∥C∥R,M_m}. Parse
D as D_1∥ · · · ∥D_{2m−1}, where |D_{2i−1}| = N(λ, n, 2s + 1) for 1 ≤ i ≤ m and
|D_{2i}| = N(λ, n, 2s) for 1 ≤ i < m. Output RIO(1^λ, L)∥Encode(1^λ, D_1)∥ · · · ∥
Encode(1^λ, D_{2m−1})∥RIO(1^λ, R†)."

`refExpect … λ n C g` is `E[g(output)]`, `s = s(λ, n)`, with fresh independent coins for each call
of RIO and Encode; the output is the description of the concatenation of the circuits they output
(each read as an ancilla-free `n`-qubit circuit; the empty string if one is not).

**Formalization Note.** Used only for `m ≥ 1` (Assumption 6.5). -/
noncomputable def refExpect (G : GateSet) (RIO Enc : UPPT) (s : ℕ → ℕ → ℕ) (N : ℕ → ℕ → ℕ → ℕ)
    (l n : ℕ) (C : List (Placement G n)) (g : Str → ℝ) : ℝ :=
  let m := C.length
  let S := s l n
  let N₁ := N l n (2 * S + 1)
  let N₂ := N l n (2 * S)
  let enc : List (Placement G n) → Str := fun gs => pair (unary l) (encCirc (afCirc n gs))
  avgRand G n S fun L => avgRand G n S fun R =>
    avgEquiv G n (m * N₁ + (m - 1) * N₂) (afDagger L ++ C ++ R) fun Dg =>
      expectRuns ((RIO, enc L) :: (splitLens (blockLens m N₁ N₂) Dg).map (fun b => (Enc, enc b)) ++
          [(RIO, enc (afDagger R))])
        fun outs => g (concatDecoded G n outs)

end QiOPoQ.Supplement


