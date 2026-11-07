-- Prove2me | Definitions.Def_QiOPoQ_qptExpect
-- name    : QiOPoQ_qptExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:42.435978+00:00
-- url     : https://prove2.me/theorems/fe6c6bad-8a45-43a8-a4cc-b627e8fc3457
-- title:
--   Quantum polynomial-time algorithms with classical input and output
-- statement:
--   A quantum polynomial-time algorithm that returns a classical response is described through the output $s$ of a classical polynomial-time generator on its input. The string $s$ is a tuple of circuit descriptions; each circuit is run on the all-zero state, its output register is measured in the computational basis, and the response is the concatenation of the outcomes in order. If $s$ is not a tuple of circuit descriptions, the response is the empty string. `qptExpect` is the expectation of a function of the response under this law.
--
--   **Formalization Note** This is the standard model "uniform classical generator of polynomial-size circuits": by the unary description, the circuits are polynomial-size. A list of circuits run side by side is one circuit, so allowing a list adds nothing.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3, p.13; Definition 3.3, p.14

import Mathlib
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_encCirc

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

variable {G : GateSet}

/-- `E[g(z)]` for `z` the measured output register of `C` run on the all-zero state
`|0^{n_in}⟩_in ⊗ |0^{n_anc}⟩_anc`. -/
noncomputable def zeroRunExpect (C : Circ G) (g : Str → ℝ) : ℝ :=
  ∑ z : Fin C.out.length → Bool, outProb C (fun _ => false) z * g (List.ofFn z)

/-- Run the circuits of a list independently on `|0…0⟩`, measure each output register, and
concatenate the outcomes in list order: `E[g(z₁ ++ ⋯ ++ z_k)]`. -/
noncomputable def runListExpect : List (Circ G) → (Str → ℝ) → ℝ
  | [], g => g []
  | C :: Cs, g => zeroRunExpect C fun z => runListExpect Cs fun rest => g (z ++ rest)

/-- **A quantum polynomial-time algorithm with classical input and output** (Gheorghiu, Gupte,
Havlíček, Liu, arXiv:2609.40289, sha256 fe2f9210…, §3, p.13, "QPT"; Definition 3.3, p.14:
"Prove(1^λ, chall) → resp is a quantum polynomial-time prover that returns a classical
response"), given by the output `s` of its classical polynomial-time generator on the input:
`s` is a tuple of circuit descriptions over `G`; each circuit is run on `|0…0⟩` and its output
register measured; the response is the concatenation of the outcomes. `qptExpect G s g` is
`E[g(resp)]`. If `s` is not a tuple of circuit descriptions the response is the empty string.

**Formalization Note.** This is the standard model "a uniform classical polynomial-time
generator of polynomial-size circuits"; the input is hardwired by the generator. A list of
circuits run side by side is one circuit, so allowing a list adds nothing. -/
noncomputable def qptExpect (G : GateSet) (s : Str) (g : Str → ℝ) : ℝ :=
  match (untuple s).bind (fun l => l.mapM (decCirc G)) with
  | some Cs => runListExpect Cs g
  | none => g []

end QiOPoQ


