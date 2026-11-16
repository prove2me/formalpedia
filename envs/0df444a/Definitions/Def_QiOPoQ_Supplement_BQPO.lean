-- Prove2me | Definitions.Def_QiOPoQ_Supplement_BQPO
-- name    : QiOPoQ_Supplement_BQPO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:57:27.813209+00:00
-- url     : https://prove2.me/theorems/bb367a8c-f589-4fa1-9ff4-4f00c94fd0a3
-- title:
--   The relativized class $\mathsf{BQP}^O$ over a gate set
-- statement:
--   A language $L$ is in $\mathsf{BQP}^O$ if there is a uniformly generated family of polynomial-size oracle circuits $A_n$ ($n$ input wires, one output wire; one deterministic polynomial-time generator from $1^n$) such that, run relative to $O$ on $x\in\{0,1\}^n$, $A_n$ outputs $1$ with probability at least $2/3$ if $x\in L$ and at most $1/3$ if $x\notin L$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 5.3, p.25

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_Supplement_ochan

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

/-- **The class `BQP^O`** over the gate set `G` (Gheorghiu, Gupte, Havlíček, Liu,
arXiv:2609.40289, sha256 fe2f9210…, Theorem 5.3, p.25; standard relativized class): `L ∈ BQP^O` if
a uniformly generated family of polynomial-size oracle circuits `A_n` (one generator computing
`A_n` from `1^n` in deterministic polynomial time; `n` input wires, one output wire), run relative
to `O` on `x ∈ {0,1}^n`, outputs `1` with probability `≥ 2/3` for `x ∈ L` and `≤ 1/3` for `x ∉ L`.
-/
def BQPO (G : GateSet) (O : Str → Bool) : Set (Set Str) :=
  {L | ∃ A : ℕ → OCirc G,
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n, g (unary n) = oEncCirc (A n)) ∧
    (∀ n, (A n).nin = n) ∧ (∀ n, (A n).out.length = 1) ∧
    ∀ x : Str, (x ∈ L → (2 / 3 : ℝ) ≤ oRunProb O (A x.length) x [true]) ∧
      (x ∉ L → oRunProb O (A x.length) x [true] ≤ (1 / 3 : ℝ))}

end QiOPoQ.Supplement


