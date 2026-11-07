-- Prove2me | Definitions.Def_QiOPoQ_IsObfCorrect
-- name    : QiOPoQ_IsObfCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:18.27225+00:00
-- url     : https://prove2.me/theorems/1d62b182-e0ec-4f99-8e13-0f735567f636
-- title:
--   Definition 3.1: obfuscator for $\mathcal C_{\mathsf{BQP}}$, correctness
-- statement:
--   A classical PPT algorithm Obf, on input $(1^\lambda,C)$, is an **obfuscator** for $\mathcal C_{\mathsf{BQP}}$ if for every family $\{C_\lambda\}$ in the class there is a negligible $\mu$ such that for every $\lambda$, with probability at least $1-\mu(\lambda)$ over the coins of Obf, the output is the description of a circuit $\hat C$ with the same numbers of input and output qubits as $C_\lambda$ and
--
--   $$
--   \|\hat C-C_\lambda\|_\diamond\le\mu(\lambda).
--   $$
--
--   **Formalization Note** "negl" is per family, as in the class itself. An output that describes no circuit counts as a failure of correctness.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.1, p.14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_InCBQP
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_UPPT

set_option autoImplicit false

namespace QiOPoQ

open QAdvFew.PoQOracle QAlgorithms.Complexity

variable {G : GateSet}

open Classical in
/-- **Definition 3.1 (Quantum circuit obfuscator), correctness, for C_BQP.** Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.1, p.14: "An obfuscator for C is a PPT
algorithm Obf that, on input (1^λ, C) with C ∈ C_λ, outputs a circuit Ĉ ← Obf(1^λ, C). Further,
it must satisfy the following correctness guarantee. Correctness: For every λ ∈ N and every
C ∈ C_λ, Pr_{Ĉ←Obf(1^λ,C)}[∥Ĉ − C∥⋄ ≤ negl(λ)] ≥ 1 − negl(λ)."

`Obf` is a classical PPT algorithm (footnote 11) on `pair (unary λ) (encCirc C)`; for every
family in C_BQP there is a negligible `μ` such that, with probability at least `1 − μ(λ)`, the
output describes a circuit `Ĉ` over `G` with the same numbers of input and output qubits as
`C_λ` and `∥Ĉ − C_λ∥⋄ ≤ μ(λ)`.

**Formalization Note.** "negl(λ)" is read per family (one `μ` per family `{C_λ}` in C_BQP, see
`InCBQP`). An output that is not a circuit description counts as a failure. -/
def IsObfCorrect (G : GateSet) (Obf : UPPT) : Prop :=
  ∀ Cf : ℕ → Circ G, InCBQP Cf → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
    1 - μ n ≤ Obf.expect (pair (unary n) (encCirc (Cf n))) fun s =>
      if ∃ D : Circ G, decCirc G s = some D ∧ D.nin = (Cf n).nin ∧
          D.out.length = (Cf n).out.length ∧ circDist D (Cf n) ≤ μ n then 1 else 0

end QiOPoQ


