-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsObfCorrectOn
-- name    : QiOPoQ_Supplement_IsObfCorrectOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:44:27.651399+00:00
-- url     : https://prove2.me/theorems/3487acd5-87e7-4faa-affc-283389733b00
-- title:
--   Definition 3.1: correctness of a quantum circuit obfuscator for a circuit class
-- statement:
--   Definition 3.1 for an arbitrary circuit class $\mathcal C$, given as a predicate on families $\lambda\mapsto C_\lambda$. A classical PPT algorithm Obf is a correct obfuscator for $\mathcal C$ if for every family $\{C_\lambda\}$ in $\mathcal C$ there is a negligible $\mu$ with
--
--   $$\Pr_{\hat C\leftarrow \mathrm{Obf}(1^\lambda,C_\lambda)}\big[\|\hat C-C_\lambda\|_\diamond\le\mu(\lambda)\big]\ \ge\ 1-\mu(\lambda)\qquad\text{for every }\lambda,$$
--
--   where an output that does not describe a circuit with the same numbers of input and output qubits as $C_\lambda$ counts as a failure.
--
--   Theorems 6.6 and 6.7 use it for ancilla-free unitary and tidy unitary families. **Formalization Note** For $\mathcal C=\mathcal C_{\mathsf{BQP}}$ it is, by definition, the published `QiOPoQ.IsObfCorrect`.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.1, p.14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_diamond
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_UPPT

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

variable {G : GateSet}

open Classical in
/-- **Definition 3.1 (Quantum circuit obfuscator), correctness, for a circuit class.**
Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit
Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.1, p.14: "Let C = {C_λ}λ∈N be a
class of quantum circuits. An obfuscator for C is a PPT algorithm Obf that, on input (1^λ, C)
with C ∈ C_λ, outputs a circuit Ĉ ← Obf(1^λ, C). … Correctness: For every λ ∈ N and every
C ∈ C_λ, Pr_{Ĉ←Obf(1^λ,C)}[∥Ĉ − C∥⋄ ≤ negl(λ)] ≥ 1 − negl(λ)."

The class is a predicate `cls` on circuit families `λ ↦ C_λ`. `Obf` is a classical PPT algorithm
(footnote 11) run on `(1^λ, C_λ)`; for every family in the class one negligible `μ` bounds both
the failure probability and the diamond distance; an output that does not describe a circuit with
`C_λ`'s numbers of input and output qubits is a failure.

**Formalization Note.** Same reading as the published `QiOPoQ.IsObfCorrect`, which is the
instance `cls = InCBQP` (definitionally). The classes of the paper contain only
polynomial-size families. -/
def IsObfCorrectOn (G : GateSet) (cls : (ℕ → Circ G) → Prop) (Obf : UPPT) : Prop :=
  ∀ Cf : ℕ → Circ G, cls Cf → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
    1 - μ n ≤ Obf.expect (pair (unary n) (encCirc (Cf n))) fun s =>
      if ∃ D : Circ G, decCirc G s = some D ∧ D.nin = (Cf n).nin ∧
          D.out.length = (Cf n).out.length ∧ circDist D (Cf n) ≤ μ n then 1 else 0

end QiOPoQ.Supplement


