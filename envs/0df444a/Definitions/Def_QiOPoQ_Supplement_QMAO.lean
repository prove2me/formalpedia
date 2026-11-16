-- Prove2me | Definitions.Def_QiOPoQ_Supplement_QMAO
-- name    : QiOPoQ_Supplement_QMAO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:58:14.411858+00:00
-- url     : https://prove2.me/theorems/186cdff8-8bab-40f0-abad-6a2787f25371
-- title:
--   The relativized class $\mathsf{QMA}^O$ over a gate set
-- statement:
--   A language $L$ is in $\mathsf{QMA}^O$ if there are a polynomial witness length $w$ and a uniformly generated family of polynomial-size oracle verifier circuits $V_n$ on $n+w(n)$ input wires with one output wire such that: if $x\in L$, some normalized $w(|x|)$-qubit witness state makes $V_{|x|}$, run relative to $O$ on $|x\rangle$ and the witness, output $1$ with probability at least $2/3$; if $x\notin L$, every witness state is accepted with probability at most $1/3$.
--
--   **Formalization Note** The witness is a quantum state; pure states suffice, since acceptance is linear in the witness density matrix.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 5.3, p.25; Proposition 5.5, p.25

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_Supplement_ochan

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

variable {G : GateSet}

open Classical in
/-- The acceptance probability of a verifier `V` (input register of `n + w` wires) relative to
`O` on the instance `x` (first `n` input wires) and the pure witness state `ψ` on the last `w`
input wires: the probability that the output qubit is measured as `1`. -/
noncomputable def qmaAcc (O : Str → Bool) (V : OCirc G) (n w : ℕ) (x : Str)
    (ψ : (Fin w → Bool) → ℂ) : ℝ :=
  let v : (Fin (n + w) → Bool) → ℂ := fun y =>
    if ∀ i : Fin n, y (Fin.castAdd w i) = x.getD i.val false then ψ (fun j => y (Fin.natAdd n j))
    else 0
  (ochanAs O V (n + w) 1 (Matrix.vecMulVec v (star v)) (fun _ => true) (fun _ => true)).re

/-- **The class `QMA^O`** over the gate set `G` (Gheorghiu, Gupte, Havlíček, Liu,
arXiv:2609.40289, sha256 fe2f9210…, Theorem 5.3, p.25: "BQP^O = QMA^O"; Proposition 5.5, p.25:
"Fix a language in QMA^O and its uniform polynomial-size verifier"; standard relativized class):
`L ∈ QMA^O` if there are a polynomial witness length `w` and a uniformly generated family of
polynomial-size oracle verifier circuits `V_n` (`n + w(n)` input wires, one output wire) such that
for `x ∈ L` some normalized `w(|x|)`-qubit witness state is accepted with probability `≥ 2/3`, and
for `x ∉ L` every normalized witness state is accepted with probability `≤ 1/3`.

**Formalization Note.** The witness is a quantum state; pure states suffice, since the acceptance
probability is linear in the witness density matrix. -/
def QMAO (G : GateSet) (O : Str → Bool) : Set (Set Str) :=
  {L | ∃ (V : ℕ → OCirc G) (w : Polynomial ℕ),
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n, g (unary n) = oEncCirc (V n)) ∧
    (∀ n, (V n).nin = n + w.eval n) ∧ (∀ n, (V n).out.length = 1) ∧
    ∀ x : Str,
      (x ∈ L → ∃ ψ : (Fin (w.eval x.length) → Bool) → ℂ, ∑ j, Complex.normSq (ψ j) = 1 ∧
        (2 / 3 : ℝ) ≤ qmaAcc O (V x.length) x.length (w.eval x.length) x ψ) ∧
      (x ∉ L → ∀ ψ : (Fin (w.eval x.length) → Bool) → ℂ, ∑ j, Complex.normSq (ψ j) = 1 →
        qmaAcc O (V x.length) x.length (w.eval x.length) x ψ ≤ (1 / 3 : ℝ))}

end QiOPoQ.Supplement


