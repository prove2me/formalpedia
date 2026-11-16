-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_IsQvOSP
-- name    : QAdvFew_PoQOracle_Supplement_IsQvOSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:27.087015+00:00
-- url     : https://prove2.me/theorems/e7f00c57-6ccf-40fb-a186-70ec5901e016
-- title:
--   Quantum-verifier oblivious state preparation
-- statement:
--   **Oblivious state preparation** relative to the oracles $(O,C)$ (Definition 3.28) is a protocol with classical communication between a verifier $V$, which has an input bit $b$ and outputs a bit $s$, and a QPT prover $P$, which outputs one qubit, on common input $1^n$, such that:
--
--   1. **Correctness.** For each $b\in\{0,1\}$, measuring the honest prover's output qubit in the computational basis if $b=0$, or the Hadamard basis if $b=1$, gives $s$ with probability at least $1-\mathrm{negl}(n)$.
--   2. **Security.** For every nonuniform QPT malicious prover $P^*$ with access to $(O,C)$ that outputs a bit,
--   $$
--   \bigl|\Pr[P^*\to1\text{ in }\langle V(1^n,0),P^*(1^n)\rangle]-\Pr[P^*\to1\text{ in }\langle V(1^n,1),P^*(1^n)\rangle]\bigr|\le\mathrm{negl}(n).
--   $$
--
--   With a QPT verifier this is **quantum verifier oblivious state preparation** (qv-OSP). A protocol is **four-message** if exactly four messages are exchanged at every $n$.
--
--   **Formalization Note** The verifier's input bit is the initial value of its input/output qubit and $s$ is that qubit's final measurement. $\mathrm{negl}$ is the published `Negligible`. Either party may send the first message.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.28, p. 19 (PDF p. 21); Theorem 1.8, pp. 3–4 (PDF pp. 5–6)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IParty
import Definitions.Def_QAdvFew_PoQOracle_Negligible

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- A protocol skeleton with a QPT verifier: `M(n)` messages of length `ℓ(n)` (polynomials), the
verifier sending message `0` iff `vFirst`, and the verifier party. -/
structure QVProtocol (ar : ℕ → ℕ → ℕ) where
  M : Polynomial ℕ
  ℓ : Polynomial ℕ
  vFirst : Bool
  V : IParty ar (fun n => ℓ.eval n)

/-- **Quantum verifier oblivious state preparation** relative to the oracles `(O, C)` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Definition 3.28, p. 19 (PDF p. 21): "a protocol with classical communication between a PPT verifier
`V^O` and a QPT prover `P^O`, on common input `1^n`. The verifier also has an input bit `b`,
outputs a bit `s`, and the prover outputs one qubit. … 1. Correctness. For each `b ∈ {0,1}`,
measuring the honest prover's output in the computational basis if `b = 0`, or the Hadamard basis
if `b = 1`, gives `s` with probability at least `1 − negl(n)`. 2. Security. For every nonuniform
QPT malicious prover `P^{∗O}` outputting a bit, `|Pr[P^{∗O} → 1 in ⟨V^O(1^n, 0), P^{∗O}(1^n)⟩] −
Pr[P^{∗O} → 1 in ⟨V^O(1^n, 1), P^{∗O}(1^n)⟩]| ≤ negl(n)`. Allowing the verifier to be QPT instead
gives quantum verifier oblivious state preparation (qv-OSP)").

The verifier `Pr.V` and the honest prover `P` are uniform and polynomially bounded. The verifier's
input bit `b` is its input/output qubit's initial value and `s` is that qubit's final measurement;
the prover's output qubit is its input/output wire. A malicious prover is any polynomially bounded
`IParty` (no uniformity) with access to the same oracles; its output bit is its input/output wire.

**Formalization Note** `negl(n)` is the published `QAdvFew.PoQOracle.Negligible`. The malicious
prover is quantified after the oracles, so its circuits may depend on them (§3.2.1). -/
def IsQvOSP {ar : ℕ → ℕ → ℕ} (O : UOracle ar) (C : Oracle) (Pr : QVProtocol ar)
    (P : IParty ar (fun n => Pr.ℓ.eval n)) : Prop :=
  Pr.V.Uniform ∧ Pr.V.PolyBounded ∧ P.Uniform ∧ P.PolyBounded ∧
  (∀ b : Bool, Negligible (fun n => 1 -
    ∑ τ : ITranscript (Pr.M.eval n) (Pr.ℓ.eval n), ∑ s : Bool,
      Pr.V.lik O C n Pr.vFirst τ b false s * P.lik O C n (!Pr.vFirst) τ false b s)) ∧
  ∀ P' : IParty ar (fun n => Pr.ℓ.eval n), P'.PolyBounded →
    Negligible (fun n =>
      |(∑ τ : ITranscript (Pr.M.eval n) (Pr.ℓ.eval n), ∑ s : Bool,
          Pr.V.lik O C n Pr.vFirst τ false false s * P'.lik O C n (!Pr.vFirst) τ false false true) -
        (∑ τ : ITranscript (Pr.M.eval n) (Pr.ℓ.eval n), ∑ s : Bool,
          Pr.V.lik O C n Pr.vFirst τ true false s * P'.lik O C n (!Pr.vFirst) τ false false true)|)

/-- qv-OSP exists relative to `(O, C)`. -/
def QvOSPExists {ar : ℕ → ℕ → ℕ} (O : UOracle ar) (C : Oracle) : Prop :=
  ∃ (Pr : QVProtocol ar) (P : IParty ar (fun n => Pr.ℓ.eval n)), IsQvOSP O C Pr P

/-- A **four message** protocol (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 1.8, pp. 3–4 (PDF pp. 5–6): "a four message qv-OSP"):
exactly four classical messages at every `n`. -/
def FourMessage {ar : ℕ → ℕ → ℕ} (Pr : QVProtocol ar) : Prop := ∀ n : ℕ, Pr.M.eval n = 4

end QAdvFew.PoQOracle.Supplement


