-- Prove2me | Definitions.Def_FRouting_InQSZK
-- name    : FRouting_InQSZK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:42.61655+00:00
-- url     : https://prove2.me/theorems/7b326df3-81ed-4063-9bb8-7b5917a28fd6
-- title:
--   The class $\mathrm{QSZK}(T)$
-- statement:
--   A promise problem is in $\mathrm{QSZK}(B)$ if there are an honest verifier machine, a negligible error $\mu\le 1/3$, a polynomial $r$ and, per input, an honest prover such that:
--
--   1. on every input $w$ the machine prints the verifier's protocol in time at most $B(|w|)$, with total gates and width at most $B(|w|)$;
--   2. for $w$ in Yes, the honest prover is accepted with probability at least $1-\mu(|w|)$;
--   3. for $w$ in No, every prover is accepted with probability at most $\mu(|w|)$;
--   4. for every $S$ and every cheating verifier machine running in time $S$, using the same message qubits and rounds and taking an auxiliary input, there are a constant $C$, a simulator machine running in time at most $C\,r(B(|w|)+S(|w|))$, printing a circuit of that size and width, and a negligible $\nu$, such that for $w$ in Yes, every finite reference and every state on reference and auxiliary input,
--   $$\Delta\big((\mathrm{id}\otimes\text{interaction})(\xi),(\mathrm{id}\otimes\text{simulator})(\xi)\big)\le \nu(|w|).$$
--
--   Here a time, size or width bound $B(|w|)$ of the honest or cheating verifier is read as $\max(1,B(|w|))$, which differs from $B$ only where $B(|w|)=0$, a bound no machine meets. Negligible is the published `CompNonlocal.Negligible` and $\Delta$ the published `DimFreeShadow.traceDistance`.
--
--   **Formalization Note** The paper's definition cites [Wat02; Wat09]. The readings are: errors that imply both the 2/3–1/3 and the negligible conventions; zero knowledge with auxiliary input and a stabilized trace distance, the honest prover being fixed before the cheating verifier; one polynomial $r$ per problem and a constant per verifier; qubit gates for verifier and simulator.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 5.1, p.20

import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_WildeQIT_QMemory_idTensorChannel
import Definitions.Def_FRouting_StrMachine
import Definitions.Def_FRouting_languageOf
import Definitions.Def_FRouting_VerifierDesc

set_option autoImplicit false

open Matrix

namespace FRouting

open QAlgorithms.Complexity

/-- **Membership in `QSZK(B)`.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held
copy, sha256 4a327f29…), Definition 5.1, p.20: "The complexity class QSZK(T) consists of all languages
having a Quantum Statistical Zero-Knowledge proof whose honest verifier Ver runs in time at most T(n)
and for which every verifier Ver∗ running in time S(n) has a simulator Sim_{Ver∗} running in time
poly(T(n) + S(n)) on inputs of length n. The statistical simulation error is negligible in n."

There are an honest verifier machine `Ver`, a negligible error `μ ≤ 1/3`, a polynomial `r` and, per
input, an honest prover such that:
1. on every `w`, `Ver` prints the protocol `hon w` within the budget of `B |w|`, and that protocol's
   quantum work is within the same budget;
2. completeness: for `w` in Yes, the honest prover is accepted with probability at least `1 − μ |w|`;
3. soundness: for `w` in No, every prover is accepted with probability at most `μ |w|`;
4. zero knowledge: for every `S` and every cheating verifier machine running in time `S`, which
   interacts on the same message qubits for the same number of rounds and may take an auxiliary
   input, there are a constant `C`, a simulator machine running within `C · r(B |w| + S |w|)`,
   printing a circuit of that size and width, and a negligible `ν`, such that for all `w` in Yes,
   every finite reference and every state on the reference and the auxiliary input, the trace
   distance between the outputs of the interaction and of the simulator is at most `ν |w|`.

**Formalization Note** The definition is cited from [Wat02; Wat09], so the following are readings.
(a) The errors: `μ` negligible and `≤ 1/3` implies both the 2/3–1/3 and the negligible-error
conventions. (b) Zero knowledge with auxiliary input, tested on any reference (a stabilized trace
distance, avoiding the diamond norm), with the honest prover fixed before the verifier; taking trivial
auxiliary and reference recovers the reading without auxiliary input. (c) One polynomial `r` per
problem, with a factor `C` per verifier since step counts depend on the machine. (d) Verifier and
simulator circuits are over the qubit gates `Gate 2`. -/
def InQSZK (P : PromiseProblem) (B : ℕ → ℕ) : Prop :=
  ∃ (Ver : StrMachine) (msg : Str → ℕ) (hon : ∀ w, VerifierDesc 0 1 (msg w))
    (prover : ∀ w, Prover (msg w)) (μ : ℕ → ℝ) (r : Polynomial ℕ),
    CompNonlocal.Negligible μ ∧ (∀ n, μ n ≤ 1 / 3) ∧
    (∀ w, PrintsInTime Ver w (encVerifier (hon w)) (budget B w.length) ∧
      (hon w).SizeBound (budget B w.length)) ∧
    (∀ w ∈ P.Yes, 1 - μ w.length ≤ acceptance (hon w) (prover w)) ∧
    (∀ w ∈ P.No, ∀ P' : Prover (msg w), acceptance (hon w) P' ≤ μ w.length) ∧
    ∀ (S : ℕ → ℕ) (Vstar : StrMachine) (aux out : Str → ℕ)
      (cheat : ∀ w, VerifierDesc (aux w) (out w) (msg w)),
      (∀ w ∈ P.Yes, PrintsInTime Vstar w (encVerifier (cheat w)) (budget S w.length) ∧
        (cheat w).SizeBound (budget S w.length) ∧
        (cheat w).rounds.length = (hon w).rounds.length) →
      ∃ (C : ℕ) (Sim : StrMachine) (sim : ∀ w, Circuit 2 (aux w) (out w)) (ν : ℕ → ℝ),
        CompNonlocal.Negligible ν ∧
        ∀ w ∈ P.Yes,
          PrintsInTime Sim w (encCircuit (sim w)) (C * r.eval (B w.length + S w.length)) ∧
          (sim w).size ≤ C * r.eval (B w.length + S w.length) ∧
          (sim w).width ≤ C * r.eval (B w.length + S w.length) ∧
          ∀ (Rf : Reg) (ξ : Matrix (Rf × Qubits (aux w)) (Rf × Qubits (aux w)) ℂ),
            PeresTerno.IsDensityMatrix ξ →
            DimFreeShadow.traceDistance
              (WildeQIT.QMemory.idTensorChannel (interaction (cheat w) (prover w)) ξ)
              (WildeQIT.QMemory.idTensorChannel (sim w).channel ξ) ≤ ν w.length

end FRouting


