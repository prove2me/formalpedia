-- Prove2me | Definitions.Def_SignFreeOracle_Separation_MA
-- name    : SignFreeOracle_Separation_MA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:59.98984+00:00
-- url     : https://prove2.me/theorems/942d590c-ba06-4f54-8279-28fe08ca3809
-- title:
--   Operational oracle MA
-- statement:
--   Let $O:\{0,1\}^*\to\{0,1\}$ be a fixed Boolean oracle and $L=(L_{\rm yes},L_{\rm no})$ a promise problem. A verifier consists of a finite two-tape oracle machine and three fixed natural-coefficient polynomials for witness length, private random-bit length, and running time. Its acceptance probability is the fraction of fair random strings on which its clocked execution accepts. Timeouts reject. Writing queries and reading input, witness and coins take machine transitions.
--
--   The class $\mathrm{MA}^O$ requires
--   $$x\in L_{\rm yes}\Rightarrow\exists w:\Pr[V^O(x,w)=1]\ge2/3,\qquad x\in L_{\rm no}\Rightarrow\forall w:\Pr[V^O(x,w)=1]\le1/3.$$
--   Witnesses have the specified polynomial length and can depend arbitrarily on the entire oracle. The machine and polynomials precede every input. This supplies the operational classical class for the goal. Preselecting polynomially many private fair bits and using a polynomial clock represents all probabilistic polynomial-time oracle verifiers, with polynomial simulation overhead.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definition 2.1, pp. 6–7 (PDF pp. 6–7)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- A polynomially clocked finite oracle machine, using a private uniformly random string.
The clock is a polynomial in the ordinary input length. Reading the witness, random bits,
and writing an oracle query use ordinary machine transitions. A timeout rejects. -/
structure MAVerifier where
  machine : OTM
  witnessLength : Polynomial ℕ
  randomLength : Polynomial ℕ
  clock : Polynomial ℕ

noncomputable def MAVerifier.accept (V : MAVerifier) (O : Oracle) (x w : Str) : ℝ := by
  classical
  exact ((Finset.univ.filter fun r : Bits (V.randomLength.eval x.length) =>
    V.machine.result O (tup [x, w, List.ofFn r]) (V.clock.eval x.length) = some true).card : ℝ) /
      2 ^ V.randomLength.eval x.length

/-- Definition 2.1, pp. 6–7: the same finite verifier and three polynomials work at all lengths.
Witnesses are arbitrary classical strings of the specified length, with no restriction on
how they depend on the fixed oracle. -/
def MA (O : Oracle) : Set PromiseProblem :=
  {L | ∃ V : MAVerifier, ∀ x : Str,
    (x ∈ L.yes → ∃ w : Str, w.length = V.witnessLength.eval x.length ∧
      (2 / 3 : ℝ) ≤ V.accept O x w) ∧
    (x ∈ L.no → ∀ w : Str, w.length = V.witnessLength.eval x.length →
      V.accept O x w ≤ (1 / 3 : ℝ))}

end SignFreeOracle.Separation


