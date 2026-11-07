-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_IsPoQ
-- name    : QAdvFew_PoQOracle_IsPoQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:30.229076+00:00
-- url     : https://prove2.me/theorems/1416d48f-12cf-4a20-b7e2-3ec3105e426a
-- title:
--   Proof of quantumness
-- statement:
--   A **proof of quantumness** relative to $O$ is a protocol with classical communication between a QPT prover $P^O$ and a PPT verifier $V^O$ on common input $1^n$, in which the verifier outputs a bit, such that:
--
--   1. (Completeness) $\Pr[(V^O\leftrightarrows P^O)(1^n)\to1]\ge 1-\mathrm{negl}(n)$;
--   2. (Classical soundness) for every nonuniform PPT classical prover $P^{*O}$, $\Pr[(V^O\leftrightarrows P^{*O})(1^n)\to1]\le\mathrm{negl}(n)$.
--
--   **Formalization Note** The honest prover is a uniform, polynomially bounded QPT party; an unbounded honest prover would make completeness trivial.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_CVerifier
import Definitions.Def_QAdvFew_PoQOracle_QParty
import Definitions.Def_QAdvFew_PoQOracle_NUProver
import Definitions.Def_QAdvFew_PoQOracle_Negligible

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **proof of quantumness** relative to `O` (Goldin, Lombardi, Morimae, *Quantum Advantage has
Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21)): a protocol
with classical communication between a QPT prover `P^O` and a PPT verifier `V^O` on common input
`1^n`, in which the verifier outputs a bit, such that
1. (completeness) `Pr[(V^O ⇆ P^O)(1^n) → 1] ≥ 1 − negl(n)`;
2. (classical soundness) for every nonuniform PPT classical prover `P^{∗O}`,
   `Pr[(V^O ⇆ P^{∗O})(1^n) → 1] ≤ negl(n)`.

**Formalization Note** `V` is a `CVerifier` (polynomially many rounds, polynomial time, polynomially
many coins) run on `1^n` with length parameter `n`; the honest prover is a uniform, polynomially
bounded `QParty`; soundness quantifies over every `NUProver`. -/
def IsPoQ (O : Oracle) (V : CVerifier) (P : QParty (fun n => V.ℓ.eval n)) : Prop :=
  P.Uniform ∧ P.PolyBounded ∧
  Negligible (fun n => 1 - acceptProb (V.R.eval n) (V.ℓ.eval n) (V.lik O (unary n) n)
    (P.likP O n)) ∧
  ∀ P' : NUProver (fun n => V.ℓ.eval n),
    Negligible (fun n => acceptProb (V.R.eval n) (V.ℓ.eval n) (V.lik O (unary n) n) (P'.lik O n))

end QAdvFew.PoQOracle


