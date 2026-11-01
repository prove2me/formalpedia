-- Prove2me | Definitions.Def_CoupledLearning_payoffEquivSet
-- name    : CoupledLearning_payoffEquivSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:52.121155+00:00
-- url     : https://prove2.me/theorems/4ad9fb74-873f-4822-b365-fc64c117d766
-- title:
--   Payoff-equivalent parameters $S^*(q)$ (Definition 2)
-- statement:
--   A parameter $s$ is **payoff-equivalent** to the true parameter $s^*$ at the profile $q$ if $D_{KL}(\varphi^{s^*}(y|q)\|\varphi^{s}(y|q))=0$. The set of such parameters is
--
--   $$S^*(q)=\{s\in S\mid D_{KL}(\varphi^{s^*}(y|q)\|\varphi^{s}(y|q))=0\}.$$
--
--   Payoffs realized at $q$ cannot distinguish $s\in S^*(q)$ from $s^*$; condition (2a) of Theorem 1 says the limit belief is supported in $S^*(\bar q)$.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Definition 2, p.12

import Mathlib
import Definitions.Def_CoupledLearning_KL

namespace CoupledLearning

/-- Definition 2 (payoff-equivalent parameters), arXiv:2206.05637v2, p.12: for a profile `q`, the
set `S*(q) = {s ∈ S | D_KL(φ^{s*}(y|q) ‖ φ^s(y|q)) = 0}` of parameters that are payoff-equivalent
to the true parameter `s*`. -/
def payoffEquivSet {I S : Type*} [Fintype I] {d : I → ℕ}
    (φ : S → Prof d → (I → ℝ) → ℝ) (sstar : S) (q : Prof d) : Set S :=
  {s | KL φ sstar s q = 0}

end CoupledLearning


