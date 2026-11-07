-- Prove2me | Definitions.Def_QPACLarge_prfEval
-- name    : QPACLarge_prfEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:22.832746+00:00
-- url     : https://prove2.me/theorems/caa913f6-1b10-404a-a590-5d6d7850b324
-- title:
--   Member $g_{\lambda,s}$ of a function family
-- statement:
--   A function family $G_\lambda = \{g_{\lambda,s} : \{0,1\}^\lambda \to \{0,1\}\}_{s \in \{0,1\}^{\ell(\lambda)}}$ is given by a deterministic evaluation algorithm $G$ run on input $(1^\lambda, s, x)$: $g_{\lambda,s}(x)$ is the first output bit of $G$ on $1^\lambda 0\, s\, x$.
--
--   **Formalization Note** An empty output is read as $0$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 4.2.1, p.31

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **A member `g_{λ,s}` of a function family given by its evaluation algorithm.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 4.2.1, p.31: "`G_λ = {g_{λ,s} : {0,1}^λ → {0,1}}_{s ∈ {0,1}^{ℓ(λ)}}` with a
deterministic evaluation algorithm running in `poly(λ)` time on input `(1^λ, s, x)`".

`prfEval G λ s x` is the first output bit of the evaluation algorithm `G` on input
`1^λ0 · s · x`.

**Formalization Note.** An empty output is read as `0` (`false`). -/
def prfEval (G : Str → Str) (lam : ℕ) (s : Str) (x : Qubits lam) : Bool :=
  (G (encNat lam ++ s ++ List.ofFn x)).headD false

end QPACLarge


