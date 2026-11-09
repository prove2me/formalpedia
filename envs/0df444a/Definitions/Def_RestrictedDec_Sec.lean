-- Prove2me | Definitions.Def_RestrictedDec_Sec
-- name    : RestrictedDec_Sec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:54:43.782195+00:00
-- url     : https://prove2.me/theorems/a2e6f76c-0b44-4227-8bfb-2ff8ccc63d1e
-- title:
--   Security classes $\mathrm{Sec}^{na}(\mathcal F)$ and $\mathrm{Sec}^{ad}(\mathcal F)$
-- statement:
--   For $t\in\{na,ad\}$, a scheme $\Pi$ over $\{0,1\}^{n(\lambda)}$ belongs to $\mathrm{Sec}^t(\mathcal F)$ (is $\mathrm{IND}^t_{\mathcal F}$-secure) if
--
--   1. it has ordinary negligible-error correctness (Definition 3), and
--   2. every uniform probabilistic polynomial-time adversary $A$ has negligible advantage $\mathrm{Adv}^t_{\Pi,\mathcal F}(A,\lambda)$.
--
--   $\mathrm{Sec}^t(q)$ is $\mathrm{Sec}^t(\mathcal F_q)$.
--
--   **Formalization Note** Efficiency of the scheme is the separate predicate `PKE.IsScheme`, which the theorems of the mission state for every scheme they compare.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Correct
import Definitions.Def_RestrictedDec_expIND
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The **security class** `Sec^t(𝓕)` (`IND^t_𝓕` security) over the message space
`{0,1}^{n(λ)}`: the scheme has ordinary negligible-error correctness (Definition 3) and every
uniform PPT adversary has negligible advantage in `Exp^{IND,t}_{P,𝓕}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13 ("A scheme
satisfies INDna F or INDad F if it has ordinary negligible-error correctness (Definition 3) and every
probabilistic polynomial-time (PPT) adversary has negligible advantage in the corresponding game.
… Write Secna(F) and Secad(F) for the schemes secure in these games.").

**Formalization Note.** Efficiency of the scheme is the separate predicate `PKE.IsScheme`.
`Negligible` is `NoisyOWMPC.Negligible`; its sign clause holds for an absolute value. -/
def Sec (t : Timing) (n : ℕ → ℕ) (F : Family) (P : PKE) : Prop :=
  Correct n P ∧ ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (adv t n P F A)

end RestrictedDec


