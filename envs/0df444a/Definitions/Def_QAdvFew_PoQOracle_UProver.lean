-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_UProver
-- name    : QAdvFew_PoQOracle_UProver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:35.501611+00:00
-- url     : https://prove2.me/theorems/73682ce7-8985-474c-ac61-7da0dd85eb89
-- title:
--   Unbounded prover
-- statement:
--   An **unbounded prover** is an arbitrary function from the common input and the messages so far to its next message; its likelihood $w_P(\tau)$ is $1$ if it sends exactly its messages of $\tau$ and $0$ otherwise.
--
--   **Formalization Note** Unbounded provers are deterministic: a randomized prover's acceptance probability is an average of those of deterministic provers, so the supremum is the same.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.8, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Protocol

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- An **unbounded prover** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.8, p. 13 (PDF p. 15): "there is an unbounded prover
`P^O`", "for every unbounded prover `P^{∗O}`"): an arbitrary function from the common input and the
messages so far to its next message.

**Formalization Note** Unbounded provers are deterministic: a randomized prover's acceptance
probability is an average of those of deterministic provers, so the maximum over deterministic
provers is the same. The prover may depend on the oracle, since it is quantified after it. -/
def UProver := Str → List Str → Str

namespace UProver

/-- The prover's likelihood `w_P(τ)` (`1` if it sends exactly its messages of `τ`, else `0`). -/
noncomputable def lik (P : UProver) (s : Str) {R ℓ : ℕ} (τ : Transcript R ℓ) : ℝ := by
  classical exact if ∀ j : Fin R, padTo ℓ (P s (τ.prefixP j)) = (τ j).2 then 1 else 0

end UProver

end QAdvFew.PoQOracle


