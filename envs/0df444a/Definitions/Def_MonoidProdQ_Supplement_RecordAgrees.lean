-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_RecordAgrees
-- name    : MonoidProdQ_Supplement_RecordAgrees
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:11:37.162796+00:00
-- url     : https://prove2.me/theorems/ac8334bc-6d17-4de0-9a1b-2ace724c8c5d
-- title:
--   Record agreeing with the input
-- statement:
--   A record $\rho$ (a partial assignment of letters to positions) **agrees with the input** $x$ if every recorded letter is the input letter at its position: $\rho(i)=a$ implies $a=x_i$. Theorem 46 asserts this for every record its algorithm can output ("on every branch").
--
--   **Formalization Note** A decidability instance is provided.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 46, p.63

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 46, p.63: a record
`ρ : Fin n → Option G` "agree[s] with the input" `x` if every recorded letter is the input letter
at its position: `ρ i = some a ⟹ a = xᵢ`. The decidability instance below lets the statements
take the probability of this event. -/
def RecordAgrees {M : Type*} {G : Finset M} {n : ℕ} (x : Fin n → G) (ρ : Fin n → Option G) :
    Prop :=
  ∀ i a, ρ i = some a → a = x i

instance RecordAgrees.instDecidable {M : Type*} [DecidableEq M] {G : Finset M} {n : ℕ}
    (x : Fin n → G) (ρ : Fin n → Option G) : Decidable (RecordAgrees x ρ) := by
  unfold RecordAgrees; infer_instance

end MonoidProdQ.Supplement


