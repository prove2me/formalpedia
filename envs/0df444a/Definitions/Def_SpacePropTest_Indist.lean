-- Prove2me | Definitions.Def_SpacePropTest_Indist
-- name    : SpacePropTest_Indist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:52.333894+00:00
-- url     : https://prove2.me/theorems/582b8bd5-787e-4239-8033-c558a9571433
-- title:
--   $\varepsilon$-indistinguishable Markov chains (Definition 8)
-- statement:
--   Two Markov chains $C_1,C_2$ on the same state set with the same start state are **$\varepsilon$-indistinguishable** if for all transitions $(s,s')$
--
--   $$(1+\varepsilon)^{-1}\,C_1(s,s')\le C_2(s,s')\le(1+\varepsilon)\,C_1(s,s').$$
--
--   In particular the two chains have the same positive transitions. This multiplicative closeness is what the lower bounds transfer to long-run probabilities (Lemma 10).
--
--   **Formalization Note** The common state set and start state are encoded by a shared state type and a shared start state in each statement.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Definition 8, p.16 (PDF 18)

import Mathlib

set_option autoImplicit false

namespace SpacePropTest

/-- **ε-indistinguishable Markov chains** (C. Canonne, X. Chen, W. Pires, T. Pitassi,
R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2, 2026,
sha256 65850aa6…; Definition 8, p.16 (PDF 18)): for all transitions `(s, s')`,
`(1 + ε)⁻¹ · C₁(s, s') ≤ C₂(s, s') ≤ (1 + ε) · C₁(s, s')`.

**Formalization Note.** "The same set of states and the same start state" is encoded by the two
matrices sharing the state type `σ`, and, in every statement, a single start state `s₀`. -/
def Indist {σ : Type*} (C₁ C₂ : Matrix σ σ ℝ) (ε : ℝ) : Prop :=
  ∀ s s', (1 + ε)⁻¹ * C₁ s s' ≤ C₂ s s' ∧ C₂ s s' ≤ (1 + ε) * C₁ s s'

end SpacePropTest


