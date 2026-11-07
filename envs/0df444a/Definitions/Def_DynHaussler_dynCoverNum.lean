-- Prove2me | Definitions.Def_DynHaussler_dynCoverNum
-- name    : DynHaussler_dynCoverNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:44.795206+00:00
-- url     : https://prove2.me/theorems/f5cf5cee-12e1-4437-9804-583dd95d9235
-- title:
--   Global dynamic covering number $N^{\mathrm{dyn}}_p(F,\varepsilon,T)$
-- statement:
--   The **global dynamic covering number** $N^{\mathrm{dyn}}_p(F,\varepsilon,T)$ is the least cardinality of a global dynamic $\ell_p$ cover of $F$ at accuracy $\varepsilon$ and horizon $T$ (Definition 4), or $\infty$ if no finite cover exists.
--
--   This is the quantity bounded above and below by the mission's goal theorem: it is horizon-independent exactly when one bound on the size of a cover holds for all $T$.
--
--   **Formalization Note** Valued in `ℕ∞` as the infimum of the attainable sizes; the infimum of the empty set is $\top$, the paper's $\infty$. Statements compare it with real bounds through the coercion `ℕ∞ → ℝ≥0∞`.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Definition 4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_DynHaussler_IsGlobalCover

set_option autoImplicit false

namespace DynHaussler

/-- The **global dynamic covering number** `N^dyn_p(F, ε, T)`: the least cardinality of a global
dynamic `ℓ_p` cover of `F` at accuracy `ε` and horizon `T`, or `∞` if none exists.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Definition 4, p.14 (PDF p.16).

**Formalization Note** Valued in `ℕ∞`: the infimum of the empty set is `⊤`, which is the paper's
"`∞` if none exists". Statements compare it with real bounds through the coercion
`ℕ∞ → ℝ≥0∞`. -/
noncomputable def dynCoverNum {X : Type*} (p ε : ℝ) (F : Set (X → ℝ)) (T : ℕ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ k : ℕ, (k : ℕ∞) = n ∧ ∃ G : Fin k → CausalExpert X T, IsGlobalCover p ε F G}

end DynHaussler


