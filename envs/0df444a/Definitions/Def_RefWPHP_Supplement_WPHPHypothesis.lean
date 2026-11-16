-- Prove2me | Definitions.Def_RefWPHP_Supplement_WPHPHypothesis
-- name    : RefWPHP_Supplement_WPHPHypothesis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:22:17.890431+00:00
-- url     : https://prove2.me/theorems/b48f3735-fa16-433c-8ad9-707a1afa2f16
-- title:
--   Hypothesis 1.4 — the WPHP Hypothesis for constant-depth Frege
-- statement:
--   The **WPHP Hypothesis** states that for every $d \in \mathbb N$ there exist $n_0 \in \mathbb N$ and a function $f_d = \omega(1)$ such that for every $n \ge n_0$, every $\mathrm{PK}_d$-refutation of the weak pigeonhole formula $\mathrm{PHP}^{n^2}_n$ has size at least
--
--   $$
--   n^{f_d(n)} .
--   $$
--
--   That is, refuting $\mathrm{PHP}^{n^2}_n$ in depth-$d$ Frege requires superpolynomial size, for every fixed depth $d$. The paper treats it as a working hypothesis and derives from it the hardness results of Sections 4 and 5.
--
--   **Formalization Note** This is a proposition used only as a hypothesis, never asserted. $\mathrm{PK}_d$ refutations and size are the base mission's `IsPKRefutation d` and `derivSize`, and $f_d = \omega(1)$ is $f_d(n) \to \infty$.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Hypothesis 1.4, p.4 (PDF p.6), restated p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF

namespace RefWPHP

namespace Supplement

open Filter

/-- The WPHP Hypothesis (Hypothesis 1.4) of N. Arteche, *Resolution Lower Bounds versus the Weak
Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), p.4 (PDF 6), in
the form restated on p.34 (PDF 36): "for every `d ∈ ℕ` there exist `n₀ ∈ ℕ` and a function
`f_d = ω(1)` such that for every `n ≥ n₀` the unsatisfiable CNF formula `PHP^{n²}_n` requires size
at least `n^{f_d(n)}` to be refuted in depth-`d` Frege".

**Formalization Note.** Depth-`d` Frege is the base calculus `PK_d` (`IsPKRefutation d`), size is
the base `derivSize`, and `f_d = ω(1)` is `f_d(n) → ∞`. This is a `Prop`, used only as a
hypothesis; it is not asserted. -/
def WPHPHypothesis : Prop :=
  ∀ d : ℕ, ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ ρ : List (Cedent (Fin (n ^ 2) × Fin n)), IsPKRefutation d (phpCNF (n ^ 2) n) ρ →
      (n : ℝ) ^ f n ≤ (derivSize ρ : ℝ)

end Supplement

end RefWPHP


