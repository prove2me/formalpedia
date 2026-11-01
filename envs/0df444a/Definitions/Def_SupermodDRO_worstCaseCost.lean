-- Prove2me | Definitions.Def_SupermodDRO_worstCaseCost
-- name    : SupermodDRO_worstCaseCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:12.88435+00:00
-- url     : https://prove2.me/theorems/334a3c75-5347-4187-ad64-beaf4b29f923
-- title:
--   Worst-case expected second-stage cost $\sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]$
-- statement:
--   For a first-stage decision $x$,
--   $$
--   \sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]\in[-\infty,+\infty],
--   $$
--   the supremum over the joint laws of $(\tilde k,\tilde z)$ in $\mathcal F$ of the expected second-stage cost.
--
--   **Formalization Note** The expectation is the platform's extended expectation ($+\infty$ whenever the positive part has infinite integral, in particular when $g(x,\tilde z)=+\infty$ with positive probability).
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, p.6

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SupermodDRO_ambiguitySet

open MeasureTheory

namespace SupermodDRO

/-- **The worst-case expected second-stage cost `sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)]`.** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
§2.1, p.6 (display before (2)).

**Formalization Note** `P` is a law of `(k̃, z̃)`; the integrand is `(k, z) ↦ g(x, z)`. The
expectation is the published `DupacovaWets.Consistency.expect` (`+∞` when the positive part has
infinite integral, in particular when `g(x, z̃) = ∞` with positive probability), and the supremum is
taken in `EReal`. -/
noncomputable def worstCaseCost {l m r n K s : ℕ} (D : Data l m r n K s) (x : Fin l → ℝ) :
    EReal :=
  ⨆ P ∈ ambiguitySet D, DupacovaWets.Consistency.expect P (fun ω => D.g x ω.2)

end SupermodDRO


