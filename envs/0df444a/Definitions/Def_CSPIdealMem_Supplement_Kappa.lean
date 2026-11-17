-- Prove2me | Definitions.Def_CSPIdealMem_Supplement_Kappa
-- name    : CSPIdealMem_Supplement_Kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:36:03.549202+00:00
-- url     : https://prove2.me/theorems/55f7369c-95b6-4b6a-ba85-b9b557cf9381
-- title:
--   The degree threshold $\kappa(\Gamma)$
-- statement:
--   Let $D\subseteq\mathbb Q$ be a nonempty finite domain and $\Gamma$ a finite constraint language on $D$. With $U_d$ the span of the degree-$d$ evaluation vectors of the covered endomorphisms of $\Gamma$, the **degree threshold** of $\Gamma$ is
--   $$
--   \kappa(\Gamma)=\min\{d\ge0 \mid \nu_d(\mathrm{id}_D)\notin U_d\},
--   $$
--   with $\kappa(\Gamma)=\infty$ if the set is empty. It is the first degree at which the finite span condition fails.
--
--   **Formalization Note** $\kappa(\Gamma)$ takes values in the extended naturals $\mathbb N\cup\{\infty\}$ and is the infimum of the failing degrees; the infimum of the empty set is $\infty$.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), "Degree threshold", p.5 (PDF 5)

import Mathlib
import Definitions.Def_CSPIdealMem_EvalSpace

namespace CSPIdealMem.Supplement

/-! # The degree threshold `κ(Γ)`

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), "Degree threshold", p.5 (PDF 5).

**Formalization Note.** `κ(Γ)` takes values in `ℕ∞`; the infimum of the empty set is `⊤ = ∞`,
matching "κ(Γ) = ∞ if the set is empty". -/

/-- `κ(Γ) := min{d ≥ 0 | ν_d(id_D) ∉ U_d}` (p.5), with `κ(Γ) = ∞` if the set is empty. -/
noncomputable def kappa {D : Finset ℚ} (Γ : ConstraintLanguage D) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : ¬ SpanCondition Γ d), (d : ℕ∞)

end CSPIdealMem.Supplement


