-- Prove2me | Definitions.Def_MarkdownReadjust_A2
-- name    : MarkdownReadjust_A2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:03.695021+00:00
-- url     : https://prove2.me/theorems/7a1674f9-a1d3-4217-94f1-eec8a4a32ded
-- title:
--   $A_2=\lambda\sum_n(t_{n+1}-t_n)\mathsf E[(\hat\rho_n-\rho^d)^2]$
-- statement:
--   The second-order term of the Taylor expansion of the revenue,
--
--   $$
--   A_2=\lambda\sum_{n=0}^{N}(t_{n+1}-t_n)\,\mathsf E\big[(\hat\rho_n-\rho^d)^2\big],
--   $$
--
--   with expectations over the uncapped process. It is the dominant part of the revenue loss (Lemma EC.1).
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, p.ec13 (underbrace A₂)

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw

open MeasureTheory

namespace MarkdownReadjust

/-- `A₂ = λ Σ_{n=0}^{N} (t_{n+1} − tₙ) E[(ρ̂ₙ − ρᵈ)²]` (Chen–Jasin, SSRN 3740871, p.ec13,
underbrace), the expectation under the uncapped law `hatLaw`.

**Formalization Note.** The integrand is bounded, so the Bochner integral is the expectation. -/
noncomputable def A2 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : ℝ :=
  M.lam * ∑ n ∈ Finset.range (N + 1), (tgrid x τ N (n + 1) - tgrid x τ N n) *
    ∫ ω, (rhoHat M α N x τ (pathExt ω) n - rhoD M x τ) ^ 2 ∂(hatLaw M α N x τ)

end MarkdownReadjust


