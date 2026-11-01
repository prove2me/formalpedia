-- Prove2me | Definitions.Def_MarkdownReadjust_A1
-- name    : MarkdownReadjust_A1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:06.133979+00:00
-- url     : https://prove2.me/theorems/9ca62130-2a33-4387-b879-035c672b5ff3
-- title:
--   $A_1=(-\lambda)\sum_n(t_{n+1}-t_n)\mathsf E[\hat\rho_n-\rho^d]$
-- statement:
--   The first-order term of the Taylor expansion of the revenue,
--
--   $$
--   A_1=(-\lambda)\sum_{n=0}^{N}(t_{n+1}-t_n)\,\mathsf E\big[\hat\rho_n-\rho^d\big],
--   $$
--
--   with expectations over the uncapped process. Lemma EC.1 bounds it by a multiple of $\mathbb P(\mathcal G^c)$.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, p.ec13 (underbrace A₁)

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw

open MeasureTheory

namespace MarkdownReadjust

/-- `A₁ = (−λ) Σ_{n=0}^{N} (t_{n+1} − tₙ) E[ρ̂ₙ − ρᵈ]` (Chen–Jasin, SSRN 3740871, p.ec13,
underbrace), the expectation under the uncapped law `hatLaw`.

**Formalization Note.** `ρ̂ₙ ∈ [0,1]` is bounded, so the Bochner integral is the expectation. -/
noncomputable def A1 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : ℝ :=
  -M.lam * ∑ n ∈ Finset.range (N + 1), (tgrid x τ N (n + 1) - tgrid x τ N n) *
    ∫ ω, (rhoHat M α N x τ (pathExt ω) n - rhoD M x τ) ∂(hatLaw M α N x τ)

end MarkdownReadjust


