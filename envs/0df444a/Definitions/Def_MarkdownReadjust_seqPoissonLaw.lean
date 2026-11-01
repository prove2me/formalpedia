-- Prove2me | Definitions.Def_MarkdownReadjust_seqPoissonLaw
-- name    : MarkdownReadjust_seqPoissonLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:52.871662+00:00
-- url     : https://prove2.me/theorems/8877b5b4-58b8-48fc-a2d2-475b1121563a
-- title:
--   Sequential Poisson law of interval demand counts
-- statement:
--   For rate functions $r_m$ that depend only on the past, the **sequential Poisson law** of $(D_0,\dots,D_{n-1})\in\mathbb N^n$ is the law under which, given $D_0,\dots,D_{m-1}$, the count $D_m$ is Poisson with mean $r_m(D_0,\dots,D_{m-1})$.
--
--   When the price is constant on each interval $[t_m,t_{m+1})$ and chosen from past sales, Poisson thinning and independent increments make the numbers of buying customers in the intervals follow this law, with $r_m=\lambda(t_{m+1}-t_m)\rho_m$. It is the probability space of the policy's revenue and of the uncapped process of Appendix B.
--
--   **Formalization Note** Built by iterated binding of probability mass functions, so it is a probability measure; causality is enforced by typing ($r_m$ sees only the first $m$ counts). `pathExt` extends a finite path by zeros.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §3 p.6 (Poisson arrivals), §5.1 p.10 (Sₘ Poisson with mean λ(t_{m+1}−tₘ)ρₘ), Appendix B.1 p.ec12

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MarkdownReadjust

/-- The sequential Poisson law on prefixes `(d₀, …, d_{n−1}) ∈ ℕⁿ`: given the first `m` values
`p`, the next value `d_m` is Poisson with mean `rate m p`, which may depend on `p` (the past
only). Built by iterated `PMF.bind` of Mathlib's Poisson law `poissonMeasure` (as a PMF), so it
is a probability distribution by construction. -/
noncomputable def seqPoissonPMF (rate : (n : ℕ) → (Fin n → ℕ) → NNReal) :
    (n : ℕ) → PMF (Fin n → ℕ)
  | 0 => PMF.pure (fun i => i.elim0)
  | n + 1 => (seqPoissonPMF rate n).bind fun p =>
      (poissonMeasure (rate n p)).toPMF.map fun d => Fin.snoc (α := fun _ => ℕ) p d

/-- The sequential Poisson law of `(D₀, …, D_{n−1})` as a measure on `Fin n → ℕ`
(conditionally on `D₀, …, D_{m−1}`, `D_m` is Poisson with mean `rate m (D₀, …, D_{m−1})`).

**Formalization Note.** This is the exact joint law of the per-interval demand counts of a
Poisson arrival process thinned by a price that is constant on each interval and chosen from the
past counts (Poisson thinning and independent increments): the continuous-time process itself
is not built. Causality is enforced by the type: `rate m` sees only the first `m` counts. -/
noncomputable def seqPoissonLaw (rate : (n : ℕ) → (Fin n → ℕ) → NNReal) (n : ℕ) :
    Measure (Fin n → ℕ) :=
  (seqPoissonPMF rate n).toMeasure

/-- Extension of a finite path `(ω₀, …, ω_{n−1})` to `ℕ → ℕ` by zeros. -/
def pathExt {n : ℕ} (ω : Fin n → ℕ) : ℕ → ℕ :=
  fun m => if h : m < n then ω ⟨m, h⟩ else 0

end MarkdownReadjust


