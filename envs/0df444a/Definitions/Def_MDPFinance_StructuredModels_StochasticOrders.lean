-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_StochasticOrders
-- name    : MDPFinance_StructuredModels_StochasticOrders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:32:34.016165+00:00
-- url     : https://prove2.me/theorems/8eb91a70-312f-48fa-9b88-566f71d55890
-- title:
--   Stochastic, convex and concave orders on measures (Appendix B.3)
-- statement:
--   For random elements $X, Y$ of $E$ with laws $\mu, \nu$: $\mu \leq_{\mathrm{st}} \nu$ iff
--   $\mathbb{E}f(X) \leq \mathbb{E}f(Y)$ for every bounded increasing $f$; $\mu \leq_{\mathrm{cx}}
--   \nu$ iff this holds for every convex $f$; $\mu \leq_{\mathrm{cv}} \nu$ iff it holds for every
--   concave $f$ (whenever the expectations exist, in each case).
--
--   **Formalization Note.** $\leq_{\mathrm{st}}$ is defined here via Theorem B.3.3(ii)'s
--   equivalent functional characterization rather than the book's CDF definition B.3.2 (stated
--   only for $\mathbb{R}$-valued random variables), since it must apply to the general state
--   space $E$ of §2.4.4. $\leq_{\mathrm{cx}}$ matches Definition B.3.9a verbatim.
--   $\leq_{\mathrm{cv}}$ has no verbatim numbered definition in the book (only the *increasing*-
--   concave order $\leq_{\mathrm{icv}}$, Definition B.3.9c, is given a number) — see
--   `MODERATION_NOTES.md` for why the concave-test-function analogue of $\leq_{\mathrm{cx}}$ is the
--   faithful reading of Theorem 2.4.23's own "cv".
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 358-361, Definition B.3.2/Theorem B.3.3/Definition B.3.9

import Mathlib

open MeasureTheory

namespace MDPFinance.StructuredModels

variable {E : Type*} [MeasurableSpace E] [Preorder E]

/-- The usual stochastic order on measures on `E` (Bäuerle–Rieder, Definition B.3.2 + Theorem
B.3.3(ii), p. 358-359, PDF 365-366): `μ ≤_st ν` iff `∫ f dμ ≤ ∫ f dν` for every bounded
increasing `f`. The book's Definition B.3.2 is stated via CDFs for real-valued random variables;
Theorem B.3.3(ii) gives the equivalent characterization used here directly, since Theorem 2.4.23
compares kernels on the general state space `E ⊆ ℝ^d` of §2.4.4 rather than on `ℝ` itself (see
`MODERATION_NOTES.md`). -/
def LEStochasticOrder (μ ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Monotone f → Integrable f μ → Integrable f ν → ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν

variable {F : Type*} [MeasurableSpace F] [AddCommGroup F] [Module ℝ F]

/-- The convex order on measures on `F` (Bäuerle–Rieder, Definition B.3.9a, p. 361, PDF 368):
`μ ≤_cx ν` iff `∫ f dμ ≤ ∫ f dν` for every convex `f` for which both integrals exist. -/
def LEConvexOrder (μ ν : Measure F) : Prop :=
  ∀ f : F → ℝ, ConvexOn ℝ Set.univ f → Integrable f μ → Integrable f ν → ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν

/-- The concave order on measures on `F` (Bäuerle–Rieder, Theorem 2.4.23's `≤_cv`, p. 38, PDF
53): `μ ≤_cv ν` iff `∫ f dμ ≤ ∫ f dν` for every concave `f` for which both integrals exist. The
book's Appendix B.3 defines `≤_cx` (Def. B.3.9a) and the *increasing*-concave order `≤_icv`
(Def. B.3.9c), but never a bare, non-monotone `≤_cv` under that name; this is the direct
concave-test-function analogue of Def. B.3.9a (dual to `≤_cx`, matching the book's own
`IM_n^cv := {v ∈ IB_b^+ | v concave}`, itself not required to be increasing) and is the standard
"concave order" of Müller and Stoyan (2002), the reference the book cites for this whole section
(see `MODERATION_NOTES.md`). -/
def LEConcaveOrder (μ ν : Measure F) : Prop :=
  ∀ f : F → ℝ, ConcaveOn ℝ Set.univ f → Integrable f μ → Integrable f ν →
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν

end MDPFinance.StructuredModels


