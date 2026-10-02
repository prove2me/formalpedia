-- Prove2me | Definitions.Def_MDPFinance_LPDuality_Discretization
-- name    : MDPFinance_LPDuality_Discretization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:52:19.71422+00:00
-- url     : https://prove2.me/theorems/121ec7fb-c68e-428a-9e1f-52ebb3697a6c
-- title:
--   Grid approximation data for state-space discretization (§7.5.3)
-- statement:
--   To make an infinite (Borel) state space numerically tractable, §7.5.3 approximates it by a
--   finite grid $G \subset E$ and interpolates the Bellman operator $T$ linearly between grid points,
--   producing a grid operator $T_G$ and a grid bounding function $b_G$ that agree with $T$/$b$ on $G$
--   itself. This mission represents $T_G$/$b_G$ as *data* satisfying exactly the structural
--   properties Proposition 7.5.11 and Theorem 7.5.12's own proofs use — $b_G$ a bounding function
--   with $b_G \ge 1$, $T_G$ mapping the uniformly-continuous class $IM_c$ into itself — rather than
--   reconstructing the literal convex-combination interpolation formula $x = \sum_k\lambda_kx_k$,
--   $x_k \in G$, which presupposes a vector-space (or at least convex) structure on $E$ that this
--   book's series does not otherwise assume of a general Borel state space. `mtilde b bG := \sup_x
--   |b(x)-b_G(x)|$ and `normG bG v := \sup_x |v(x)|/b_G(x)$ are the two real quantities both target
--   theorems are actually stated in terms of.
--
--   **Moderation note.** $b_G$ is measurable (it is "again a bounding function"), so that the integrals in $\alpha_G$ are genuine.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 220-221, unnumbered display preceding Proposition 7.5.11

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- A **grid approximation** of a bounding function `b` (Bäuerle–Rieder, §7.5.3, p. 220-221, PDF
231-232): a grid bounding function `b_G` (itself a bounding function, `b_G \ge 1$) and a grid
Bellman operator `T_G$ mapping the uniformly-continuous class `IM_c$ into itself, agreeing with
`T$ on the grid `G$ (the book's own linear-interpolation construction — a specific `T_G$/`b_G$
built from a grid `G \subset E$ and simplex weights `x = \sum_k \lambda_kx_k$ — is *not*
reconstructed here: no such convex-combination structure is assumed of the general Borel state
space `E$ this book's series otherwise uses, and neither Proposition 7.5.11 nor Theorem 7.5.12's
own proof uses the interpolation formula itself, only the two structural facts recorded as fields
below; see `MODERATION_NOTES.md`). -/
structure GridApprox (M : MarkovDecisionModel E A) (IMc : Set (E → ℝ)) where
  bG : E → ℝ
  hbG_meas : Measurable bG
  hbG_ge1 : ∀ x, 1 ≤ bG x
  TG : (E → ℝ) → (E → ℝ)
  hTG_maps : ∀ v ∈ IMc, TG v ∈ IMc

/-- `\tilde m(h) := \|b-b_G\| = \sup_x |b(x)-b_G(x)|` (Bäuerle–Rieder, proof of Proposition
7.5.11, p. 221, PDF 232). -/
noncomputable def mtilde (b bG : E → ℝ) : ℝ :=
  ⨆ x, |b x - bG x|

/-- `\|v\|_G := \sup_x |v(x)|/b_G(x)` (Bäuerle–Rieder, p. 221, PDF 232). -/
noncomputable def normG (bG : E → ℝ) (v : E → ℝ) : ℝ :=
  ⨆ x, |v x| / bG x

/-- `\alpha_G := \sup_{(x,a) \in D} \int b_G(y)\,Q(dy|x,a) / b_G(x)` (Bäuerle–Rieder, p. 221, PDF
232-233). -/
noncomputable def alphaG (M : MarkovDecisionModel E A) (bG : E → ℝ) : ℝ :=
  ⨆ xa ∈ M.D, (∫ y, bG y ∂(M.Q xa)) / bG xa.1

end MDPFinance.LPDuality


