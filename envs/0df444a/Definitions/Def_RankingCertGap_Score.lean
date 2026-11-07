-- Prove2me | Definitions.Def_RankingCertGap_Score
-- name    : RankingCertGap_Score
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:43.57944+00:00
-- url     : https://prove2.me/theorems/a2e4a3d2-987b-438f-a1a2-54cf3e8f4930
-- title:
--   The rank law, $\mathbb E[\mathrm{RANKING}(G)]$, the endpoint score $\Phi_G(i,j;f)$ and the conditional safety probabilities
-- statement:
--   The offline ranks are independent and uniform on $[0,1]$; $\mu_m$ denotes their joint law on $\mathbb R^m$. Then $\mathbb E[\mathrm{RANKING}(G)]$ is the integral of the matching cardinality under $\mu_m$. For a gain-sharing function $f$ and an edge $(i,j)$, the **expected endpoint score** is
--
--   $$
--   \Phi_G(i,j;f):=\mathbb E[f(Y_i)X_i]+\mathbb E[(1-f(Y_j))X_j].
--   $$
--
--   This is the quantity the protocol's expected edgewise dual-feasibility criterion controls.
--
--   The **conditional safety probability** $\Pr[\mathcal E_i\mid Y_i=y]$ is taken in the version the source fixes: the rank of $i$ is set to $y$, and the remaining ranks are sampled independently and uniformly. The same holds for two fixed ranks.
--
--   **Formalization Note** The conditional probabilities are explicit integrals with one coordinate overwritten, not conditional expectations, which would be defined only almost everywhere and could not carry "for every $y$". The verification file proves that both integrands of $\Phi$ are integrable for every $f\in\mathcal A$, so the integrals are not junk.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), §1, p.1; eq. (3), p.3; Corollary 1, p.17; eq. (39), p.18

import Mathlib
import Definitions.Def_RankingCertGap_RankingRun

open MeasureTheory

namespace RankingCertGap

variable {m n : ℕ}

/-- The law of the offline ranks: independent uniform ranks in `[0, 1]`. Xu, arXiv:2610.17545
(held file sha256 75896dd9…), §1, p.1. It is a probability measure on `Fin m → ℝ`, and each
coordinate lies in `[0, 1]` almost surely. -/
noncomputable def rankMeasure (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Set.Icc 0 1)

namespace Inst

/-- `E[RANKING(G)]`, with the expectation over the independent offline ranks (§1.1, p.2). -/
noncomputable def rankingValue (G : Inst m n) : ℝ :=
  ∫ Y, (G.rankingCard Y : ℝ) ∂rankMeasure m

/-- The expected endpoint score, Xu, arXiv:2610.17545 (held file sha256 75896dd9…), eq. (3), p.3:
`Φ_G(i, j; f) := E[f(Y_i) X_i] + E[(1 − f(Y_j)) X_j]`.

**Formalization Note.** The Bochner integrals are of bounded measurable functions whenever `f` is
Borel; the verification file proves integrability, so neither integral takes its junk value. -/
noncomputable def Phi (G : Inst m n) (i : Fin m) (j : Fin n) (f : ℝ → ℝ) : ℝ :=
  (∫ Y, f (Y i) * G.Xoff Y i ∂rankMeasure m) +
    ∫ Y, (1 - f (G.partnerRank Y j)) * G.Xon Y j ∂rankMeasure m

/-- The safety event `E_i` after the arrival prefix of length `t`, as a set of rank vectors (p.17). -/
def safeEvent (G : Inst m n) (t : ℕ) (i : Fin m) : Set (Fin m → ℝ) := {Y | G.safeAfter Y t i}

/-- `Pr[E_i | Y_i = y]`, in the version of p.17: "specified ranks are fixed, and the remaining ranks
are sampled independently and uniformly on `[0, 1]`". The coordinate `i` is overwritten by `y`, and
the other coordinates are integrated out.

**Formalization Note.** This is not a `condExp`: a conditional expectation is defined only almost
everywhere and could not carry "for every `y`". -/
noncomputable def condSafe (G : Inst m n) (t : ℕ) (i : Fin m) (y : ℝ) : ℝ :=
  (rankMeasure m).real {Y | G.safeAfter (Function.update Y i y) t i}

/-- `Pr[E_{i₁} ∩ E_{i₂} | Y_{i₁} = x, Y_{i₂} = y]`, in the same version: both coordinates are
overwritten and the others integrated out (eq. (39), p.18). -/
noncomputable def condSafePair (G : Inst m n) (t : ℕ) (i₁ i₂ : Fin m) (x y : ℝ) : ℝ :=
  (rankMeasure m).real
    {Y | G.safeAfter (Function.update (Function.update Y i₁ x) i₂ y) t i₁ ∧
      G.safeAfter (Function.update (Function.update Y i₁ x) i₂ y) t i₂}

end Inst

end RankingCertGap


