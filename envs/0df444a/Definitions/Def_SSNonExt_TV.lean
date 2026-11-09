-- Prove2me | Definitions.Def_SSNonExt_TV
-- name    : SSNonExt_TV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:32.83199+00:00
-- url     : https://prove2.me/theorems/9b351644-9378-443a-9c70-9cd7b97fe028
-- title:
--   Total variation distance $\mathrm{TV}$, min-entropy $H_\infty$ and flat distributions
-- statement:
--   Let $X$ be a finite set and $P,P'$ probability distributions on $X$. The **total variation distance** (statistical distance) is
--
--   $$\mathrm{TV}(P,P')=\frac12\sum_{x\in X}|P(x)-P'(x)|.$$
--
--   For a random variable $Y=f(K)$ with $K\sim P$ one writes $\mathrm{TV}(f(K),P')$ for the distance between the law of $f(K)$ (the push-forward of $P$ along $f$) and $P'$. The **min-entropy** of $P$ (for nonempty $X$) is
--
--   $$H_\infty(P)=-\log_2\max_{x\in X}P(x),$$
--
--   all logarithms being base two. A distribution is **flat** if it is uniform on a nonempty subset of $X$.
--
--   These are the three measurements of Theorem 1.1: privacy is a total variation distance between share laws, the sources are flat with large min-entropy, and the extraction error is a total variation distance from uniform.
--
--   **Formalization Note** $\mathrm{TV}$ is the published `IsingLTL.BeliefProp.tvDist` (the $\tfrac12\ell^1$ normalization) applied to the real values of two `PMF`s; the values of a `PMF` are at most $1$, so passing from $\mathbb R_{\ge0}^\infty$ to $\mathbb R$ loses nothing. The maximum in $H_\infty$ is a finite maximum over the nonempty type.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §2, p.5 (PDF p.5)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace SSNonExt

/-- **Total variation distance** between two probability mass functions on a finite set (§2, p.5):
`TV(P, P′) = ½ ∑ₓ |P(x) − P′(x)|`.
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §2, p.5 (PDF p.5).

**Formalization Note.** This is the published `IsingLTL.BeliefProp.tvDist` (`(∑ x, |p x − q x|) / 2`)
applied to the real values of the two mass functions. The values of a `PMF` lie in `ℝ≥0∞` and are at
most `1`, so `ENNReal.toReal` loses nothing. "TV(Ext(K), U_ℓ), K ∼ P" is `TV (P.map Ext) U`. -/
noncomputable def TV {X : Type*} [Fintype X] (P Q : PMF X) : ℝ :=
  IsingLTL.BeliefProp.tvDist (fun x => (P x).toReal) (fun x => (Q x).toReal)

/-- **Min-entropy** `H∞(P) = −log₂ maxₓ P(x)` of a distribution on a finite nonempty set (§2, p.5,
"All logarithms are base two").
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §2, p.5.

**Formalization Note.** The maximum is `Finset.sup'` over the (nonempty) finite type, so it is a true
maximum; the logarithm is `Real.logb 2`. -/
noncomputable def minEntropy {X : Type*} [Fintype X] [Nonempty X] (P : PMF X) : ℝ :=
  -Real.logb 2 (Finset.univ.sup' Finset.univ_nonempty fun x => (P x).toReal)

/-- A **flat** distribution is uniform on a nonempty subset of its domain (§2, p.5).
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §2, p.5. -/
def IsFlat {X : Type*} (P : PMF X) : Prop :=
  ∃ (Z : Finset X) (hZ : Z.Nonempty), P = PMF.uniformOfFinset Z hZ

end SSNonExt


