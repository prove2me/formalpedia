-- Prove2me | Definitions.Def_MomentSearch_Supplement_quantileDist
-- name    : MomentSearch_Supplement_quantileDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:30:36.034422+00:00
-- url     : https://prove2.me/theorems/6933ebd9-78a4-481b-80f5-9fc89405bf49
-- title:
--   $q$-quantiles, the quantile sketch and the distribution with mass $1/q$ at each quantile
-- statement:
--   For an integer $q\ge1$ and $p\in\Delta_n$ with CDF $P$, the **$\ell$-th $q$-quantile** is
--   $$x_\ell=\min\{t\in[n]_0: P(t)\ge \ell/q\},\qquad \ell=1,\dots,q .$$
--   The **quantile sketch** maps $p$ to $(x_1,\dots,x_q)\in[n]_0^q$. For any tuple $(x_1,\dots,x_q)$, the associated distribution places mass $1/q$ at each entry, adding masses when entries repeat:
--   $$\pi_t=\frac{|\{\ell: x_\ell=t\}|}{q}.$$
--   Applied to the quantile sketch of $p$, this is the distribution constructed in Theorem 8; it depends on $p$ only through its quantiles.
--
--   **Formalization Note** The minimum is a natural-number infimum; for $p\in\Delta_n$, $n\ge1$ and $1\le\ell\le q$ the set is nonempty because $P(n-1)=1$, so the junk value of an empty infimum is never used.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), §3.2, p.9 (PDF p.11); proof of Theorem 8, App. B.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MomentSearch_Supplement_cdf

namespace MomentSearch.Supplement

/-- The `ℓ`-th `q`-quantile `x_ℓ := min{t ∈ [n]₀ : P(t) ≥ ℓ/q}` of a distribution `p ∈ Δ_n`
(Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the
Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §3.2, p.9 (PDF p.11)).

**Formalization Note.** A natural-number `sInf`. For `p ∈ Δ_n`, `n ≥ 1` and `1 ≤ ℓ ≤ q` the set
is nonempty (`P(n − 1) = 1 ≥ ℓ/q`), so this is the paper's minimum; the junk value `0` of an
empty set is never used. -/
noncomputable def quantile {n : ℕ} (p : Fin n → ℝ) (q ℓ : ℕ) : ℕ :=
  sInf {t : ℕ | t < n ∧ (ℓ : ℝ) / q ≤ cdf p t}

/-- The `q`-quantile sketch `p ↦ (x_1, …, x_q) ∈ [n]₀^q` (arXiv:2611.04559, held version,
§3.2, p.9 (PDF p.11)); the entry with index `ℓ : Fin q` is `x_{ℓ+1}`. -/
noncomputable def quantileSketch (n q : ℕ) (p : Fin n → ℝ) : Fin q → ℕ :=
  fun ℓ => quantile p q ((ℓ : ℕ) + 1)

/-- The distribution placing mass `1/q` at each entry of a tuple `(x_1, …, x_q)`, adding masses
when entries repeat: `π_t = |{ℓ : x_ℓ = t}|/q` (arXiv:2611.04559, held version, §3.2, p.9
(PDF p.11), and proof of Theorem 8, p.18 (PDF p.20)). Applied to the quantile sketch, this is the
distribution of Theorem 8, which depends on `p` only through its quantiles. -/
noncomputable def quantileDist (n q : ℕ) (x : Fin q → ℕ) : Fin n → ℝ :=
  fun t => ((Finset.univ.filter (fun ℓ : Fin q => x ℓ = (t : ℕ))).card : ℝ) / q

end MomentSearch.Supplement


