-- Prove2me | Definitions.Def_PrettyGoodShadow_alg1Law
-- name    : PrettyGoodShadow_alg1Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:28.121656+00:00
-- url     : https://prove2.me/theorems/01c7d4bd-e581-441b-a74e-c0a390364797
-- title:
--   Algorithm 1: outcome law, error probability and $e_q(x)$
-- statement:
--   Algorithm 1 is given a prior and integers $k,T\ge1$. It samples $t$ uniformly from $\{T,\dots,2T-1\}$, applies the integral pretty good measurement of the prior to $kt$ copies of the input, and outputs $\hat o_i=\operatorname{tr}(O_i\rho_{\hat x})$. On input $\rho_x$ the label has the law
--
--   $$
--   \Pr[\hat x=y]=\frac1T\sum_{t=T}^{2T-1}\Pr[\text{the PGM on }kt\text{ copies outputs }y].
--   $$
--
--   For one observable $A$ this module defines the error probability $\Pr_{\hat o\sim\mathcal A(x)}[|\hat o-\operatorname{tr}(A\rho_x)|>\varepsilon]$, and for $O_1,\dots,O_m$ and a prior $q$ the largest error $e_q(x)=\max_{i\in[m]}\Pr[|\hat o_i-\operatorname{tr}(O_i\rho_x)|>\varepsilon\mid x]$.
--
--   **Formalization Note** The maximum is a supremum over a finite index set, which is a maximum as soon as $m\ge1$.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Algorithm 1, p.18; Lemma 4.3, p.18; Appendix A, p.31

import Mathlib
import Definitions.Def_PrettyGoodShadow_pgmEffect

namespace PrettyGoodShadow

/-- **Outcome law of Algorithm 1** on input `ρ_x` (arXiv:2610.06781, sha256 bd055b7d…, Algorithm 1, p.18):
sample `t` uniformly from `{T, …, 2T − 1}`, set `n = k t`, and apply the integral PGM of the prior `p` to `n`
copies, so `Pr[x̂ = y] = (1/T) Σ_{t=T}^{2T−1} Pr[PGM on kt copies outputs y]`.

**Formalization Note** `Finset.Ico T (2 * T)` has exactly `T` elements. `T = 0` gives the zero vector and is
excluded wherever the law is used. -/
noncomputable def alg1Law {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (k T : ℕ) (x y : L) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.Ico T (2 * T), pgmLaw p ρ (k * t) x y

/-- **Error probability of Algorithm 1 for one observable** (arXiv:2610.06781, sha256 bd055b7d…, Lemma 4.3,
p.18): `Pr_{ô ∼ A(x)}[|ô − tr(A ρ_x)| > ε]`, where the output is `ô = tr(A ρ_x̂)` (Algorithm 1, step 3). -/
noncomputable def errProb {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (k T : ℕ) (A : Matrix d d ℂ) (ε : ℝ) (x : L) : ℝ :=
  ∑ y with ε < |obs A (ρ y) - obs A (ρ x)|, alg1Law p ρ k T x y

/-- **The largest conditional error probability** `e_q(x) = max_{i ∈ [m]} Pr[|ô_i − tr(O_i ρ_x)| > ε | x = x]`,
Algorithm 1 being run with prior `q` (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.31).

**Formalization Note** A supremum over the finite index `Fin m`, so it is a maximum whenever `1 ≤ m`, which
every statement using it assumes. -/
noncomputable def maxErr {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] {m : ℕ} (q : L → ℝ)
    (ρ : L → Matrix d d ℂ) (O : Fin m → Matrix d d ℂ) (k T : ℕ) (ε : ℝ) (x : L) : ℝ :=
  ⨆ i : Fin m, errProb q ρ k T (O i) ε x

end PrettyGoodShadow


