-- Prove2me | Definitions.Def_FiniteMemPOMDP_dKR
-- name    : FiniteMemPOMDP_dKR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:12.957047+00:00
-- url     : https://prove2.me/theorems/5bdcaf93-4d9f-4e0a-a832-ed314e142ffa
-- title:
--   Kantorovich–Rubinstein distance $d_{KR}$ on $\Delta(\Delta(\mathcal K))$
-- statement:
--   For $z,z'\in\Delta(\Delta(\mathcal K))$,
--
--   $$d_{KR}(z,z')=\sup_{f\in\mathcal E_1}\Big|\int_{\Delta(\mathcal K)}f(p)\,z(dp)-\int_{\Delta(\mathcal K)}f(p)\,z'(dp)\Big|,$$
--
--   where $\mathcal E_1$ is the set of $1$-Lipschitz functions from $\Delta(\mathcal K)$ to $[0,1]$.
--
--   **Formalization Note** The paper does not name the metric on $\Delta(\mathcal K)$; the mission uses $\|p-p'\|_1=\sum_k|p(k)-p'(k)|$, the norm of Lemma 5.3. Lipschitz in $\|\cdot\|_1$ is the weakest of the usual conditions, so this $d_{KR}$ is the largest of the candidates and a bound $d_{KR}\le\varepsilon$ is the strongest. $\mathcal E_1$ contains $f=0$ and every term is at most $1$ for probability measures, so the supremum is genuine.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition A.6, p.23

import Mathlib

open MeasureTheory

namespace FiniteMemPOMDP

variable {K : Type} [Fintype K]

/-- **The Kantorovich–Rubinstein distance on `∆(∆(K))`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition A.6, p.23: "For all
z, z′ ∈ ∆(∆(K)), define d_KR(z, z′) := sup_{f∈E1} | ∫_{∆(K)} f(p) z(dp) − ∫_{∆(K)} f(p) z′(dp) |,
where E1 is the set of 1-Lipschitz functions from ∆(K) to [0, 1]."

`dKR z z'` is the supremum of `|∫ f dz − ∫ f dz'|` over the functions `f : ∆(K) → [0, 1]` with
`|f(p) − f(p')| ≤ ‖p − p'‖₁ = ∑_k |p(k) − p'(k)|`.

**Formalization Note** The paper does not name the metric on `∆(K)`; the `ℓ¹` norm `‖·‖₁` is the
one of Lemma 5.3. A 1-Lipschitz condition in `‖·‖₁` is the weakest among the usual norms
(`‖·‖∞ ≤ ‖·‖₂ ≤ ‖·‖₁`), so `E1` is the largest class and `d_KR` the largest of the candidate
distances. The class contains `f = 0`, and for probability measures every term is at most `1`, so
the `⨆` is a genuine supremum; every `f ∈ E1` is continuous and bounded, hence integrable. -/
noncomputable def dKR (z z' : Measure (stdSimplex ℝ K)) : ℝ :=
  ⨆ f : {f : stdSimplex ℝ K → ℝ //
      (∀ p, f p ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ p p', |f p - f p'| ≤ ∑ k, |p.1 k - p'.1 k|},
    |∫ p, f.1 p ∂z - ∫ p, f.1 p ∂z'|

end FiniteMemPOMDP


