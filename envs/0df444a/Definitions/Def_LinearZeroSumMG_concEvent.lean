-- Prove2me | Definitions.Def_LinearZeroSumMG_concEvent
-- name    : LinearZeroSumMG_concEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:54:05.665978+00:00
-- url     : https://prove2.me/theorems/cf6924f0-c982-406c-91cd-9a86385167ed
-- title:
--   The concentration event $\mathfrak E$ of Lemma 2, with explicit constant
-- statement:
--   For a constant $C\ge0$, the event $\mathfrak E(C)$ holds along a data sequence if, for all $(k,h)\in[K]\times[H]$,
--   $$
--   \Big\|\sum_{\tau=1}^{k-1}\phi^\tau_h\Big[\overline V^k_{h+1}(x^\tau_{h+1})-(\mathbb P_h\overline V^k_{h+1})(x^\tau_h,a^\tau_h,b^\tau_h)\Big]\Big\|_{(\Lambda^k_h)^{-1}}\le C\,dH\sqrt{\log(dT/p)}
--   $$
--   and the same bound holds with $\underline V^k_{h+1}$ in place of $\overline V^k_{h+1}$.
--
--   On this event the least-squares estimates of Algorithm 1 are accurate (Lemma 3), which drives the whole analysis.
--
--   **Formalization Note** The paper writes $\lesssim$; the hidden constant is the explicit argument $C$, and Lemma 2 states how large it must be. $\overline V^k_{H+1}=\underline V^k_{H+1}\equiv0$.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 2, p.17

import Mathlib
import Definitions.Def_LinearZeroSumMG_omni
import Definitions.Def_LinearZeroSumMG_Vval

namespace LinearZeroSumMG

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}

/-- **The concentration event `𝔈` of Lemma 2, with constant `C`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 2, p.17: "the following event
`𝔈` …:
`‖∑_{τ∈[k−1]} φ^τ_h [V̄^k_{h+1}(x^τ_{h+1}) − (ℙ_h V̄^k_{h+1})(x^τ_h, a^τ_h, b^τ_h)]‖_{(Λ^k_h)⁻¹} ≲ dH√(log(dT/p))`, `∀(k, h) ∈ [K] × [H]`,
`‖∑_{τ∈[k−1]} φ^τ_h [V̲^k_{h+1}(x^τ_{h+1}) − (ℙ_h V̲^k_{h+1})(x^τ_h, a^τ_h, b^τ_h)]‖_{(Λ^k_h)⁻¹} ≲ dH√(log(dT/p))`, `∀(k, h) ∈ [K] × [H]`."

`concEvent G P K p C xs as bs` is the statement that both families of bounds hold along the data
`xs`, `as`, `bs`, with right-hand side `C · d · H · √(log(dT/p))`, `T = KH`.

**Formalization Note** The `≲` of the paper hides a universal constant; here it is the explicit
argument `C`, and Lemma 2 says how large `C` must be. `log` is `Real.log`, `‖v‖_M` is
`√(vᵀMv)` (`wNorm`), and `V̄^k_{H+1} = V̲^k_{H+1} ≡ 0`. -/
def concEvent (G : MarkovGame S A) (P : OmniParams S A d) (K : ℕ) (p C : ℝ)
    (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A) : Prop :=
  ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 G.H,
    wNorm (gram P.φ xs as bs k h)⁻¹
        (∑ τ ∈ Finset.Ico 1 k,
          (VUp G P xs as bs k (h + 1) (xs τ (h + 1)) -
            transOp G h (VUp G P xs as bs k (h + 1)) (xs τ h) (as τ h) (bs τ h)) •
            feat P.φ xs as bs τ h)
        ≤ C * d * G.H * Real.sqrt (Real.log (d * ((K : ℝ) * G.H) / p)) ∧
    wNorm (gram P.φ xs as bs k h)⁻¹
        (∑ τ ∈ Finset.Ico 1 k,
          (VLo G P xs as bs k (h + 1) (xs τ (h + 1)) -
            transOp G h (VLo G P xs as bs k (h + 1)) (xs τ h) (as τ h) (bs τ h)) •
            feat P.φ xs as bs τ h)
        ≤ C * d * G.H * Real.sqrt (Real.log (d * ((K : ℝ) * G.H) / p))

end LinearZeroSumMG


