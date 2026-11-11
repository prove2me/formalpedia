-- Prove2me | Definitions.Def_SumReLU_events
-- name    : SumReLU_events
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:28.877276+00:00
-- url     : https://prove2.me/theorems/69d3bf0e-b644-4dba-a5fb-ba0b4fd1fef6
-- title:
--   The far set $A_{i^*}(\xi)$, the correlation and separation events (11), and the filter degree $p$
-- statement:
--   For unit vectors $w_1,\dots,w_k$, an index $i^*$ and $\xi>0$,
--   $$
--   A_{i^*}(\xi)=\{i\in[k]:|w_i\cdot w_{i^*}|\le1-\xi\}.
--   $$
--   For $Z>0$ and $p\ge1$ the correlation and separation events on probes $u\in\mathbb C^d$ are
--   $$
--   E^{\mathrm{Cor}}_{i^*}=\{u:|w_{i^*}\cdot u|\ge Z^{1/(2p)}\},\qquad E^{\mathrm{Sep}}_{i^*}=\{u:|w_{i^*}\cdot u|\ge(1+\xi)|w_j\cdot u|\ \ \forall j\in A_{i^*}(\xi)\}.
--   $$
--   The filter degree is $p=\lceil\log(k/\lambda)/\log(1+\xi)\rceil$ (natural logarithm).
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.2, (11), p.25 (PDF p.27); Lemma 4.13, p.34 (PDF p.36); Algorithm 7, line 4, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_SumReLU_CTensor

namespace SumReLU

/-- `A_{i*}(ξ) = {i ∈ [k] : |w_i · w_{i*}| ≤ 1 − ξ}`, the indices far from `w_{i*}`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.2, p.25 (PDF p.27). -/
def Aset {d k : ℕ} (ξ : ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) (i₀ : Fin k) : Set (Fin k) :=
  {i | |inner ℝ (w i) (w i₀)| ≤ 1 - ξ}

/-- The correlation event `E^{Cor}_{i*} = {u : |w_{i*} · u| ≥ (Z_p(U))^{1/(2p)}}` (Lemma 4.2, (11),
p.25, PDF p.27), with `Z = Z_p(U)`.

**Formalization Note.** `Real.rpow`; every use has `Z > 0` and `p ≥ 1`. -/
def corrEvent {d k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin d)) (i₀ : Fin k) (p : ℕ) (Z : ℝ) :
    Set (Fin d → ℂ) :=
  {u | Z ^ (1 / (2 * (p : ℝ))) ≤ ‖dotC (w i₀) u‖}

/-- The separation event `E^{Sep}_{i*} = {u : |w_{i*} · u| ≥ (1 + ξ)|w_j · u|, ∀ j ∈ A_{i*}(ξ)}`
(Lemma 4.2, (11), p.25, PDF p.27). -/
def sepEvent {d k : ℕ} (ξ : ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) (i₀ : Fin k) :
    Set (Fin d → ℂ) :=
  {u | ∀ j ∈ Aset ξ w i₀, (1 + ξ) * ‖dotC (w j) u‖ ≤ ‖dotC (w i₀) u‖}

/-- The filter degree `p = ⌈log(k/λ)/log(1 + ξ)⌉` (Lemma 4.2, p.25; Lemma 4.13, p.34; Algorithm 7,
line 4), natural logarithm. -/
noncomputable def degree (ξ : ℝ) (k : ℕ) (lam : ℝ) : ℕ :=
  ⌈Real.log (k / lam) / Real.log (1 + ξ)⌉₊

end SumReLU


