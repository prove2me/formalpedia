-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
-- name    : PrivateContinualCounting_Kraft_LTIFactors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:56.891713+00:00
-- url     : https://prove2.me/theorems/92c1d2cd-1475-4d5f-b150-fe152b130586
-- title:
--   Scalar/vector LTI coefficients and their Gaussian releases
-- statement:
--   For $m\ge1$, let $l_j$ be row vectors and $r_k$ column vectors in $\mathbb R^m$ or $\mathbb C^m$, indexed from zero. Admissibility means
--   $$\sum_{j=0}^s\sum_{q=1}^m l_{j,q}r_{s-j,q}=1\quad(s\ge0),\qquad
--   \Delta^2=\sum_{k\ge0}\sum_q|r_{k,q}|^2<\infty.$$
--   The pairing is bilinear even over $\mathbb C$. Define $E_t=\sum_{j<t}\sum_q|l_{j,q}|^2$ and $v_t=\Delta^2E_t$. There is no sign restriction and no requirement that the full decoder sequence belong to $H^2$. Real coefficients give Toeplitz matrices $L_{t,(i,q)}=l_{t-i,q}$ for $i\le t$ and $R_{(i,q),j}=r_{i-j,q}$ for $i\ge j$, zero elsewhere. One independent Gaussian product seed defines all releases
--   $$Y_t=S_t+\frac\Delta\mu\sum_{i=1}^t\sum_q l_{t-i,q}Z_{i,q},\qquad \mu>0.$$
--   Their finite transcript laws are included. A scalar counter has $m=1$. Appendix A's realification is defined by $\widetilde l=[\Re l,-\Im l]$ and $\widetilde r=[\Re r;\Im r]$. These definitions separate formal complex factors from the actual real mechanism. All vector norms are Euclidean coordinate sums.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 6, PDF p. 8, Definition 2.2; Kisung Park, STOC 2027 submission #86 (October 2026), p. 18, PDF p. 20, Appendix A, complex realification

import Definitions.Def_PrivateContinualCounting_Kraft_GaussianCounter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Raw scalar/vector coefficient data, without a positivity restriction. -/
structure LTIData (𝕜 : Type) (m : ℕ) where
  l : ℕ → Fin m → 𝕜
  r : ℕ → Fin m → 𝕜

/-- Euclidean squared norm, also for complex vectors. The Pi supremum norm is not used. -/
noncomputable def vectorSq {𝕜 : Type} [NormedAddCommGroup 𝕜] {m : ℕ}
    (a : Fin m → 𝕜) : ℝ := ∑ q, ‖a q‖ ^ 2

/-- Formal convolution uses the bilinear row-column product, without conjugation. -/
def IsLTI {𝕜 : Type} [RCLike 𝕜] {m : ℕ} (d : LTIData 𝕜 m) : Prop :=
  0 < m ∧
  (∀ s : ℕ, (∑ j ∈ Finset.range (s + 1), ∑ q, d.l j q * d.r (s - j) q) = 1) ∧
  Summable (fun k => vectorSq (d.r k))

noncomputable def LTIData.deltaSq {𝕜 : Type} [RCLike 𝕜] {m : ℕ}
    (d : LTIData 𝕜 m) : ℝ := ∑' k, vectorSq (d.r k)

noncomputable def LTIData.energy {𝕜 : Type} [RCLike 𝕜] {m : ℕ}
    (d : LTIData 𝕜 m) (t : ℕ) : ℝ := ∑ j ∈ Finset.range t, vectorSq (d.l j)

noncomputable def LTIData.variance {𝕜 : Type} [RCLike 𝕜] {m : ℕ}
    (d : LTIData 𝕜 m) (t : ℕ) : ℝ := d.deltaSq * d.energy t

/-- The real finite-channel counters in Definition 2.2. -/
abbrev LTICounter (m : ℕ) := {d : LTIData ℝ m // IsLTI d}

/-- Actual lower-triangular Toeplitz decoder. Both time coordinates here are zero-based. -/
def ltiDecoder {m : ℕ} (d : LTIData ℝ m) (t : ℕ) (iq : ℕ × Fin m) : ℝ :=
  if iq.1 ≤ t then d.l (t - iq.1) iq.2 else 0

def ltiStrategy {m : ℕ} (d : LTIData ℝ m) (iq : ℕ × Fin m) (j : ℕ) : ℝ :=
  if j ≤ iq.1 then d.r (iq.1 - j) iq.2 else 0

/-- Canonical finite-row Gaussian sum: one seed for all times and all streams. -/
noncomputable def LTICounter.release {m : ℕ} (M : LTICounter m)
    (μ : Set.Ioi (0 : ℝ)) (x : Stream) (t : ℕ) (ω : ℕ × Fin m → ℝ) : ℝ :=
  prefixSum x t + Real.sqrt M.val.deltaSq / (μ : ℝ) *
    ∑ i ∈ Finset.range t, ∑ q, M.val.l (t - 1 - i) q * ω (i, q)

noncomputable def LTICounter.transcriptLaw {m : ℕ} (M : LTICounter m)
    (μ : Set.Ioi (0 : ℝ)) (x : Stream) (n : ℕ) : Measure (Fin n → ℝ) :=
  (gaussianSeed (ℕ × Fin m)).map (fun ω k => M.release μ x (k.val + 1) ω)

/-- Appendix A realification [Re l,-Im l] and [Re r;Im r]. -/
def realify {m : ℕ} (d : LTIData ℂ m) : LTIData ℝ (m + m) where
  l j q := if h : q.val < m then (d.l j ⟨q.val, h⟩).re
    else -(d.l j ⟨q.val - m, by omega⟩).im
  r k q := if h : q.val < m then (d.r k ⟨q.val, h⟩).re
    else (d.r k ⟨q.val - m, by omega⟩).im

end PrivateContinualCounting.Kraft


