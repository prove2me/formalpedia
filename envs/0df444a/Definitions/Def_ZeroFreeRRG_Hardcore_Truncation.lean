-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_Truncation
-- name    : ZeroFreeRRG_Hardcore_Truncation
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T22:51:42.400524+00:00
-- url     : https://prove2.me/theorems/421b992d-3b32-4c38-96b0-162c5f9c17dd
-- title:
--   Real and complex truncation estimates for the typical-graph cutoff
-- statement:
--   For a positive reference parameter $x$, the cutoff event is $E_n=\{\mathcal Z_G(x)\le a_n(x)e^{\varepsilon n}\}$. `RealTruncationBound` packages four exponentially small real error sums: the untruncated first moment on $E_n^{\mathrm c}$, the local second moment on $E_n^{\mathrm c}$, and the out-of-box second moment on $E_n$ and on $E_n^{\mathrm c}$. These are the quantitative form of equation (76), including the additional outside-cutoff term used for analytic continuation.
--
--   `WeightComparison` records the configurationwise comparison of $\mathcal Z_G(z)$, $\mathcal Z^{(2)}_{G,B}(z,w)$, and $\mathcal Z_G(z)\mathcal Z_G(w)-\mathcal Z^{(2)}_{G,B}(z,w)$ with their positive values at $(x,x)$. `FirstMomentBounds` gives a uniform lower bound for $|a_n|$ on a disk and an upper bound for $a_n(x)$. `ComplexTruncationBound` is the conclusion (31) for a prescribed event and disk.
--
--   These interfaces separate Appendix E.4's real planted/profiling estimates from its deterministic complex-weight comparison.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), Appendix E.4, pp. 82–83 (printed), especially equations (76)–(77) and Step 4.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical

namespace ZeroFreeRRG.Hardcore

open AFIsingKS

/-- The cutoff graph event used in Appendix E.4: the normalized partition function at the
positive real parameter `x` is at most `a_n(x) exp (ε n)`. -/
noncomputable def partitionCutoff (m : Model) (x : ℝ) (d n : ℕ) (ε : ℝ) :
    Set (Matching n d) :=
  {M | normZ m x M ≤ an m d n x * Real.exp (ε * n)}

/-- Quantitative real-parameter truncation errors. The four sums are respectively the untruncated
weight outside `E`, the in-box second moment outside `E`, and the out-of-box second moment inside
and outside `E`. At a positive parameter all four quantities are nonnegative, so the norms do not
change the real error sums. -/
def RealTruncationBound (m : Model) (d : ℕ) (x : ℝ)
    (B : Set (m.Spin × m.Spin → ℝ)) (E : ∀ n : ℕ, Set (Matching n d))
    (c C : ℝ) (N : ℕ) : Prop :=
  ∀ n ≥ N, Even (n * d) →
    cmE (fun M : Matching n d => if M ∉ E n then (normZ m x M : ℝ) else 0) ≤
        C * Real.exp (-c * n) * an m d n x ∧
    ‖cmE (fun M : Matching n d => if M ∉ E n then Z2 m B (x : ℂ) (x : ℂ) M else 0)‖ ≤
        C * Real.exp (-c * n) * (an m d n x) ^ 2 ∧
    ‖cmE (fun M : Matching n d =>
        if M ∈ E n then normZ m (x : ℂ) M ^ 2 - Z2 m B (x : ℂ) (x : ℂ) M else 0)‖ ≤
        C * Real.exp (-c * n) * (an m d n x) ^ 2 ∧
    ‖cmE (fun M : Matching n d =>
        if M ∉ E n then normZ m (x : ℂ) M ^ 2 - Z2 m B (x : ℂ) (x : ℂ) M else 0)‖ ≤
        C * Real.exp (-c * n) * (an m d n x) ^ 2

/-- Uniform comparison of the three complex configuration sums with their positive real
counterparts. The constants do not depend on `n`, the pairing, or the spin configurations. -/
def WeightComparison (m : Model) (d : ℕ) (t x : ℝ)
    (B : Set (m.Spin × m.Spin → ℝ)) (A k R : ℝ) : Prop :=
  0 < A ∧ 0 < k ∧ 0 < R ∧
    ∀ (n : ℕ) (M : Matching n d) (z : ℂ), z ∈ Metric.ball (t : ℂ) R →
      ∀ w : ℂ, w ∈ Metric.ball (t : ℂ) R →
        ‖normZ m z M‖ ≤ A * Real.exp (k * n) * (normZ m x M : ℝ) ∧
        ‖Z2 m B z w M‖ ≤ A * Real.exp (k * n) * ‖Z2 m B (x : ℂ) (x : ℂ) M‖ ∧
        ‖normZ m z M * normZ m w M - Z2 m B z w M‖ ≤
          A * Real.exp (k * n) *
            ‖(normZ m (x : ℂ) M) ^ 2 - Z2 m B (x : ℂ) (x : ℂ) M‖

/-- Uniform lower bounds for the complex first moment near `t`, together with an upper bound at
the positive comparison parameter `x`. -/
def FirstMomentBounds (m : Model) (d : ℕ) (t x : ℝ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ A₀ : ℝ, ∃ N : ℕ,
    ∀ n ≥ N, Even (n * d) →
      (∀ z ∈ Metric.ball (t : ℂ) R, a₀ ≤ ‖an m d n z‖) ∧ an m d n x ≤ A₀

/-- The three complex moment estimates in Lemma 4.21 for a prescribed truncation and disk. -/
def ComplexTruncationBound (m : Model) (d : ℕ) (t : ℝ)
    (B : Set (m.Spin × m.Spin → ℝ)) (E : ∀ n : ℕ, Set (Matching n d))
    (R γ C : ℝ) (N : ℕ) : Prop :=
  ∀ n ≥ N, Even (n * d) →
    ‖cmE (fun M : Matching n d =>
        if M ∈ E n then normZ m (t : ℂ) M ^ 2 - Z2 m B t t M else 0)‖ ≤
      C * Real.exp (-γ * n) * ‖an m d n (t : ℂ)‖ ^ 2 ∧
    ∀ z ∈ Metric.ball (t : ℂ) R, ∀ w ∈ Metric.ball (t : ℂ) R,
      ‖cmE (fun M : Matching n d => if M ∈ E n then normZ m z M else 0) - an m d n z‖ ≤
          C * Real.exp (-γ * n) * ‖an m d n z‖ ∧
      ‖cmE (fun M : Matching n d =>
          (if M ∈ E n then normZ m z M else 0) * (if M ∈ E n then normZ m w M else 0)) -
        cmE (fun M : Matching n d => Z2 m B z w M)‖ ≤
          C * Real.exp (-γ * n) * ‖an m d n z * an m d n w‖

end ZeroFreeRRG.Hardcore


