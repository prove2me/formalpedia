-- Prove2me | Definitions.Def_OrderedExperts_Supplement_Algorithm3Run
-- name    : OrderedExperts_Supplement_Algorithm3Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:47:33.006021+00:00
-- url     : https://prove2.me/theorems/ae881429-96a8-49ce-968c-4315ff5d8a48
-- title:
--   Algorithm 3 — endpoint flow with robust mirror descent
-- statement:
--   **Algorithm 3** starts from uniform expert weights. On every round it aggregates those weights onto the current active ranks, smooths the rank distribution by $1/T$, and samples a paid pair using the endpoint-flow kernel. From the two aggregate BV losses it forms the endpoint-flow estimate and performs robust mirror descent on the open simplex with
--
--   $$
--   \Psi(w)=\sum_f w(f)\log w(f)-\mu\sum_f\log w(f).
--   $$
--
--   An `Algorithm3Run` records the conditional pair law and the weight vector at every possible observation history, with the exact minimization update required by the algorithm.
--
--   **Formalization Note** The history contains only aggregate BV losses and never a monotone decomposition. Active ranks are 1-based, and the sampled pair has law $\pi(a)\kappa(a,b)$.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Algorithm 3, p. 13; Sec. 5.1, pp. 12–13

import Definitions.Def_OrderedExperts_Supplement_TwoPointPolicy
import Definitions.Def_OrderedExperts_chainSize
import Definitions.Def_OrderedExperts_rank
import Definitions.Def_OrderedExperts_kappa
import Definitions.Def_OrderedExperts_est

open Finset

namespace OrderedExperts.Supplement

/-- **Algorithm 3: endpoint flow with robust mirror descent.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Algorithm 3, p. 13, and Sec. 5.1, pp. 12--13.

An `Algorithm3Run A n T η μ` packages the two-point conditional law and the expert weights at
every possible BV-feedback history.  The initial weights are uniform.  At each history, they are
aggregated onto active ranks, smoothed by `1/T`, and passed to the published endpoint-flow pair
kernel.  After observing the two aggregate losses, the next full-support weight vector minimizes
the robust mirror-descent objective with negative entropy plus the log barrier of weight `μ`.

**Formalization Note.** The history contains only the two aggregate BV losses, never a monotone
decomposition.  The explicit divergence in `update_min` is the Bregman divergence of
`Ψ(w) = ∑_f w(f) log w(f) - μ ∑_f log w(f)` on the open simplex; the affine terms of the
entropy divergence cancel because both vectors sum to one.  Ranks are 1-based and the pair law is
exactly `π(a) κ(a,b)`. -/
structure Algorithm3Run (A : Type*) (n T : ℕ) [LinearOrder A] [OrderBot A]
    (η μ : ℝ) where
  policy : TwoPointPolicy A n (ℝ × ℝ)
  weight : List ((Fin n → A) × ℕ × ℕ × (ℝ × ℝ)) → Fin n → ℝ
  weight_pos : ∀ h f, 0 < weight h f
  weight_sum : ∀ h, ∑ f, weight h f = 1
  initial : ∀ f, weight [] f = 1 / (n : ℝ)
  select : ∀ current h, ∀ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
    ∀ b ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
      let rs : ℕ → Fin n → A := fun _ ↦ current
      let m := chainSize rs 0
      let p : ℕ → ℝ := fun j ↦
        ∑ f ∈ Finset.univ.filter (fun f ↦ rank rs 0 f = j), weight h f
      let π : ℕ → ℝ := fun j ↦
        (1 - 1 / (T : ℝ)) * p j + (1 / (T : ℝ)) / (m : ℝ)
      policy.mass current h a b = π a * kappa m (1 / (T : ℝ)) π a b
  update_min : ∀ current h, ∀ a ∈ Icc 1 (chainSize (fun _ ↦ current) 0),
    ∀ b ∈ Icc 1 (chainSize (fun _ ↦ current) 0), ∀ yA yB : ℝ,
    ∀ v : Fin n → ℝ, (∀ f, 0 < v f) → ∑ f, v f = 1 →
      let rs : ℕ → Fin n → A := fun _ ↦ current
      let m := chainSize rs 0
      let p : ℕ → ℝ := fun j ↦
        ∑ f ∈ Finset.univ.filter (fun f ↦ rank rs 0 f = j), weight h f
      let π : ℕ → ℝ := fun j ↦
        (1 - 1 / (T : ℝ)) * p j + (1 / (T : ℝ)) / (m : ℝ)
      let g : ℕ → ℝ := fun j ↦ if j = a then yA else if j = b then yB else 0
      let next := weight (h ++ [(current, a, b, (yA, yB))])
      (∑ f, (next f * Real.log (next f / weight h f) +
          μ * (next f / weight h f - 1 - Real.log (next f / weight h f)))) +
          η * ∑ f, next f * est m (1 / (T : ℝ)) π g a b (rank rs 0 f) ≤
        (∑ f, (v f * Real.log (v f / weight h f) +
          μ * (v f / weight h f - 1 - Real.log (v f / weight h f)))) +
          η * ∑ f, v f * est m (1 / (T : ℝ)) π g a b (rank rs 0 f)

end OrderedExperts.Supplement


