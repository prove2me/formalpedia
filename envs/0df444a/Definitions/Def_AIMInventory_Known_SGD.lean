-- Prove2me | Definitions.Def_AIMInventory_Known_SGD
-- name    : AIMInventory_Known_SGD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:27.170991+00:00
-- url     : https://prove2.me/theorems/9fe86459-fe8e-457c-8b2b-5afe730d307d
-- title:
--   §2.3.1: Euclidean projection P_S, step ϵ_t = γ diam(S)/(B̄√t), and the projected stochastic subgradient iterates of Lemma 3
-- statement:
--   This file fixes the objects of Lemma 3 (§2.3.1, p. 8). Let $S \subseteq \mathbb R^n$. The **projection** $P_S(z)$ is a point of $S$ closest to $z$ in the Euclidean norm; for a nonempty closed convex $S$ it exists and is unique. With $\operatorname{diam}(S) = \sup\{\|u-v\| : u,v \in S\}$, a scale $\gamma > 0$ and a bound $\bar B > 0$, the **step size** is
--   $$\epsilon_t = \frac{\gamma\, \operatorname{diam}(S)}{\bar B \sqrt t}.$$
--   Given a starting point $w_1 \in S$ and random directions $H_1, H_2, \dots$ (the estimate $H(w_t)$ used at step $t$), the **projected stochastic subgradient iterates** are
--   $$w_{t+1} = P_S\big(w_t - \epsilon_t H_t\big), \qquad t \ge 1 .$$
--
--   **Formalization Note** The projection is defined by choice among nearest points, with the fallback $P_S(z) = z$ when no nearest point exists; that case never arises for the sets of Lemma 3. Index $0$ of the iterate sequence is unused and set to $w_1$. $\operatorname{diam}$ is Mathlib's `Metric.diam`, which agrees with the paper's maximum on compact sets.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 8, §2.3.1 and Lemma 3

import Mathlib
open scoped RealInnerProductSpace
noncomputable section

namespace AIMInventory.Known

open Classical in
/-- The Euclidean projection `P_S(z)` onto `S ⊆ ℝⁿ`, p. 8: a point of `S` closest to `z`. For a
nonempty closed convex `S` such a point exists and is unique, so this is the projection; the
fallback value `z` is never used in that case. -/
def projSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  if h : ∃ p ∈ S, ∀ q ∈ S, ‖z - p‖ ≤ ‖z - q‖ then h.choose else z

/-- The step size `ϵ_t = γ diam(S) / (B̄ √t)` of Lemma 3, p. 8. -/
def sgdStep {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (γ Bbar : ℝ) (t : ℕ) : ℝ :=
  γ * Metric.diam S / (Bbar * Real.sqrt t)

/-- The projected stochastic subgradient iterates of Lemma 3, p. 8: `w_1 = w1` and
`w_{t+1} = P_S(w_t − ϵ_t H_t)` for `t ≥ 1`, where `H t : Ω → ℝⁿ` is the random direction
`H(w_t)` used at step `t`. Index `0` is unused and set to `w1`. -/
def sgdIterate {n : ℕ} {Ω : Type*} (S : Set (EuclideanSpace ℝ (Fin n))) (γ Bbar : ℝ)
    (w1 : EuclideanSpace ℝ (Fin n)) (H : ℕ → Ω → EuclideanSpace ℝ (Fin n)) :
    ℕ → Ω → EuclideanSpace ℝ (Fin n)
  | 0 => fun _ => w1
  | 1 => fun _ => w1
  | (t + 2) => fun ω =>
      projSet S (sgdIterate S γ Bbar w1 H (t + 1) ω - sgdStep S γ Bbar (t + 1) • H (t + 1) ω)

end AIMInventory.Known


