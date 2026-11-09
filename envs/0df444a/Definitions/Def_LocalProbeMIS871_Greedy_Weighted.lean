-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Weighted
-- name    : LocalProbeMIS871_Greedy_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:21.074836+00:00
-- url     : https://prove2.me/theorems/401232eb-5c1f-47ec-9fdd-079efed59551
-- title:
--   §3.3.1 — Arbitrary integrable weights and the residual weighted-set sum
-- statement:
--   Fix a root $v$, real ranks $r$, and $0<a<1$. A set $S\subseteq V(H_a)$ containing $v$ is admissible if every vertex of $S\setminus\{v\}$ has a neighbor in $S$ of strictly higher real rank. Let $\psi:(a,1)\to[0,\infty)$ be any Lebesgue integrable function. Define
--
--   $$\omega_\psi(S)=\prod_{u\in S\setminus\{v\}}\psi(r(u)),\qquad Z^a(\psi)=\sum_{\substack{S\subseteq V(H_a),\ v\in S\\\operatorname{Adm}(S,r)}}\omega_\psi(S).$$
--
--   The sum is zero when the root is absent, and the singleton root has weight one. This is the actual residual graph of the actual greedy process.
--
--   The weighted sum permits statements simultaneous over sets selected after the ranks are sampled. No boundedness, continuity, or finite-precision restriction is placed on the weight.
--
--   **Formalization Note** The weight is represented by a real function nonnegative and integrable on the open interval, extended by zero outside it when evaluated. There is no weight evaluation at the root. Arbitrary such interval functions have this representation, and nonroot boundary events are null under the forced-root law.
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 16, PDF p. 18, §3.3.1, definitions preceding Lemma 3.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- §3.3.1: each nonroot vertex has a higher-real-rank neighbor within S. -/
def Adm {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S.erase v, ∃ z ∈ S, G.Adj u z ∧ r u < r z

/-- Arbitrary nonnegative Lebesgue integrable weight on the open interval. -/
def Weight (a : ℝ) (ψ : ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Ioo a 1, 0 ≤ ψ z) ∧ IntegrableOn ψ (Set.Ioo a 1)

/-- Values outside the open interval have no source meaning and are set to zero. -/
def weightValue (a : ℝ) (ψ : ℝ → ℝ) (z : ℝ) : ℝ := if z ∈ Set.Ioo a 1 then ψ z else 0

def omega {n : ℕ} (v : Fin n) (r : Fin n → ℝ) (a : ℝ) (ψ : ℝ → ℝ)
    (S : Finset (Fin n)) : ℝ := ∏ u ∈ S.erase v, weightValue a ψ (r u)

/-- Actual residual weighted-set sum; zero for an absent root, singleton weight one. -/
def Z {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (a : ℝ) (ψ : ℝ → ℝ)
    (r : Fin n → ℝ) : ℝ :=
  ∑ S ∈ (H G r a).powerset.filter (fun S => v ∈ S ∧ Adm G v r S), omega v r a ψ S

end LocalProbeMIS871.Greedy


