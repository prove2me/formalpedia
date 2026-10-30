-- Prove2me | Definitions.Def_OfflineStochMatchFull_InfinitePatience_Execution
-- name    : OfflineStochMatchFull_InfinitePatience_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:46:15.526994+00:00
-- url     : https://prove2.me/theorems/ed517ca7-3d9e-4f8b-a9d9-d3ef0277c56e
-- title:
--   Actual Algorithm 1 matching output and online decisions
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph, $p,y\in[0,1]^E$, $t\in(\mathbb N\cup\{\infty\})^V$, $w\in\mathbb R_{\ge0}^E$, and $\widetilde a$ an attenuation function. Reuse Algorithm 1's actual sequential state transitions. Its law draws an independent uniform permutation $\sigma$ and independent bits $Y_e\sim\operatorname{Bernoulli}(y_e)$, $A_e\sim\operatorname{Bernoulli}(\widetilde a(p_ey_e))$, and $P_e\sim\operatorname{Bernoulli}(p_e)$.
--
--   For the first $k$ arrivals, define the actual committed edges and expected terminal reward by
--
--   $$
--   M_k=\{e:\sigma(e)<k,\ e\text{ is probed by Algorithm 1},\ P_e=1\},\qquad
--   \operatorname{ALG}(y)=\sum_{e\in E}w_e\Pr[e\in M_{|E|}].
--   $$
--
--   The observable history before an arrival retains only earlier probes and their revealed active bits. Operational correctness requires each probing decision to equal the legal history-based rule with its current $Y_e,A_e$ bits; every prefix must be an active matching and earlier commitments must persist. Equal observable histories and equal current private bits must give equal probing decisions, even when order and hidden bits differ elsewhere.
--
--   The probability-law predicate requires normalization, nonnegativity, and probability $1/|E|!$ for each order. Coin and order independence are fixed by the reused product-weight probability definition. This output and reward layer connects the per-edge analysis to actual weighted matchings; it does not define reward from an LP bound.
--
--   **Formalization Note** Positions start at zero, so the unique empty permutation has weight $1/0!=1$. Finite sums cover all real probability inputs, including zero.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3 (20 April 2026), https://arxiv.org/abs/2106.06892v3, §3.1 Algorithm 1 p. 8; §3.2 Equation (4) p. 9; Definition 2 p. 8.

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Policies

namespace OfflineStochMatchFull.InfinitePatience

open OfflineStochMatch.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The ordered edge list supplied by a permutation, including the empty one. -/
def arrivalList (σ : E ≃ Fin (Fintype.card E)) : List E :=
  (List.finRange (Fintype.card E)).map σ.symm

open Classical in
/-- Actual matched edges among the first `k` arrivals of published Algorithm 1.
An edge enters exactly when the actual sequential run probes it and it is active.
Brubach et al., arXiv:2106.06892v3, Algorithm 1 p. 8, Equation (4) p. 9. -/
noncomputable def matchedPrefix (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (k : ℕ) : Finset E :=
  Finset.univ.filter fun e => (σ e).val < k ∧ IsProbed G t σ Y A P e ∧ P e = true

/-- Terminal matching from the actual Algorithm 1 run, not an LP expression. -/
noncomputable def terminalMatching (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) : Finset E :=
  matchedPrefix G t σ Y A P (Fintype.card E)

/-- Expected actual matched weight, as the sum of edge weights times their
inclusion probabilities under the published independent uniform-order law. -/
noncomputable def algorithmReward (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p : E → ℝ) (t : V → ℕ∞) (y w : E → ℝ) (aT : ℝ → ℝ) : ℝ :=
  ∑ e, w e * prob p y aT (fun σ Y A P => e ∈ terminalMatching G t σ Y A P)

open Classical in
/-- Only observations made by earlier probes are available before `e`.
The actual run's transition reads `P f` only when `f` is probed. -/
noncomputable def observedBefore (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) : ProbeHistory E :=
  ((arrivalList σ).take (σ e).val).filterMap fun f =>
    if IsProbed G t σ Y A P f then some (f, P f) else none

/-- Explicit online/irrevocable content of Algorithm 1: each probing decision is
the legal local rule on observed history and current private bits; every prefix
is an active matching, and accepted edges are never removed. No output law is
supplied as data. -/
def AlgorithmOperational (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) : Prop :=
  (∀ (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E),
    LegalHistory G t (observedBefore G t σ Y A P e) ∧
      (IsProbed G t σ Y A P e ↔
        LegalNext G t (observedBefore G t σ Y A P e) e ∧ Y e = true ∧ A e = true)) ∧
  (∀ (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (k : ℕ),
    EdmondsMatching65.Polyhedron.IsMatching G (matchedPrefix G t σ Y A P k) ∧
      (∀ e ∈ matchedPrefix G t σ Y A P k, P e = true) ∧
      matchedPrefix G t σ Y A P k ⊆ matchedPrefix G t σ Y A P (k + 1)) ∧
  (∀ (σ σ' : E ≃ Fin (Fintype.card E)) (Y A P Y' A' P' : E → Bool) (e : E),
    observedBefore G t σ Y A P e = observedBefore G t σ' Y' A' P' e →
    Y e = Y' e → A e = A' e →
    (IsProbed G t σ Y A P e ↔ IsProbed G t σ' Y' A' P' e))

/-- The normalized Algorithm 1 law and its independent uniform order marginal.
Independence from all coin families is explicit in the product weights of `prob`. -/
def AlgorithmProbabilityLaw (p y : E → ℝ) (aT : ℝ → ℝ) : Prop :=
  prob p y aT (fun _ _ _ _ => True) = 1 ∧
  (∀ ev, 0 ≤ prob p y aT ev) ∧
  (∀ σ₀ : E ≃ Fin (Fintype.card E),
    prob p y aT (fun σ _ _ _ => σ = σ₀) = 1 / ((Fintype.card E).factorial : ℝ))

end OfflineStochMatchFull.InfinitePatience


