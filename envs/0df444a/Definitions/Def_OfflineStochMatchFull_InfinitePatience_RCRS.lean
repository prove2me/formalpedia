-- Prove2me | Definitions.Def_OfflineStochMatchFull_InfinitePatience_RCRS
-- name    : OfflineStochMatchFull_InfinitePatience_RCRS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:47:26.591568+00:00
-- url     : https://prove2.me/theorems/5123bba2-3a65-46cb-94df-62d3965f2b76
-- title:
--   Causal random-order contention resolution and balancedness
-- statement:
--   Let $G=(V,E)$ be a finite loopless undirected graph, and let $\zeta\in[0,1]^E$ satisfy $\sum_{e\in\delta(v)}\zeta_e\le1$ at every vertex. This is the full degree-constraint domain called the matching polytope in Definition 1, without additional odd-set inequalities. Fix an attenuation function $\widetilde a$ and a balance factor $c$.
--
--   Independently draw a uniform edge order, active bits $P_e\sim\operatorname{Bernoulli}(\zeta_e)$ and private attenuation bits $A_e\sim\operatorname{Bernoulli}(\widetilde a(\zeta_e))$. On arrival, reveal the current active bit and apply the immediate acceptance rule
--
--   $$
--   \operatorname{accept}(M,e,P_e,A_e)=1
--   \quad\Longleftrightarrow\quad
--   P_e=A_e=1\ \text{and neither endpoint of }e\text{ is matched in }M.
--   $$
--
--   Accepting inserts the edge; otherwise it is irrevocably discarded. The sequential fold of this rule defines the actual output. Operational causality requires equal observed arrival prefixes and equal revealed bits and coins to give equal accumulated matchings, and identifies each terminal membership decision with the rule at that edge's arrival. Every prefix must be an active matching, and commitments persist.
--
--   The full balanced-RCRS predicate also requires a normalized nonnegative law, a uniform order marginal, the pathwise coupling with Algorithm 1 at $p=\zeta,y=1,t=\infty$, and
--
--   $$
--   \Pr[e\text{ is accepted}]\ge c\zeta_e\quad(e\in E).
--   $$
--
--   This ex ante form includes zero coordinates without conditioning on a null event. The scheme is an explicit online transition rule, rather than an arbitrary matching-valued distribution.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3 (20 April 2026), https://arxiv.org/abs/2106.06892v3, §2, Definitions 1–2 and the probing-to-CRS reduction pp. 7–8; §3.1 Algorithm 1 p. 8.

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Execution

namespace OfflineStochMatchFull.InfinitePatience

open OfflineStochMatch.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The full degree relaxation called the matching polytope in Definition 1,
arXiv:2106.06892v3, p. 7. No odd-set inequalities are added. -/
def DegreeRelaxation (G : EdmondsMatching65.Polyhedron.Graph V E) (ζ : E → ℝ) : Prop :=
  (∀ e, 0 ≤ ζ e ∧ ζ e ≤ 1) ∧ (∀ v, ∑ e ∈ delta G v, ζ e ≤ 1)

open Classical in
/-- Causal acceptance rule at an arrival: current active bit, current private
attenuation coin, and the already committed matching are its only observations. -/
noncomputable def crsAccept (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (e : E) (active attenuation : Bool) : Bool :=
  decide (active = true ∧ attenuation = true ∧
    ∀ f ∈ M, ∀ v, v ∈ G.ends e → v ∉ G.ends f)

/-- Immediate accept-or-discard transition, with no ability to recall a discard. -/
noncomputable def crsStep (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (e : E) (active attenuation : Bool) : Finset E :=
  if crsAccept G M e active attenuation then insert e M else M

/-- Sequential execution of the arrival rule, consuming exactly the first `k`
arrivals, including their current revealed activeness and private coin. -/
noncomputable def crsPrefix (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) (k : ℕ) : Finset E :=
  ((arrivalList σ).take k).foldl (fun M e => crsStep G M e (P e) (A e)) ∅

noncomputable def crsOutput (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) : Finset E :=
  crsPrefix G σ A P (Fintype.card E)

/-- Independent uniform permutation, Bernoulli(`ζ e`) active bits and independent
Bernoulli(`aT (ζ e)`) private attenuation bits. The irrelevant Y family is 1 a.s. -/
noncomputable def crsProb (ζ : E → ℝ) (aT : ℝ → ℝ)
    (ev : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → Prop) : ℝ :=
  prob ζ (fun _ => 1) aT (fun σ _ A P => ev σ A P)

/-- Operational causality, active matching output, and irrevocability. Equality
of observed arrival prefixes and their revealed bits/coins implies equality of
the accumulated matching even if the entire unobserved future is changed. -/
def CRSOperational (G : EdmondsMatching65.Polyhedron.Graph V E) : Prop :=
  (∀ (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) (k : ℕ),
    EdmondsMatching65.Polyhedron.IsMatching G (crsPrefix G σ A P k) ∧
    (∀ e ∈ crsPrefix G σ A P k, P e = true ∧ (σ e).val < k) ∧
    crsPrefix G σ A P k ⊆ crsPrefix G σ A P (k + 1)) ∧
  (∀ (σ σ' : E ≃ Fin (Fintype.card E)) (A P A' P' : E → Bool) (k : ℕ),
    (arrivalList σ).take k = (arrivalList σ').take k →
    (∀ e ∈ (arrivalList σ).take k, A e = A' e ∧ P e = P' e) →
    crsPrefix G σ A P k = crsPrefix G σ' A' P' k) ∧
  (∀ (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) (e : E),
    (e ∈ crsOutput G σ A P ↔
      crsAccept G (crsPrefix G σ A P (σ e).val) e (P e) (A e) = true))

/-- Full c-balanced random-order CRS, including its causal rule, normalized law,
uniform order, ex ante guarantee at zero as well as positive coordinates, and
pathwise coupling with the actual Algorithm 1 (p=ζ, y=1, t=∞). -/
def BalancedRCRS (G : EdmondsMatching65.Polyhedron.Graph V E) (ζ : E → ℝ)
    (aT : ℝ → ℝ) (c : ℝ) : Prop :=
  CRSOperational G ∧ crsProb ζ aT (fun _ _ _ => True) = 1 ∧
  (∀ ev, 0 ≤ crsProb ζ aT ev) ∧
  (∀ σ₀ : E ≃ Fin (Fintype.card E),
    crsProb ζ aT (fun σ _ _ => σ = σ₀) = 1 / ((Fintype.card E).factorial : ℝ)) ∧
  (∀ e, c * ζ e ≤ crsProb ζ aT (fun σ A P => e ∈ crsOutput G σ A P)) ∧
  (∀ (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool),
    crsOutput G σ A P = terminalMatching G (fun _ => ⊤) σ (fun _ => true) A P)

end OfflineStochMatchFull.InfinitePatience


