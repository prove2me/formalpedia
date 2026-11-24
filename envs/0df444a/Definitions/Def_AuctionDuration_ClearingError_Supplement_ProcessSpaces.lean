-- Prove2me | Definitions.Def_AuctionDuration_ClearingError_Supplement_ProcessSpaces
-- name    : AuctionDuration_ClearingError_Supplement_ProcessSpaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:48:27.783498+00:00
-- url     : https://prove2.me/theorems/a9e38dc5-0db5-460c-a278-d253c1c7a4ce
-- title:
--   Appendix C.1 — adapted H² and S², null equality and masked selector convergence
-- statement:
--   The reference measure on time and paths is Lebesgue measure on $[0,h]$ times $P$. An $H^2$ representative is a jointly square-integrable adapted process. Representatives equal almost everywhere for this product measure represent the same element of $H^2$. Its two-coordinate version is the pair of scalar spaces. Weak convergence is defined by testing against every adapted square-integrable scalar process:
--   $$
--   U_n\rightharpoonup U\quad\Longleftrightarrow\quad
--   E\!\int_0^h U_n(t)Q(t)\,dt\longrightarrow E\!\int_0^h U(t)Q(t)\,dt
--   \quad\text{for every }Q\in H^2.
--   $$
--   The $S^2$ predicate requires a finite expected square path supremum. Marginal processes evaluate forward differences at pre-jump counts; a masked smoothed selector uses the zero set of the limiting marginal. Its weak limit is the similarly masked threshold, not the everywhere positive threshold itself.
--
--   These definitions retain weak convergence and all test processes, rather than substituting a stronger convergence mode or finite test family.
--
--   **Formalization Note** The scalar quotient is supplied explicitly; the two scalar weak limits are equivalent to weak convergence of their pair in $H^2(\mathbb R^2)$. Nonnegative-time Lebesgue measure is the pushforward of restricted real Lebesgue measure. The $S^2$ definition corrects the source's stray differential and bound-variable typo using the square-supremum estimates on p.33. Threshold processes used as controls have predictable representatives, which are also progressively measurable.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, https://arxiv.org/abs/1906.01713v3, p.24, spaces; pp.26,33–35, selector limits

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_StrategicGame

noncomputable section

namespace AuctionDuration.ClearingError.Supplement

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- Lebesgue time times the REFERENCE probability, restricted to [0,h]. -/
def Game.timeProbability (G : Game) : Measure (ℝ≥0 × Sample) :=
  ((Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Ici 0))).restrict
    (Icc (0 : ℝ≥0) (Real.toNNReal G.h))).prod G.P

/-- Adapted, jointly measurable square-integrable scalar processes. -/
def Game.InH2 (G : Game) (U : Process) : Prop :=
  (∀ t : ℝ≥0, (t : ℝ) ≤ G.h →
    StronglyMeasurable[naturalFiltration t] (U t)) ∧
  MemLp (Function.uncurry U) 2 G.timeProbability

/-- H² representatives; null modifications are quotiented below. -/
def Game.H2Rep (G : Game) := {U : Process // G.InH2 U}

def Game.h2Setoid (G : Game) : Setoid G.H2Rep where
  r U V := Function.uncurry U.val =ᵐ[G.timeProbability] Function.uncurry V.val
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl,
    fun h => h.symm, fun h k => h.trans k⟩

/-- The scalar H² space modulo dt×P equality; the vector space is its pair. -/
def Game.H2 (G : Game) := Quotient G.h2Setoid

/-- Weak H² convergence written against every adapted L² test process. The
pairing is invariant under the quotient's dt×P equality. -/
def Game.WeakH2 (G : Game) (U : ℕ → Process) (L : Process) : Prop :=
  G.InH2 L ∧ (∀ n, G.InH2 (U n)) ∧
  ∀ Q : Process, G.InH2 Q →
    Tendsto (fun n => ∫ p, U n p.1 p.2 * Q p.1 p.2 ∂G.timeProbability)
      atTop (𝓝 (∫ p, L p.1 p.2 * Q p.1 p.2 ∂G.timeProbability))

/-- Adapted S² representatives with a genuine, bounded pathwise supremum. -/
def Game.InS2 (G : Game) (U : Process) : Prop :=
  (∀ t : ℝ≥0, (t : ℝ) ≤ G.h →
    StronglyMeasurable[naturalFiltration t] (U t)) ∧
  (∀ᵐ ω ∂G.P, BddAbove {r : ℝ | ∃ t : ℝ≥0, (t : ℝ) ≤ G.h ∧ r = |U t ω| ^ 2}) ∧
  Integrable (fun ω => sSup {r : ℝ | ∃ t : ℝ≥0,
    (t : ℝ) ≤ G.h ∧ r = |U t ω| ^ 2}) G.P

/-- Evaluate a forward difference along the predictable pre-jump state. -/
def Game.marginalProcess (G : Game) (V : ValueField) (i : Fin 2) (x : State) : Process :=
  fun t ω => if (t : ℝ) ≤ G.h then
    D i V t (fun j => x j + preX t ω j) else 0

/-- The zero set belongs to the LIMIT marginal, not its approximation. -/
def Game.maskedSmooth (G : Game) (n : ℕ) (Vn V : ValueField)
    (i : Fin 2) (x : State) : Process :=
  fun t ω => if G.marginalProcess V i x t ω = 0 then
    G.smooth n (G.marginalProcess Vn i x t ω) else 0

/-- Only the masked threshold is a weak limit; the completed threshold itself
is bounded below by the positive lower intensity. -/
def Game.maskedThreshold (G : Game) (θ V : ValueField) (i : Fin 2) (x : State) : Process :=
  fun t ω => if G.marginalProcess V i x t ω = 0 then
    G.liftFeedback θ x t ω else 0

end AuctionDuration.ClearingError.Supplement


