-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_TechnicalSelector
-- name    : StrategicRFx_Benefit_Supplement_TechnicalSelector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:09:45.1872+00:00
-- url     : https://prove2.me/theorems/dce6a998-155a-49b6-82b7-f374637e2f18
-- title:
--   Proof of Theorem 4, ec18–ec20 — response cutoffs and technical selector construction witnesses
-- statement:
--   Leading and pressuring are defined from the buyer's actual negotiation options and their optimal payoffs, before a technical selector is chosen. A pressuring supplier can be negotiated with first in an optimal option that rejects the follower. A leading supplier is accepted immediately at an optimum, or rejecting him first strictly beats either way of negotiating first with the other supplier.
--
--   The alternating construction uses upper and lower quote endpoints, a response curve, and its monotonicity cutoff. Its cuts are represented by greatest-lower-bound relations:
--
--   $$u=\inf\{v\ge0:\ \text{the other supplier is pressuring throughout }[v,a]\}.$$
--
--   Open and closed endpoints are retained in the leading interval and path-boundary selector constraints. A finite construction is an unbounded-length witness type, starting from $(\Pi,\Pi)$; it does not assume that a valid witness exists. A valid deterministic buyer selector must respect the first two source priorities and the specified path boundaries. Existence of the construction, existence of a selector and supplier security remain conclusions of the Theorem 4 target, not standing premises.
--
--   **Formalization Note** Greatest-lower-bound relations avoid default values on empty or unbounded infimum sets. The source's normalized cap 1 is expressed in the original profit units as $\Pi$. Symmetric half-steps use the newly constructed response curve; this records the intended reindexing of the ec18 second-half display from $\pi_{1,k}$ to $\pi_{1,k+1}$. The turning cutoff ranges over the interval on which its curve has just been defined; otherwise the printed implication admits a vacuous value outside that domain. These source-supported readings and the raw-option boundary interpretation are recorded with their source evidence in SOURCE_AUDIT.json. This object supplies construction predicates, not an implemented tendering game or a proved existence result.
--
--   **Continuation correction** The ec20 curve boundary condition is imposed on its full lower-to-upper interval, including the part below the chosen turning point. Terminal half-steps do not evaluate an undefined curve in the supplier security prescription.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), proof of Theorem 4, pp. ec18–ec20 (PDF 49–51)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_OneShot

namespace StrategicRFx.Benefit.Supplement

/-- Quote coordinates in the source order, for either moving supplier. -/
def quoteAt (i : Fin 2) (own opponent : ℝ) : Fin 2 → ℝ :=
  fun k => if k = i then own else opponent

/-- Raw buyer optimum, before priority or technical tie selection. -/
def IsRawResponse (P : Params) (t : Fin 2 → ℝ) (r : Negotiation) : Prop :=
  r.Feasible P t ∧ ∀ s : Negotiation, s.Feasible P t → (s.payoff P t).1 ≤ (r.payoff P t).1

/-- A_i R_j or R_i R_j. At the equality boundary the follower's rejection
has the same payoff as acceptance; the weak inequality retains that raw
option even though the actual buyer selector prefers acceptance. -/
def HasRejectFollowerPattern (P : Params) (t : Fin 2 → ℝ)
    (i : Fin 2) (accept : Bool) (r : Negotiation) : Prop :=
  ∃ x y, r = .bargain i accept x y ∧ followerSplit P (other i) x y ≤ t (other i)

/-- ec18: either A_i R_j or R_i R_j provides maximum buyer profit. -/
def Pressuring (P : Params) (t : Fin 2 → ℝ) (i : Fin 2) : Prop :=
  ∃ a r, HasRejectFollowerPattern P t i a r ∧ IsRawResponse P t r

/-- ec18: immediate acceptance at an optimum, or R_i R_j strictly beats
both A_j R_i and R_j R_i. This is computed from the negotiation programs,
not from an assumed strategic equilibrium or a chosen technical selector. -/
def Leading (P : Params) (t : Fin 2 → ℝ) (i : Fin 2) : Prop :=
  (∃ r, IsPriorityResponse P t r ∧ AcceptedImmediately i r) ∨
  ∃ r, r.Feasible P t ∧ HasRejectFollowerPattern P t i false r ∧
    ∀ a s, s.Feasible P t → HasRejectFollowerPattern P t (other i) a s →
      (s.payoff P t).1 < (r.payoff P t).1

/-- The moving supplier's quote cutoff above which the other supplier is
pressuring throughout the closed interval. All cuts use the source's
nonnegative quote domain. IsGLB avoids any default value on an empty set. -/
def pressureCutSet (P : Params) (i : Fin 2) (ownCap opponent : ℝ) : Set ℝ :=
  {v | 0 ≤ v ∧ ∀ x ∈ Set.Icc v ownCap, Pressuring P (quoteAt i x opponent) (other i)}

/-- Lower endpoint: the mover is leading on the open interval (v,upper). -/
def leadingCutSet (P : Params) (i : Fin 2) (upper opponent : ℝ) : Set ℝ :=
  {v | 0 ≤ v ∧ ∀ x ∈ Set.Ioo v upper, Leading P (quoteAt i x opponent) i}

/-- First argument is restricted to the interval on which the source has
just defined the response curve. The closed interval also rules out an
unintended vacuous implication at v below lower. -/
def turningCutSet (lower upper : ℝ) (curve : ℝ → ℝ) : Set ℝ :=
  {v | v ∈ Set.Icc lower upper ∧ ∀ x y, v ≤ x → x ≤ y → y ≤ upper → curve x ≤ curve y}

/-- One of the two symmetric half-steps on ec18. Unused fields at a terminal
half-step have no mathematical role; no default infimum is evaluated. -/
structure SelectorHalfStep where
  upper : ℝ
  lower : ℝ
  chosen : ℝ
  curve : ℝ → ℝ

def SelectorHalfStep.upperQuotes (s : SelectorHalfStep) (i : Fin 2)
    (t : Fin 2 → ℝ) : Fin 2 → ℝ := quoteAt i s.upper (t (other i))

def SelectorHalfStep.after (s : SelectorHalfStep) (i : Fin 2)
    (t : Fin 2 → ℝ) : Fin 2 → ℝ := quoteAt i s.chosen (t (other i))

/-- The construction in the original profit units. The proof's normalized
cap 1 is Pi here; this performs no division and applies for every positive
Pi supplied by Standing. Existence and finite stopping are not assumptions. -/
def ValidSelectorHalfStep (P : Params) (i : Fin 2) (t : Fin 2 → ℝ)
    (s : SelectorHalfStep) : Prop :=
  (∀ k, 0 ≤ t k) ∧
  IsGLB (pressureCutSet P i (t i) (t (other i))) s.upper ∧
  s.upper ∈ Set.Icc 0 (t i) ∧
  (AcceptsBoth P (s.upperQuotes i t) → s.chosen = s.upper) ∧
  (¬ AcceptsBoth P (s.upperQuotes i t) →
    IsGLB (leadingCutSet P i s.upper (t (other i))) s.lower ∧
    s.lower ∈ Set.Icc 0 s.upper ∧
    (∀ x ∈ Set.Icc s.lower s.upper,
      IsGLB (pressureCutSet P (other i) (t (other i)) x) (s.curve x)) ∧
    IsGLB (turningCutSet s.lower s.upper s.curve) s.chosen ∧
    s.chosen ∈ Set.Icc s.lower s.upper)

/-- Finite construction witnesses. No fixed upper bound on length is built
into this type, and the existence of such a witness is a theorem obligation.
The first mover is supplier 1; all actual protocol orders remain separate. -/
structure SelectorConstruction where
  length : ℕ
  quotes : ℕ → Fin 2 → ℝ
  steps : ℕ → SelectorHalfStep

def selectorMover (k : ℕ) : Fin 2 := if Even k then 0 else 1

def ValidSelectorConstruction (P : Params) (c : SelectorConstruction) : Prop :=
  0 < c.length ∧ c.quotes 0 = (fun _ => P.Pi) ∧
  (∀ k, k < c.length →
    ValidSelectorHalfStep P (selectorMover k) (c.quotes k) (c.steps k) ∧
    c.quotes (k + 1) = (c.steps k).after (selectorMover k) (c.quotes k) ∧
    (AcceptsBoth P ((c.steps k).upperQuotes (selectorMover k) (c.quotes k)) ↔
      k + 1 = c.length))

/-- Canonical accept-both may be implemented with either first supplier.
Otherwise the realized leader is the first supplier of the selected bargain. -/
def ChoosesLeader (i : Fin 2) : Negotiation → Prop
  | .both => True
  | .bargain j _ _ _ => j = i

/-- The ec20 path-boundary restrictions, written for both symmetric half-
steps. Endpoint inclusions match the displayed (a,b] and [a,b] intervals.
This predicate does not assert a selector or construction exists. -/
def RespectsSelectorConstruction (P : Params) (c : SelectorConstruction)
    (β : BuyerSelector) : Prop :=
  RespectsPriorities P β ∧ ∀ k, k < c.length →
    let i := selectorMover k
    let t := c.quotes k
    let s := c.steps k
    (∀ x ∈ Set.Ioc s.upper (t i),
      ChoosesLeader (other i) (β (quoteAt i x (t (other i))))) ∧
    (¬ AcceptsBoth P (s.upperQuotes i t) →
      (∀ x ∈ Set.Icc s.lower s.upper,
        ChoosesLeader (other i) (β (quoteAt i x (s.curve x)))) ∧
      (∀ y ∈ Set.Ioc (s.curve s.chosen) (t (other i)),
        ChoosesLeader i (β (quoteAt i s.chosen y))))

end StrategicRFx.Benefit.Supplement


