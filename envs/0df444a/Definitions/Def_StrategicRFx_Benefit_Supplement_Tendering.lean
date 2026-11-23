-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_Tendering
-- name    : StrategicRFx_Benefit_Supplement_Tendering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:10:50.922806+00:00
-- url     : https://prove2.me/theorems/5ef17907-627e-4876-aac1-afb921a67310
-- title:
--   §3.2.1 and proof of Theorem 4 — public quote histories, strategies and tendering outcomes
-- statement:
--   Two suppliers first quote independently in the full nonnegative real domain. A public history records the initial quotes and every revealed request and response. At each request either one supplier or both suppliers simultaneously may revise their quotes. Iterative rules permit only reductions or unchanged quotes; general tendering rules also permit upward revisions. A quote change by one supplier clears the other supplier's answer; the process is settled when each supplier has answered a request given the opponent's current quote. As in Figure 4, an alternating procedure therefore ends when the requested supplier keeps his quote after the other has lowered. Arbitrary history-dependent request schedules are admitted, subject to each supplier eventually receiving response opportunities along any continuing play. General procedures may end earlier, including one-shot solicitation. Iterative procedures satisfy
--
--   $$\text{stop at }h\ \Longleftrightarrow\ \text{neither supplier lowers given the current opposing quote information}.$$
--
--   A pure strategy contains an independent initial quote and a response at every public history. Unilateral deviations replace the entire strategy and are compared by the realized final negotiation profits, first the supplier's own profit, then the buyer's profit, and then the buyer's accept-both/early-acceptance priority when both profits tie. An equilibrium target requires pure Nash optimality initially and at all reachable public histories. Final quotations are computed from the first stopping event, rather than identified with an arbitrary accept-both point. No finite horizon, uniform stopping bound, equilibrium existence, security guarantee or unique Nash-program maximizer is assumed.
--
--   The source's finite technical-selector construction is independent of the actual tendering game. The security response prescription retains its constant strips, curve segments and final accept-both boundary. Both supplier orders and simultaneous requests are represented.
--
--   **Formalization Note** All quotes are nonnegative reals. A nonterminating play is explicitly represented by an absent final quotation; negotiation never begins, and its no-transaction profits are set to zero using p. 7 normalization. This is a disclosed boundary reading, not a limiting quotation or an automatic infimum value. Page 7 explicitly requires off-path outcomes to be subgame perfect, supporting sequential rationality at every public history. The paper assigns no separate outcome to an endless solicitation; zero no-transaction profit is the reading, recorded in MODERATION_NOTES.md.
--
--   **Source notation repair** The accept-both boundary uses both inequalities in Lemma 2 (p. 18): $\tau_i(z)=\min\{\theta_i(\Pi-z-\Pi^{-i})^+, (\Pi-\Pi^{-j}-z/\theta_j)^+\}$, where $j$ is the other supplier. The ec17 display repeats index $i$ in the second bound and reverses the region inequalities. The Lean already uses the Lemma 2 boundary; this correction excludes no source parameter or quotation.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), pp. 14–16, ec17–ec21; no-transaction normalization p. 7

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_PreferenceGame
import Definitions.Def_StrategicRFx_Benefit_Supplement_Primitives
import Definitions.Def_StrategicRFx_Benefit_Supplement_TechnicalSelector

namespace StrategicRFx.Benefit.Supplement

abbrev Quotation := Fin 2 → NNReal

/-- A request is made to either supplier or to both simultaneously. -/
inductive Request where
  | one (supplier : Fin 2)
  | both
  deriving DecidableEq

def Request.includes : Request → Fin 2 → Prop
  | .one i, j => i = j
  | .both, _ => True

/-- A publicly revealed quotation profile, and for each supplier whether he
has already answered a request given the opponent's current quotation (by
keeping or revising his own). A change of the opponent's quotation clears it. -/
structure TenderState where
  quote : Quotation
  answered : Fin 2 → Bool

/-- Events are stored most recent first; there is no finite horizon. -/
structure TenderHistory where
  initial : Quotation
  past : List (Request × TenderState)

def TenderHistory.state (h : TenderHistory) : TenderState :=
  match h.past with
  | [] => ⟨h.initial, fun _ => false⟩
  | (_, s) :: _ => s

/-- p. 14: no supplier changes his price given the opponent's offer
information. In Figure 4 the play ends when the requested supplier refuses,
the other having made his latest offer against the current quotation. Any
change clears the opponent's flag, so a settled history ends with no change. -/
def TenderHistory.settled (h : TenderHistory) : Prop :=
  ∀ i, h.state.answered i = true

/-- Both ordinary finite solicitation rules and unlimited iterative rules use
this interface. Supplier strategies, not the procedure, set the quotations.
All new offers are revealed before the next request. General rules may allow
upward revisions; iterative rules enforce reductions only. -/
structure TenderProcedure where
  request : TenderHistory → Request
  stop : TenderHistory → Bool
  reductionsOnly : Bool

structure TenderStrategy where
  initial : NNReal
  response : TenderHistory → NNReal

abbrev TenderProfile := Fin 2 → TenderStrategy

/-- Iterative requests permit lower or unchanged quotes. General procedures
also allow unrestricted revised quotes, retaining the full domain in Theorem 6.
The minimum parametrizes the full iterative feasible interval, not a grid. -/
noncomputable def nextQuotation (p : TenderProcedure) (s : TenderProfile)
    (h : TenderHistory) : Quotation := by
  classical
  exact fun i => if (p.request h).includes i then
    if p.reductionsOnly then min (h.state.quote i) ((s i).response h) else (s i).response h
    else h.state.quote i

noncomputable def advanceTender (p : TenderProcedure) (s : TenderProfile)
    (h : TenderHistory) : TenderHistory := by
  classical
  let t := nextQuotation p s h
  let r : Fin 2 → Bool := fun i =>
    if t (other i) ≠ h.state.quote (other i) then false
    else if (p.request h).includes i then true else h.state.answered i
  exact ⟨h.initial, (p.request h, ⟨t, r⟩) :: h.past⟩

/-- Each finite prefix is defined even for a play that never stops. A stopped
history is absorbing. No limit quotation or default infimum is evaluated. -/
noncomputable def tenderRunFrom (p : TenderProcedure) (s : TenderProfile)
    (h : TenderHistory) : ℕ → TenderHistory
  | 0 => h
  | n + 1 => let h' := tenderRunFrom p s h n
      if p.stop h' then h' else advanceTender p s h'

def initialHistory (s : TenderProfile) : TenderHistory :=
  ⟨fun i => (s i).initial, []⟩

def TerminatesFrom (p : TenderProcedure) (s : TenderProfile) (h : TenderHistory) : Prop :=
  ∃ n, p.stop (tenderRunFrom p s h n) = true

/-- A terminal quote is present exactly at the first stopping event. `none`
means that negotiation has never begun, not negotiation at a limiting quote. -/
noncomputable def finalQuotationFrom (p : TenderProcedure) (s : TenderProfile)
    (h : TenderHistory) : Option Quotation := by
  classical
  exact if H : TerminatesFrom p s h then
    some (tenderRunFrom p s h (Nat.find H)).state.quote else none

noncomputable def finalQuotation (p : TenderProcedure) (s : TenderProfile) : Option Quotation :=
  finalQuotationFrom p s (initialHistory s)

def ReachableHistory (p : TenderProcedure) (h : TenderHistory) : Prop :=
  ∃ s n, tenderRunFrom p s (initialHistory s) n = h

/-- The procedural opportunity condition in ec21: no supplier can be denied
responses forever along a continuing legal play. This is fairness of requests,
not a bound on the number of responses or on equilibrium stopping time. -/
def FairRequests (p : TenderProcedure) : Prop :=
  ∀ h s, ReachableHistory p h → ¬ TerminatesFrom p s h →
    ∀ i N, ∃ n, N ≤ n ∧ (p.request (tenderRunFrom p s h n)).includes i

/-- General source tendering rules must allow both initial quotes and end
when both suppliers decline to lower. They may also stop earlier (one-shot
or a finite number of rounds). Iterative rules stop exactly at settled histories
(p. 14: the procedure ends if and only if no supplier lowers his price given
the opponent's offer information). -/
def ValidTenderProcedure (p : TenderProcedure) : Prop :=
  FairRequests p ∧ ∀ h, ReachableHistory p h → h.settled → p.stop h = true

def IterativeTenderProcedure (p : TenderProcedure) : Prop :=
  p.reductionsOnly = true ∧ FairRequests p ∧
    ∀ h, ReachableHistory p h → (p.stop h = true ↔ h.settled)

/-- This realizes the exact one-shot simultaneous protocol: the two independent
initial offers are sent to negotiation without any response request. -/
def oneShotProcedure : TenderProcedure := ⟨fun _ => .both, fun _ => true, false⟩

noncomputable def alternatingProcedure (first : Fin 2) : TenderProcedure := by
  classical
  exact ⟨fun h => .one (if Even h.past.length then first else other first),
    fun h => decide h.settled, true⟩

noncomputable def simultaneousProcedure : TenderProcedure := by
  classical
  exact ⟨fun _ => .both, fun h => decide h.settled, true⟩

def realQuotation (t : Quotation) : Fin 2 → ℝ := fun i => (t i : ℝ)

/-- No transactions occur during solicitation. On an endless play no
negotiation or procurement occurs: all profits are zero by the no-transaction
normalization on p. 7 (the paper gives no other outcome for endless play);
it is not a limit-continuation convention. -/
def quotationPayoff (P : Params) (β : BuyerSelector) : Option Quotation → Payoff
  | none => ⟨0, fun _ => 0⟩
  | some t => ⟨((β (realQuotation t)).payoff P (realQuotation t)).1,
      ((β (realQuotation t)).payoff P (realQuotation t)).2⟩

/-- The buyer's secondary acceptance hierarchy at equal profit. No final
quote has no accepted offer. This is explicit even at zero supplier profit. -/
noncomputable def quotationPriority (P : Params) (β : BuyerSelector) : Option Quotation → ℕ
  | none => 0
  | some t => (β (realQuotation t)).priority P (realQuotation t)

/-- Lexicographic own profit, buyer profit, then buyer acceptance priority.
The final tier matters for a zero-profit supplier: equal buyer profits do
not make an accepted quote indifferent to a rejected one. -/
def SupplierPrefers (P : Params) (β : BuyerSelector) (i : Fin 2)
    (new old : Option Quotation) : Prop :=
  let v := quotationPayoff P β new
  let w := quotationPayoff P β old
  w.supplier i < v.supplier i ∨
    (v.supplier i = w.supplier i ∧
      (w.buyer < v.buyer ∨ (v.buyer = w.buyer ∧
        quotationPriority P β old < quotationPriority P β new)))

noncomputable def tenderGame (P : Params) (β : BuyerSelector) (p : TenderProcedure) :
    PreferenceGame (Fin 2) (fun _ => TenderStrategy) (Option Quotation) :=
  ⟨finalQuotation p, SupplierPrefers P β⟩

noncomputable def continuationGame (P : Params) (β : BuyerSelector)
    (p : TenderProcedure) (h : TenderHistory) :
    PreferenceGame (Fin 2) (fun _ => TenderStrategy) (Option Quotation) :=
  ⟨fun s => finalQuotationFrom p s h, SupplierPrefers P β⟩

/-- Complete contingent strategies compare final profits after all future
responses. Sequential rationality is required at every public history,
including the intermediate history between two alternating requests. The
predicate contains no coordination, accept-both or security condition. -/
def IsTenderEquilibrium (P : Params) (β : BuyerSelector)
    (p : TenderProcedure) (s : TenderProfile) : Prop :=
  (tenderGame P β p).IsNash s ∧
  ∀ h, ReachableHistory p h → (continuationGame P β p h).IsNash s

/-- A source technical selector has an actual finite cutoff construction;
neither its existence nor the game equilibrium is assumed in this definition. -/
def SourceBuyerSelector (P : Params) (β : BuyerSelector) : Prop :=
  ∃ c, ValidSelectorConstruction P c ∧ RespectsSelectorConstruction P c β

/-- Boundary τ_i of the accept-both region, in original profit units.
Use the two inequalities of Lemma 2 (p. 18): the second bound uses the OTHER
supplier's exclusive surplus and bargaining power. The ec17 display repeats
index i in that bound and reverses the region inequalities. This is a notation
repair, not a restriction on the quotation or parameter domain. -/
noncomputable def acceptanceBoundary (P : Params) (i : Fin 2) (opponent : ℝ) : ℝ :=
  min (P.θ i * max (P.Pi - opponent - P.PiEx i) 0)
    (max (P.Pi - P.PiEx (other i) - opponent / P.θ (other i)) 0)

/-- The ec20–ec21 supplier response prescription: the constant strips,
curve segments and final acceptance boundary are all obligations on ρ.
Quotes above Pi have the same continuation as Pi, as on ec17. -/
def SecurityResponse (P : Params) (c : SelectorConstruction)
    (ρ : Fin 2 → ℝ → ℝ) : Prop :=
  (∀ i z, P.Pi < z → ρ i z = ρ i P.Pi) ∧
  (∀ i z, 0 ≤ z → z ≤ c.quotes c.length (other i) →
    ρ i z = acceptanceBoundary P i z) ∧
  ∀ k, k < c.length →
    let i := selectorMover k
    let t := c.quotes k
    let a := c.steps k
    ¬ AcceptsBoth P (a.upperQuotes i t) →
      (∀ z ∈ Set.Ioc (a.curve a.chosen) (t (other i)), ρ i z = a.chosen) ∧
      (∀ z ∈ Set.Icc a.lower a.upper, ρ (other i) z = a.curve z)

end StrategicRFx.Benefit.Supplement


