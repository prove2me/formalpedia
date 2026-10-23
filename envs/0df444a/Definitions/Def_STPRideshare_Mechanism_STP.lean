-- Prove2me | Definitions.Def_STPRideshare_Mechanism_STP
-- name    : STPRideshare_Mechanism_STP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:27.846281+00:00
-- url     : https://prove2.me/theorems/018a7986-f604-40dc-9328-dead7017a08c
-- title:
--   Definition 12, p. 21 — the spatio-temporal pricing (STP) mechanism, for a selector of welfare-optimal dispatchings, and the replica gains Φ^(t')_{a,t}(s_{t'}) of (56)
-- statement:
--   **The STP mechanism** (Definition 12). Fix a *selector*: a rule that picks a dispatching of every economy; it is *optimal* when it picks a welfare-optimal (integral) dispatching of every valid economy. The STP mechanism plans at time $0$ on the economy itself, and re-plans on $E^{(t)}(s_t)$ immediately after any time $t-1$ at which some driver did not take her dispatched action. At each planning step:
--
--   1. **Dispatch rule.** Every available driver is dispatched along her action path in the selected dispatching of the current economy: the relocation or rider trip of that path starting now, or exit / not enter if her path has no trip starting now.
--   2. **Payment rules.** With $\Phi_{a,t}=W(\mathcal D\cup\{(1,a,t)\})-W(\mathcal D)$ computed for the current economy, the anonymous trip prices are
--   $$p_{a,b,t}=\Phi_{a,t}-\Phi_{b,t+\delta(a,b)}+c_{a,b,t}\qquad(28),$$
--   fixed until the next re-planning. A driver dispatched to pick up rider $j$ is paid $p_{o_j,d_j,\tau_j}$ (and nothing for any other action); rider $j$ is charged $p_{o_j,d_j,\tau_j}$ times the number of drivers dispatched to pick her up, and pays only if picked up.
--
--   **Replica gains in shifted economies** (56). For a time $t'$, a state profile $s$ and a node $(a,t)$ with $t\ge t'$,
--   $$\Phi^{(t')}_{a,t}(s)=W\big(\mathcal D^{(t')}(s)\cup\{(1,a,t-t')\}\big)-W\big(\mathcal D^{(t')}(s)\big),$$
--   the welfare gain from an additional driver at $(a,t)$ in the time-shifted economy $E^{(t')}(s)$.
--
--   **Formalization Note.** The page says "compute an optimal solution $(x,y)$ to the LP (9)"; which optimum is computed is left open, so the mechanism is a family indexed by the selector, and the mission's statements quantify over every optimal selector. Times inside the selected plan are shifted by the re-planning time $t_0$; the prices of the plan are those of the economy $E^{(t_0)}(s_{t_0})$ (of the original economy when $t_0=0$).
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Definition 12, (28); p. 53, (56)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Game

namespace STPRideshare.Mechanism

open scoped Classical

noncomputable section

/-- A selector: for every economy, a dispatching (the "optimal solution `(x, y)` to the LP (9)"
that Definition 12, p. 21, computes). -/
def Selector (L : Type) : Type 1 :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ], (e : Econ L ι κ) → Dispatch e

/-- The selector picks a welfare-optimal (integral) dispatching of every valid economy. -/
def IsOptimalSelector {L : Type} (sel : Selector L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid → (sel e).IsWelfareOptimal

variable {L ι κ ι' κ' : Type}

/-- The action that the dispatching `d` (of an economy with drivers `ι'`, riders `κ'`) prescribes
for driver `i′` at its time `u`: the relocation or rider trip of `z̃_{i′}` starting at `u`
(riders mapped into `κ` by `emb`), or `φ` if `z̃_{i′}` has no trip starting at `u`. -/
def planAction {e' : Econ L ι' κ'} (d : Dispatch e') (i' : ι') (u : ℕ) (emb : κ' → κ) :
    DAction L κ :=
  match (d.z i').find? (fun st => decide (st.1.2.2 = u)) with
  | some ((_, b, _), none) => .move b
  | some (_, some j) => .pick (emb j)
  | none => .quit

variable [Fintype ι] [Fintype κ]

/-- Definition 12, p. 21, dispatch rule, given that the current plan was computed at time `t₀`:
an available driver follows the trip of the plan `sel(E^{(t₀)}(s_{t₀}))` (for `t₀ = 0`, `sel(e)`)
that starts at time `t` (shifted time `t − t₀`), and exits / does not enter if her planned path has
no trip at `t`; every other driver continues. -/
def stpDispatchVia (sel : Selector L) (e : Econ L ι κ) (t0 : ℕ) (h : Hist L ι κ) (i : ι) :
    DAction L κ :=
  if IsAvailAt h.length (stateAt e h i) then
    if t0 = 0 then planAction (sel e) i h.length id
    else if hi : stateAt e (h.drop (h.length - t0)) i ≠ .gone then
      planAction (sel (shiftEcon e (h.drop (h.length - t0)))) ⟨i, hi⟩ (h.length - t0) Subtype.val
    else .quit
  else .cont

/-- Definition 12, p. 21: the time `t₀` at which the STP mechanism last planned: `0`, or the
latest `t` such that some driver deviated from the dispatch at `t − 1` ("immediately after a
deviation by one or more drivers"). -/
def replanTime (sel : Selector L) (e : Econ L ι κ) : Hist L ι κ → ℕ
  | [] => 0
  | α :: h =>
      if ∃ i, α i ≠ stpDispatchVia sel e (replanTime sel e h) h i then h.length + 1
      else replanTime sel e h

/-- Definition 12, (28), p. 21: the STP price of the trip `(a, b, u)` (original time `u`) under
the current plan: the prices (28) of `E^{(t₀)}(s_{t₀})` at shifted time `u − t₀`, computed when
the plan was made (for `t₀ = 0`, the prices (28) of `e`). -/
def stpPriceVia (sel : Selector L) (e : Econ L ι κ) (h : Hist L ι κ) (tr : Trip L) : ℝ :=
  if replanTime sel e h = 0 then e.stpPrice tr
  else (shiftEcon e (h.drop (h.length - replanTime sel e h))).stpPrice
    (tr.1, tr.2.1, tr.2.2 - replanTime sel e h)

/-- Definition 12, p. 21: the spatio-temporal pricing mechanism with selector `sel`. It plans at
time 0 and re-plans on `E^{(t)}(s_t)` immediately after any deviation; it dispatches every
available driver along the selected dispatching; it pays a driver the trip price (28) of the rider
trip she is dispatched to (`r*`), and charges rider `j` the price of her trip times the number of
drivers dispatched to pick her up (`q*`). -/
def stp (sel : Selector L) : DynMech L where
  disp := fun e h i => stpDispatchVia sel e (replanTime sel e h) h i
  pay := fun e h i =>
    match stpDispatchVia sel e (replanTime sel e h) h i with
    | .pick j => stpPriceVia sel e h (riderTrip (e.R j))
    | _ => 0
  charge := fun e h j =>
    stpPriceVia sel e h (riderTrip (e.R j)) *
      ((Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e h) h i = .pick j).card : ℝ)

/-- (56), p. 53: `Φ^{(t′)}_{a,t}(s) = W(D^{(t′)}(s) ∪ {(1, a, t − t′)}) − W(D^{(t′)}(s))`, the
welfare gain from an additional driver at `(a, t)` in the time-shifted economy `E^{(t′)}(s)`. -/
def PhiShift (e : Econ L ι κ) (t' : ℕ) (s : ι → DState L κ) (a : L) (t : ℕ) : ℝ :=
  PhiAt (econAt e t' s) a (t - t')

end

end STPRideshare.Mechanism


