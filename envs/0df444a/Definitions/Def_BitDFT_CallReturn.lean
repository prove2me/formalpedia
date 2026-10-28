-- Prove2me | Definitions.Def_BitDFT_CallReturn
-- name    : BitDFT_CallReturn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T22:41:19.431055+00:00
-- url     : https://prove2.me/theorems/17e88460-08c5-4843-b3ff-fbc7b87d4cc8
-- title:
--   A finite controller for repeated machine calls
-- statement:
--   A finite controller can run a designated machine from a designated state of a caller controller, then return to a designated caller state when the called machine halts. Both dispatches preserve the complete tape frame.
-- source:
--   Explicit finite-state sum construction over two existing multitape machine controllers. The accompanying call-return theorem charges both dispatch transitions.

import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false
noncomputable section

namespace BitDFT.CallReturn
open IntMul BitDFT.MachineSequence

/-- A controller which can call `Q` from one designated state of `P`, then
    return to a designated state of `P` when `Q` halts. The call and return
    transitions are stationary, so the complete tape frame passes unchanged. -/
noncomputable def controller {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit) : Controller M := by
  classical
  exact {
    K := P.K ⊕ Q.K
    entry := .inl P.entry
    exit := .inl P.exit
    distinct := by
      intro h
      exact P.distinct (Sum.inl.inj h)
    transition := fun q a => match q with
      | .inl p =>
          if hp : p = P.exit then
            (.inl P.exit, fun i => (a i, .stay))
          else if hc : p = call then
            (.inr Q.entry, fun i => (a i, .stay))
          else
            let r := P.transition p a
            (.inl r.1, r.2)
      | .inr q =>
          if hq : q = Q.exit then
            (.inl resume, fun i => (a i, .stay))
          else
            let r := Q.transition q a
            (.inr r.1, r.2)
    marker := by
      intro q a i hi
      cases q with
      | inl p =>
          by_cases hp : p = P.exit
          · simp [hp, hi]
          · by_cases hc : p = call
            · subst p
              simp [hp, hi]
            · simpa [hp, hc] using P.marker p a i hi
      | inr q =>
          by_cases hq : q = Q.exit
          · simp [hq, hi]
          · simpa [hq] using Q.marker q a i hi
    noMarker := by
      intro q a i hi
      cases q with
      | inl p =>
          by_cases hp : p = P.exit
          · simp [hp, hi]
          · by_cases hc : p = call
            · subst p
              simp [hp, hi]
            · simpa [hp, hc] using P.noMarker p a i hi
      | inr q =>
          by_cases hq : q = Q.exit
          · simp [hq, hi]
          · simpa [hq] using Q.noMarker q a i hi
    frozen := by
      intro a
      simp [P.frozen]
    readonly := by
      intro q a
      cases q with
      | inl p =>
          by_cases hp : p = P.exit
          · simp [hp]
          · by_cases hc : p = call
            · subst p
              simp [hp]
            · simpa [hp, hc] using P.readonly p a
      | inr q =>
          by_cases hq : q = Q.exit
          · simp [hq]
          · simpa [hq] using Q.readonly q a
  }

abbrev machine {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (hcall : call ≠ P.exit) :=
  (controller P Q call resume hcall).machine

def fromP {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (hcall : call ≠ P.exit) (c : P.machine.Cfg) : (machine P Q call resume hcall).Cfg :=
  ⟨Sum.inl c.state, c.cells, c.head⟩

def fromQ {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (hcall : call ≠ P.exit) (c : Q.machine.Cfg) : (machine P Q call resume hcall).Cfg :=
  ⟨Sum.inr c.state, c.cells, c.head⟩

def enterQ {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (c : P.machine.Cfg) : Q.machine.Cfg :=
  ⟨Q.entry, c.cells, c.head⟩

def returnP {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (c : Q.machine.Cfg) : P.machine.Cfg :=
  ⟨resume, c.cells, c.head⟩


end BitDFT.CallReturn


