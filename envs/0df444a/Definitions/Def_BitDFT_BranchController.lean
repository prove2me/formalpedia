-- Prove2me | Definitions.Def_BitDFT_BranchController
-- name    : BitDFT_BranchController
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T21:57:37.868036+00:00
-- url     : https://prove2.me/theorems/a34191bc-172e-48d9-ace0-a5be902af266
-- title:
--   A finite controller that selects and joins two machines
-- statement:
--   Given two finite controllers over the same multitape machine and a Boolean test of one scanned symbol, this controller tests once, runs the selected controller, and maps either selected exit to one common exit. The branch selection and exit join leave every tape cell and head unchanged. This definition provides the control-flow component needed to combine the low-magnitude and boundary cases in the Fourier output rescaling machine.
-- source:
--   Finite-state composition derived from the IntMul.MultitapeTM semantics and the existing BitDFT machine-sequence controller definitions.

import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false

namespace BitDFT.MachineSequence
open IntMul

abbrev BranchState {M : MultitapeTM} (P Q : Controller M) :=
  Unit ⊕ (P.K ⊕ (Q.K ⊕ Unit))

noncomputable def branchController {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) : Controller M := by
  classical
  let done : BranchState P Q := Sum.inr (Sum.inr (Sum.inr ()))
  exact {
    K := BranchState P Q
    entry := Sum.inl ()
    exit := done
    distinct := by simp [done]
    transition := fun s a =>
      match s with
      | .inl _ =>
          if test (a source) then
            (Sum.inr (Sum.inl P.entry), fun i => (a i, .stay))
          else
            (Sum.inr (Sum.inr (Sum.inl Q.entry)), fun i => (a i, .stay))
      | .inr (.inl p) =>
          if p = P.exit then (done, fun i => (a i, .stay))
          else let r := P.transition p a; (Sum.inr (Sum.inl r.1), r.2)
      | .inr (.inr (.inl q)) =>
          if q = Q.exit then (done, fun i => (a i, .stay))
          else let r := Q.transition q a; (Sum.inr (Sum.inr (Sum.inl r.1)), r.2)
      | .inr (.inr (.inr _)) => (done, fun i => (a i, .stay))
    marker := by
      intro s a i hi
      cases s with
      | inl u =>
          by_cases hb : test (a source) = true <;> simp [done, hi, hb]
      | inr s =>
        cases s with
        | inl p =>
          by_cases hp : p = P.exit
          · simp [done, hp, hi]
          · simpa [done, hp] using P.marker p a i hi
        | inr s =>
          cases s with
          | inl q =>
            by_cases hq : q = Q.exit
            · simp [done, hq, hi]
            · simpa [done, hq] using Q.marker q a i hi
          | inr u => simp [done, hi]
    noMarker := by
      intro s a i hi
      cases s with
      | inl u =>
          by_cases hb : test (a source) = true <;> simp [done, hi, hb]
      | inr s =>
        cases s with
        | inl p =>
          by_cases hp : p = P.exit
          · simpa [done, hp] using hi
          · simpa [done, hp] using P.noMarker p a i hi
        | inr s =>
          cases s with
          | inl q =>
            by_cases hq : q = Q.exit
            · simpa [done, hq] using hi
            · simpa [done, hq] using Q.noMarker q a i hi
          | inr u => simpa [done] using hi
    frozen := by
      intro a
      rfl
    readonly := by
      intro s a
      cases s with
      | inl u =>
          by_cases hb : test (a source) = true <;> simp [hb]
      | inr s =>
        cases s with
        | inl p =>
          by_cases hp : p = P.exit
          · simp [done, hp]
          · simpa [done, hp] using P.readonly p a
        | inr s =>
          cases s with
          | inl q =>
            by_cases hq : q = Q.exit
            · simp [done, hq]
            · simpa [done, hq] using Q.readonly q a
          | inr u => simp [done] }

def branchLeftCfg {M : MultitapeTM} {source : Fin M.k} {test : M.Sym → Bool}
    {P Q : Controller M} (c : P.machine.Cfg) : (branchController source test P Q).machine.Cfg :=
  ⟨Sum.inr (Sum.inl c.state), c.cells, c.head⟩

def branchRightCfg {M : MultitapeTM} {source : Fin M.k} {test : M.Sym → Bool}
    {P Q : Controller M} (c : Q.machine.Cfg) : (branchController source test P Q).machine.Cfg :=
  ⟨Sum.inr (Sum.inr (Sum.inl c.state)), c.cells, c.head⟩

def branchDoneCfg {M : MultitapeTM} {source : Fin M.k} {test : M.Sym → Bool}
    {P Q : Controller M} (cells : Fin M.k → ℕ → M.Sym) (head : Fin M.k → ℕ) :
    (branchController source test P Q).machine.Cfg :=
  ⟨Sum.inr (Sum.inr (Sum.inr ())), cells, head⟩

def branchChooseCfg {M : MultitapeTM} {source : Fin M.k} {test : M.Sym → Bool}
    {P Q : Controller M} (cells : Fin M.k → ℕ → M.Sym) (head : Fin M.k → ℕ) :
    (branchController source test P Q).machine.Cfg :=
  ⟨Sum.inl (), cells, head⟩

end BitDFT.MachineSequence


