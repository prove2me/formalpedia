-- Prove2me | Definitions.Def_ULHC_Iso
-- name    : ULHC_Iso
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:44:32.945+00:00
-- url     : https://prove2.me/theorems/7597f30a-21c9-4dbf-a2be-1766fd53655d
-- title:
--   Iso
-- statement:
--   Definitions and structural lemmas for Iso, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean

import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


set_option autoImplicit true
namespace ULHC
open Finset
structure GridIso where
  f : Pt → Pt
  finv : Pt → Pt
  hf : ∀ x, finv (f x) = x
  hf' : ∀ x, f (finv x) = x
  g : Edge → Edge
  ginv : Edge → Edge
  hg : ∀ e, ginv (g e) = e
  hg' : ∀ e, g (ginv e) = e
  ends : ∀ e, Ends (g e) (f e.p) (f e.q)
namespace GridIso
variable (I : GridIso)
def inv : GridIso where
  f := I.finv
  finv := I.f
  hf := I.hf'
  hf' := I.hf
  g := I.ginv
  ginv := I.g
  hg := I.hg'
  hg' := I.hg
  ends := by
    intro e
    have h := I.ends (I.ginv e)
    rw [I.hg'] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2, I.hf, I.hf]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, I.hf, I.hf]; exact ⟨rfl, rfl⟩
end GridIso
def tP (x : Pt) : Pt := (x.2, x.1)
def tE (e : Edge) : Edge :=
  match e.d with
  | .h => ⟨.v, tP e.p⟩
  | .v => ⟨.h, tP e.p⟩
def transposeIso : GridIso where
  f := tP
  finv := tP
  hf := fun _ => rfl
  hf' := fun _ => rfl
  g := tE
  ginv := tE
  hg := by intro e; obtain ⟨d, p⟩ := e; cases d <;> rfl
  hg' := by intro e; obtain ⟨d, p⟩ := e; cases d <;> rfl
  ends := by
    intro e; obtain ⟨d, p1, p2⟩ := e
    left; cases d <;> simp [tE, tP, Edge.q]
def rP (x : Pt) : Pt := (x.1, -x.2)
def rE (e : Edge) : Edge :=
  match e.d with
  | .h => ⟨.h, rP e.p⟩
  | .v => ⟨.v, (e.p.1, -e.p.2 - 1)⟩
def reflectIso : GridIso where
  f := rP
  finv := rP
  hf := fun _ => by simp [rP]
  hf' := fun _ => by simp [rP]
  g := rE
  ginv := rE
  hg := by intro e; obtain ⟨d, p1, p2⟩ := e; cases d <;> simp [rE, rP]
  hg' := by intro e; obtain ⟨d, p1, p2⟩ := e; cases d <;> simp [rE, rP]
  ends := by
    intro e; obtain ⟨d, p1, p2⟩ := e
    cases d
    · left; simp [rE, rP, Edge.q]
    · right; simp [rE, rP, Edge.q]; ring
end ULHC


