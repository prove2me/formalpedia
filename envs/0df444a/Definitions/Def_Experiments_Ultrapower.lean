-- Prove2me | Definitions.Def_Experiments_Ultrapower
-- name    : Experiments_Ultrapower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:50.292797+00:00
-- url     : https://prove2.me/theorems/d4d66ac8-2d1e-460b-8632-f676ef667736
-- title:
--   Ultrapower
-- statement:
--   Definitions and structural lemmas for Ultrapower, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean

import Mathlib
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
namespace Experiments.NSA
abbrev Hyp (α : Type*) : Type _ := Germ (hyperfilter ℕ : Filter ℕ) α
abbrev std {α : Type*} (x : α) : Hyp α := Germ.const x
abbrev ext {α β : Type*} (f : α → β) (ξ : Hyp α) : Hyp β := Germ.map f ξ
def ω : Hyp ℕ := Germ.ofFun id
def IMem {α : Type*} (ξ : Hyp α) (s : Set α) : Prop := ξ.LiftPred (· ∈ s)
def Approx {E : Type*} [SeminormedAddCommGroup E] (x y : Hyp E) : Prop :=
  (x - y).Tendsto (𝓝 0)
@[inherit_doc] scoped infix:50 " ≈ₕ " => Approx
section Extension
variable {α β γ : Type*}
end Extension
section Approx
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
end Approx
end Experiments.NSA


