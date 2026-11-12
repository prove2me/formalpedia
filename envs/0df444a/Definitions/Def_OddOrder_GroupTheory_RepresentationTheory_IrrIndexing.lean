-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
-- name    : OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:56:27.668915+00:00
-- url     : https://prove2.me/theorems/d325e2f1-ecc2-4f12-b494-fbd8bfa84e21
-- title:
--   Indexing irreducible characters
-- statement:
--   Names the subtype of irreducible complex characters as a first-class indexing type, so that statements on column orthogonality, Brauer permutation and Peterfalvi §3 use a uniform API. Existence and finiteness of the indexing type are not proved here; statements take an explicit `Fintype` hypothesis.
--
--   Main definitions: `IrreducibleCharacter` (the type of irreducible characters of $G$ as class functions), `trivialIrreducibleCharacter`, and `toClassFunction` (the underlying class function of an index).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrr

namespace OddOrder.RepresentationTheory

variable (G : Type*) [Group G]

/-- The type of irreducible complex characters of `G`, as class functions. -/
abbrev IrreducibleCharacter :=
  {φ : ClassFunction G ℂ // IsIrreducibleCharacter φ}

/-- The trivial irreducible character of `G`. -/
def trivialIrreducibleCharacter : IrreducibleCharacter G :=
  ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩

namespace IrreducibleCharacter

variable {G}

/-- The underlying class function of an irreducible character index. -/
abbrev toClassFunction (χ : IrreducibleCharacter G) : ClassFunction G ℂ :=
  χ.1

instance : Coe (IrreducibleCharacter G) (ClassFunction G ℂ) :=
  ⟨toClassFunction⟩

@[simp] theorem coe_trivialIrreducibleCharacter :
    ((trivialIrreducibleCharacter G : IrreducibleCharacter G) : ClassFunction G ℂ) =
      trivialClassFunction G :=
  rfl

@[simp] theorem coe_mk (φ : ClassFunction G ℂ) (hφ : IsIrreducibleCharacter φ) :
    ((⟨φ, hφ⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = φ :=
  rfl

@[simp] theorem isIrreducible (χ : IrreducibleCharacter G) :
    IsIrreducibleCharacter (χ : ClassFunction G ℂ) :=
  χ.2

@[simp] theorem mem_irreducibleCharacters (χ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ∈ irreducibleCharacters G :=
  χ.2

theorem mem_ZIrr (χ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ∈ ZIrr G :=
  IsIrreducibleCharacter.mem_ZIrr χ.2

@[ext] theorem ext {χ ψ : IrreducibleCharacter G}
    (h : (χ : ClassFunction G ℂ) = (ψ : ClassFunction G ℂ)) : χ = ψ :=
  Subtype.ext h

@[simp] theorem eta (χ : IrreducibleCharacter G) :
    (⟨(χ : ClassFunction G ℂ), χ.isIrreducible⟩ : IrreducibleCharacter G) = χ :=
  rfl

end IrreducibleCharacter

end OddOrder.RepresentationTheory


