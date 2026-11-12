-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IsReal
-- name    : OddOrder_GroupTheory_RepresentationTheory_IsReal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:01:27.635205+00:00
-- url     : https://prove2.me/theorems/1683d2a4-ff4f-40f5-ac03-e7b4a102e91e
-- title:
--   Real (self-conjugate) class functions
-- statement:
--   For a star ring $k$ (typically $\mathbb{C}$), the conjugate of a class function $\varphi$ is $\bar\varphi(g)=\mathrm{star}(\varphi(g))$, and $\varphi$ is real when $\bar\varphi=\varphi$. This supports Peterfalvi §3 (1.1): for $|G|$ odd, $\chi\in\mathrm{Irr}(G)$ with $\chi\ne1_G$ implies $\bar\chi\ne\chi$. Mathlib has no API for complex conjugation of class functions.
--
--   Main definitions: `ClassFunction.conj` (the conjugate class function), `IsReal`, `trivialClassFunction_isReal`, `RealIrreducibleCharacter` (the type of real irreducible characters) and `trivialRealIrreducibleCharacter`.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/IsReal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/IsReal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k] [StarRing k]

/-- **Conjugate** of a class function: `φ.conj g = star (φ g)`.

Over `k = ℂ` this is the usual `χ ↦ χ̄`. -/
def conj (φ : ClassFunction G k) : ClassFunction G k :=
  ⟨fun g => star (φ g), fun g h => by
    change star (φ (h * g * h⁻¹)) = star (φ g)
    rw [φ.conj_eq]⟩

@[simp] theorem conj_apply (φ : ClassFunction G k) (g : G) :
    φ.conj g = star (φ g) := rfl

@[simp] theorem conj_conj (φ : ClassFunction G k) : φ.conj.conj = φ := by
  ext g
  simp

/-- Conjugation does not move the support: `star x = 0 ↔ x = 0`. -/
@[simp] theorem conj_support (φ : ClassFunction G k) : φ.conj.support = φ.support := by
  ext g
  simp [ClassFunction.mem_support, star_eq_zero]

/-- `ClassFunction.conj` **is** the coefficientwise complex conjugation
(`mapRingEquiv Complex.conjAe`): both are pointwise `star`. -/
theorem conj_eq_mapRingEquiv_conjAe {G : Type*} [Group G] (φ : ClassFunction G ℂ) :
    φ.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ :=
  ClassFunction.ext fun _ => rfl

@[simp] theorem conj_zero : (0 : ClassFunction G k).conj = 0 := by
  ext g
  simp

theorem conj_add (φ ψ : ClassFunction G k) : (φ + ψ).conj = φ.conj + ψ.conj := by
  ext g
  simp [star_add]

theorem conj_neg (φ : ClassFunction G k) : (-φ).conj = -(φ.conj) := by
  ext g
  simp

theorem conj_sub (φ ψ : ClassFunction G k) : (φ - ψ).conj = φ.conj - ψ.conj := by
  ext g
  simp [star_sub]

/-- A class function `φ` is **real** if it equals its conjugate (`φ̄ = φ`).

Over `k = ℂ` this means `φ(g) ∈ ℝ` for all `g : G`. -/
def IsReal (φ : ClassFunction G k) : Prop := φ.conj = φ

end ClassFunction

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem trivialClassFunction_isReal :
    ClassFunction.IsReal (trivialClassFunction G) := by
  unfold ClassFunction.IsReal
  ext g
  simp [trivialClassFunction]

/-- The type of real irreducible complex characters of `G`.

This is Peterfalvi's `χ ∈ Irr(G)` with `χ̄ = χ`, named so that Brauer's
permutation lemma and the odd-order specializations do not repeat the raw
subtype expression. -/
abbrev RealIrreducibleCharacter (G : Type*) [Group G] :=
  {χ : IrreducibleCharacter G // ClassFunction.IsReal (χ : ClassFunction G ℂ)}

/-- The trivial real irreducible character of `G`. -/
def trivialRealIrreducibleCharacter (G : Type*) [Group G] :
    RealIrreducibleCharacter G :=
  ⟨trivialIrreducibleCharacter G, by simp⟩

namespace RealIrreducibleCharacter

variable {G : Type*} [Group G]

instance : Coe (RealIrreducibleCharacter G) (IrreducibleCharacter G) :=
  ⟨fun χ => χ.1⟩

instance : Coe (RealIrreducibleCharacter G) (ClassFunction G ℂ) :=
  ⟨fun χ => (χ.1 : ClassFunction G ℂ)⟩

@[simp] theorem coe_mk (χ : IrreducibleCharacter G)
    (hχ : ClassFunction.IsReal (χ : ClassFunction G ℂ)) :
    ((⟨χ, hχ⟩ : RealIrreducibleCharacter G) : IrreducibleCharacter G) = χ :=
  rfl

@[simp] theorem coe_trivialRealIrreducibleCharacter :
    ((trivialRealIrreducibleCharacter G : RealIrreducibleCharacter G) :
      IrreducibleCharacter G) = trivialIrreducibleCharacter G :=
  rfl

@[simp] theorem coe_mk_classFunction (χ : IrreducibleCharacter G)
    (hχ : ClassFunction.IsReal (χ : ClassFunction G ℂ)) :
    ((⟨χ, hχ⟩ : RealIrreducibleCharacter G) : ClassFunction G ℂ) =
      (χ : ClassFunction G ℂ) :=
  rfl

@[simp] theorem isReal (χ : RealIrreducibleCharacter G) :
    ClassFunction.IsReal (χ : ClassFunction G ℂ) :=
  χ.2

@[simp] theorem isIrreducible (χ : RealIrreducibleCharacter G) :
    IsIrreducibleCharacter (χ : ClassFunction G ℂ) :=
  χ.1.isIrreducible

@[ext] theorem ext {χ ψ : RealIrreducibleCharacter G}
    (h : (χ : IrreducibleCharacter G) = (ψ : IrreducibleCharacter G)) : χ = ψ :=
  Subtype.ext h

end RealIrreducibleCharacter

end OddOrder.RepresentationTheory


