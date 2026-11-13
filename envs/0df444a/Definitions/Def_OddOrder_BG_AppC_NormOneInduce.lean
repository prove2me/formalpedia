-- Prove2me | Definitions.Def_OddOrder_BG_AppC_NormOneInduce
-- name    : OddOrder_BG_AppC_NormOneInduce
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:35:06.029865+00:00
-- url     : https://prove2.me/theorems/a03839e7-1f74-467b-9b68-5b424ea78e68
-- title:
--   BG Appendix C: the norm-one Frobenius kernel, induction layer
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Appendix C. The `normOneFrobeniusKernel` induce/support lemmas and the irreducible-character evaluation facts used by the class-sum estimates of Lemmas C.2/C.3. The bundle consists of lemmas and instances.
--
--   Instances record that the concrete Frobenius group $P\rtimes U$ and its additive kernel are finite with invertible cardinality over $\mathbb{C}$ (`normOneFrobeniusGroup_fintype`, `normOneFrobeniusKernel_fintype` and relatives), and that the additive kernel $P$ is abelian.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormOneInduce.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormOneInduce.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Mathlib.Data.Set.Card.Arithmetic

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

/-- The concrete Frobenius group `P ⋊ U` is finite; class-sum coefficients need
a `Fintype` instance.  `SemidirectProduct` is structurally just the product of
its left and right coordinates. -/
noncomputable instance normOneFrobeniusGroup_fintype [Fact p.Prime] :
    Fintype (normOneFrobeniusGroup p q) := by
  letI : Fintype (additiveFieldGroup p q) := Fintype.ofFinite _
  letI : Fintype (normOneUnits p q) := Fintype.ofFinite _
  exact Fintype.ofEquiv (additiveFieldGroup p q × normOneUnits p q)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.left, x.right)
      left_inv := by intro x; rfl
      right_inv := by intro x; ext <;> rfl }

/-- Over `ℂ`, the concrete Frobenius-group cardinality is invertible. -/
noncomputable instance normOneFrobeniusGroup_card_invertible [Fact p.Prime] :
    Invertible (Nat.card (normOneFrobeniusGroup p q) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The additive kernel is finite as a subtype of the concrete Frobenius group. -/
noncomputable instance normOneFrobeniusKernel_fintype [Fact p.Prime] :
    Fintype (normOneFrobeniusKernel p q) :=
  Fintype.ofFinite _

/-- Over `ℂ`, the additive-kernel cardinality is invertible. -/
noncomputable instance normOneFrobeniusKernel_card_invertible [Fact p.Prime] :
    Invertible (Nat.card (normOneFrobeniusKernel p q) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The additive kernel `P` is abelian. -/
noncomputable instance normOneFrobeniusKernel_isMulCommutative [Fact p.Prime] :
    IsMulCommutative (normOneFrobeniusKernel p q) := by
  unfold normOneFrobeniusKernel
  infer_instance

end OddOrder.BG.AppC.NormSet


