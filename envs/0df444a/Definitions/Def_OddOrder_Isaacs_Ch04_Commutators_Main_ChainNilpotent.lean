-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
-- name    : OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:23:30.867293+00:00
-- url     : https://prove2.me/theorems/05bc1f68-58d7-4660-9ea2-069b7966bfe1
-- title:
--   Isaacs §4C, Thm 4.24: a faithful chain action forces $A$ nilpotent
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, §4C, Thm 4.24: if $A$ acts faithfully on a chain, then $A$ is nilpotent. The file sets up the limit term of the lower central series and the associated action commutator.
--
--   Main definitions: `lowerCentralSeriesInfty` (the limit term $A^\infty$ of the lower central series of a finite group $A$), `phiInfty` (the induced homomorphism $A^\infty\to\mathrm{Aut}(G)$), `actionCommutatorInfty` ($[G,A^\infty]$) and its normality in $G$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/ChainNilpotent.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/ChainNilpotent.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

variable {A : Type*} [Group A]

/-- The "infinity term" of the lower central series for a finite group `A`:
`A^∞ := lowerCentralSeries A (Nat.card A)`. For a finite group this is the eventual
stable value of the lower central series. -/
noncomputable def lowerCentralSeriesInfty (A : Type*) [Group A] [Finite A] : Subgroup A :=
  (⊤ : Subgroup A).lowerCentralSeries (Nat.card A)

end

section

variable {A : Type*} [Group A]

/-- The composed hom `lowerCentralSeriesInfty A →* MulAut G` obtained by restricting `φ`. -/
private noncomputable def phiInfty {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* MulAut G) :
    (lowerCentralSeriesInfty A) →* MulAut G :=
  φ.comp (lowerCentralSeriesInfty A).subtype

/-- **A^∞ の作用 commutator** = `⁅G, A^∞⁆` (内部記法). Subgroup-typed. -/
private noncomputable def actionCommutatorInfty {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* MulAut G) : Subgroup G :=
  actionCommutator (phiInfty φ)

/-- `[G, A^∞]` is normal in G (inherited from `actionCommutator.normal`). -/
private instance actionCommutatorInfty_normal
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    (actionCommutatorInfty φ).Normal :=
  actionCommutator.normal (phiInfty φ)

end

end OddOrder.Isaacs.Ch04


