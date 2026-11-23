-- Prove2me | Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
-- name    : GroundTheory_LocalFields_CompleteTrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:02.444226+00:00
-- url     : https://prove2.me/theorems/544798b2-7990-4095-9d31-e60b023b0054
-- title:
--   Complete Trivial
-- statement:
--   Definitions and structural lemmas for Complete Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open Finset Filter
section Tate
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
def tateNorm : M →* M where
  toFun x := ∏ g : G, g • x
  map_one' := by simp
  map_mul' x y := by simp only [smul_mul', prod_mul_distrib]
def invariants : Subgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  one_mem' g := smul_one g
  mul_mem' {x y} hx hy g := by rw [smul_mul', hx g, hy g]
  inv_mem' {x} hx g := by rw [smul_inv', hx g]
def augmentation : Subgroup M :=
  Subgroup.closure {y | ∃ (g : G) (x : M), g • x / x = y}
abbrev TateZero : Type _ :=
  invariants G M ⧸ (tateNorm G M).range.subgroupOf (invariants G M)
abbrev TateNegOne : Type _ :=
  (tateNorm G M).ker ⧸ (augmentation G M).subgroupOf (tateNorm G M).ker
def augMap : (G → M) →* M where
  toFun m := ∏ g : G, g • m g / m g
  map_one' := by simp
  map_mul' m m' := by
    simp only [Pi.mul_apply, smul_mul', ← prod_mul_distrib, div_mul_div_comm]
variable {G M}
end Tate
section Filtration
structure StableFiltration (G V : Type*) [Group G] [CommGroup V] [MulDistribMulAction G V] where

  F : ℕ → Subgroup V

  antitone : Antitone F

  smul_mem : ∀ (n : ℕ) (g : G) {x : V}, x ∈ F n → g • x ∈ F n
namespace StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
instance instMulDistribMulActionF (n : ℕ) : MulDistribMulAction G (S.F n) where
  smul g x := ⟨g • (x : V), S.smul_mem n g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : V))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : V))
  smul_mul g x y := Subtype.ext (smul_mul' g (x : V) y)
  smul_one g := Subtype.ext (smul_one g)
def gr (n : ℕ) : Type _ := S.F n ⧸ (S.F (n + 1)).subgroupOf (S.F n)
instance instCommGroupGr (n : ℕ) : CommGroup (S.gr n) :=
  QuotientGroup.Quotient.commGroup _
def grMk (n : ℕ) : S.F n →* S.gr n := QuotientGroup.mk' _
theorem grMk_surjective (n : ℕ) : Function.Surjective (S.grMk n) :=
  QuotientGroup.mk'_surjective _
def grAct (n : ℕ) (g : G) : S.gr n →* S.gr n :=
  QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom (S.F n) g) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact S.smul_mem (n + 1) g hx
theorem grAct_grMk {n : ℕ} (g : G) (x : S.F n) : S.grAct n g (S.grMk n x) = S.grMk n (g • x) :=
  rfl
instance instMulDistribMulActionGr (n : ℕ) : MulDistribMulAction G (S.gr n) where
  smul g q := S.grAct n g q
  one_smul q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    exact (S.grAct_grMk 1 x).trans (congrArg _ (one_smul G x))
  mul_smul g h q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    change S.grAct n (g * h) (S.grMk n x) = S.grAct n g (S.grAct n h (S.grMk n x))
    rw [grAct_grMk, grAct_grMk, grAct_grMk, mul_smul]
  smul_mul g q r := map_mul (S.grAct n g) q r
  smul_one g := map_one (S.grAct n g)
variable [Fintype G]
end StableFiltration
end Filtration
section Complete
variable {V : Type*} [CommGroup V]
variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]
end Complete
end GroundTheory.LocalField


