-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
-- name    : ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:19.239497+00:00
-- url     : https://prove2.me/theorems/84f5522f-b9e3-435e-a4c5-eca4349e5c01
-- title:
--   Fiber First H0 Injective
-- statement:
--   Definitions and structural lemmas for Fiber First H0 Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiberFirstH0Injective.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_succ
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open Cx Function
noncomputable section
universe u
namespace ProjectiveLinePlaces
variable {R : Type u} [CommRing R] {A B : Cx R}
theorem mem_B_zero (A : Cx R) (x : A.X 0) : x ∈ A.B 0 ↔ x = 0 := Submodule.mem_bot R
theorem mem_B_succ (A : Cx R) (n : ℕ) (x : A.X (n+1)) : x ∈ A.B (n+1) ↔ ∃ y, A.d n y = x :=
  LinearMap.mem_range
theorem fib_d_snd_zero (φ : Hom A B) (x : (fib φ).X 0) : (((fib φ).d 0 x).2 : B.X 0) = φ.f 0 x.1 := by
  have h : (show B.X 0 from B.up.d 0 x.2) = 0 := rfl
  show φ.f 0 x.1 + (show B.X 0 from B.up.d 0 x.2) = _
  rw [h, add_zero]
theorem fib_d_snd_succ (φ : Hom A B) (n : ℕ) (x : (fib φ).X (n+1)) :
    (((fib φ).d (n+1) x).2 : B.X (n+1)) = φ.f (n+1) x.1 - B.d n x.2 := by
  show φ.f (n+1) x.1 + -B.d n x.2 = _
  rw [sub_eq_add_neg]
theorem fib_d_succ_iff (φ : Hom A B) (n : ℕ) (x : (fib φ).X (n+1)) :
    (fib φ).d (n+1) x = 0 ↔ A.d (n+1) x.1 = 0 ∧ φ.f (n+1) x.1 = B.d n x.2 := by
  constructor
  · intro h; exact ⟨congrArg Prod.fst h, sub_eq_zero.mp ((fib_d_snd_succ φ n x).symm.trans (congrArg Prod.snd h))⟩
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 ((fib_d_snd_succ φ n x).trans (sub_eq_zero.mpr h2))
def fibIncl (φ : Hom A B) (n : ℕ) : B.Z n →ₗ[R] (fib φ).Z (n+1) where
  toFun b := ⟨(0, b.1), (fib_d_succ_iff φ n _).mpr ⟨map_zero _, by
    show φ.f (n+1) 0 = B.d n b.1
    rw [map_zero]; exact (b.2 : B.d n b.1 = 0).symm⟩⟩
  map_add' x y := Subtype.ext (Prod.ext (add_zero (0 : A.X (n+1))).symm rfl)
  map_smul' r x := Subtype.ext (Prod.ext (smul_zero r).symm rfl)
def fibδ (φ : Hom A B) (n : ℕ) : B.H n →ₗ[R] (fib φ).H (n + 1) :=
  Submodule.mapQ _ _ (fibIncl φ n) fun x hx => by
    change (x : B.X n) ∈ B.B n at hx
    show ((0, (x : B.X n)) : (fib φ).X (n+1)) ∈ (fib φ).B (n+1)
    refine (mem_B_succ (fib φ) n _).mpr ?_
    cases n with
    | zero =>
      rw [mem_B_zero] at hx
      exact ⟨0, by rw [map_zero, hx]; rfl⟩
    | succ m =>
      obtain ⟨y, hy⟩ := (mem_B_succ B m _).mp hx
      refine ⟨(0, -y), Prod.ext (map_zero (A.d (m+1))) ?_⟩
      refine (fib_d_snd_succ φ m _).trans ?_
      show φ.f (m+1) 0 - B.d m (-y) = (x : B.X (m+1))
      rw [map_zero, map_neg, zero_sub, neg_neg, hy]
def upMap {B B' : Cx R} (β : Hom B B') : ∀ n, B.up.X n →ₗ[R] B'.up.X n
  | 0 => 0
  | m + 1 => β.f m
def fibMap {A B A' B' : Cx R} (φ : Hom A B) (φ' : Hom A' B') (α : Hom A A') (β : Hom B B')
    (hsq : ∀ n x, β.f n (φ.f n x) = φ'.f n (α.f n x)) : Hom (fib φ) (fib φ') where
  f n := (α.f n).prodMap (upMap β n)
  comm n x := by
    refine Prod.ext (α.comm n x.1) ?_
    cases n with
    | zero =>
      exact (congrArg (β.f 0) (fib_d_snd_zero φ x)).trans ((hsq 0 x.1).trans (fib_d_snd_zero φ' ((α.f 0).prodMap (upMap β 0) x)).symm)
    | succ m =>
      refine (congrArg (β.f (m+1)) (fib_d_snd_succ φ m x)).trans ?_
      refine Eq.trans ?_ (fib_d_snd_succ φ' m _).symm
      show β.f (m+1) (φ.f (m+1) x.1 - B.d m x.2) = φ'.f (m+1) (α.f (m+1) x.1) - B'.d m (β.f m x.2)
      rw [map_sub, hsq]
      exact congrArg (fun t => φ'.f (m+1) (α.f (m+1) x.1) - t) (β.comm m x.2)
def kerMap {A B C : Cx R} (i : Hom A B) (p : Hom B C) (hs : SES i p) : Hom A (fib p) where
  f n := (i.f n).prod 0
  comm n x := by
    refine Prod.ext (i.comm n x) ?_
    cases n with
    | zero => exact ((fib_d_snd_zero p _).trans ((hs.exact 0).apply_apply_eq_zero x)).symm
    | succ m =>
      refine ((fib_d_snd_succ p m _).trans ?_).symm
      show p.f (m+1) (i.f (m+1) x) - C.d m 0 = 0
      rw [map_zero, sub_zero]; exact (hs.exact _).apply_apply_eq_zero x
end ProjectiveLinePlaces
open ProjectiveLinePlaces
end
end ReciprocityTheory.Coh


