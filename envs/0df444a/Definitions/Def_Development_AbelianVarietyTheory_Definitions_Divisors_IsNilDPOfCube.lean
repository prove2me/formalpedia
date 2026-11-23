-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:10.237526+00:00
-- url     : https://prove2.me/theorems/8bacf189-b44d-4b7d-b3cb-aa2320f709ad
-- title:
--   Is Nil DPOf Cube
-- statement:
--   Definitions and structural lemmas for Is Nil DPOf Cube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsNilDPOfCube.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_dOne_smul
import Theorems.Thm_GlobalTheory_CechDR_wedge_smul_left
import Theorems.Thm_GlobalTheory_CechDR_wedge_smul_right
import Theorems.Thm_GlobalTheory_CechDR_wedge_swap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.CechDR
open CatCoh Cris
section Cube
variable {A : Type} [CommRing A] {J : Ideal A} (g : A → A)
open Classical in

def cubePow (J : Ideal A) (g : A → A) : ℕ → A → A
  | 0, x => if x ∈ J then 1 else 0
  | 1, x => if x ∈ J then x else 0
  | 2, x => if x ∈ J then g x else 0
  | _ + 3, _ => 0
def cubeDP (hm : ∀ x ∈ J, g x ∈ J) (ha : ∀ x ∈ J, ∀ y ∈ J, g (x + y) = g x + x * y + g y)
    (hs : ∀ a, ∀ x ∈ J, g (a * x) = a ^ 2 * g x) (h2 : ∀ x ∈ J, x * x = 2 * g x)
    (hk : ∀ x ∈ J, ∀ y ∈ J, g x * y = 0) (hg : ∀ x ∈ J, g (g x) = 0) : DividedPowers J where
  dpow := cubePow J g
  dpow_null {n x} hx := by rcases n with _ | _ | _ | n <;> simp [cubePow, hx]
  dpow_zero hx := by simp [cubePow, hx]
  dpow_one hx := by simp [cubePow, hx]
  dpow_mem {n x} hn hx := by rcases n with _ | _ | _ | n <;> simp_all [cubePow]
  dpow_add {n x y} hx hy := by
    have hxy := J.add_mem hx hy
    rcases n with _ | _ | _ | n
    · simp [cubePow, hx, hy, hxy]
    · simp [cubePow, hx, hy, hxy, Finset.Nat.antidiagonal_succ, add_comm]
    · simp [cubePow, hx, hy, hxy, Finset.Nat.antidiagonal_succ, ha x hx y hy]; ring
    · symm
      refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
      have hij' : i + j = n + 3 := by simpa using hij
      have k1 := hk x hx y hy
      have k2 := hk x hx _ (hm y hy)
      have k3 : x * g y = 0 := by rw [mul_comm, hk y hy x hx]
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        first | omega | simp [cubePow, hx, hy, k1, k2, k3]
  dpow_mul {n a x} hx := by
    have := J.mul_mem_left a hx
    rcases n with _ | _ | _ | n <;> simp [cubePow, hx, this, hs a x hx]
  mul_dpow {m n x} hx := by
    have k1 := hk x hx x hx
    have k2 := hk x hx _ (hm x hx)
    have k3 : x * g x = 0 := by rw [mul_comm, k1]
    rcases m with _ | _ | _ | m <;> rcases n with _ | _ | _ | n <;>
      simp [cubePow, hx, k1, k2, k3, h2 x hx, ← add_assoc]
  dpow_comp {m n x} hn hx := by
    have g0 : g 0 = 0 := by simpa using hs 0 0 J.zero_mem
    have big : 3 ≤ m * n → cubePow J g (m * n) x = 0 := fun hk ↦ by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hk
      rw [hk]; rfl
    rcases m with _ | _ | _ | m <;> rcases n with _ | _ | _ | n <;>
      first
      | exact absurd rfl hn
      | (rw [big (by nlinarith)]; simp [cubePow, hx, hg x hx, hm x hx, g0]; done)
      | simp [cubePow, hx, hm x hx, g0, Nat.uniformBell_zero_left, Nat.uniformBell_one_left,
          Nat.uniformBell_one_right]
theorem isDPNilpotent_of_cube (δ : DividedPowers J) (h3 : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    (h2 : ∀ a ∈ J, ∀ c ∈ J, δ.dpow 2 a * c = 0) (h : ∀ n, 3 ≤ n → ∀ a ∈ J, δ.dpow n a = 0) :
    IsNilDP δ := by
  have key : ∀ l : List (ℕ × A), (∀ p ∈ l, p.2 ∈ J) →
      (1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J) ∧
      (2 ≤ (l.map Prod.fst).sum → ∀ c ∈ J, (l.map fun p ↦ δ.dpow p.1 p.2).prod * c = 0) ∧
      (3 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0) := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hl
      have hp : p.2 ∈ J := hl p (by simp)
      obtain ⟨i1, i2, i3⟩ := ih fun q hq ↦ hl q (by simp [hq])
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rcases hn : p.1 with _ | _ | _ | n
      · simp only [zero_add]
        exact ⟨fun h ↦ J.mul_mem_left _ (i1 h), fun h c hc ↦ by rw [mul_assoc, i2 h c hc, mul_zero],
          fun h ↦ by rw [i3 h, mul_zero]⟩
      · have hm : δ.dpow (0 + 1) p.2 ∈ J := δ.dpow_mem (by simp) hp
        exact ⟨fun _ ↦ J.mul_mem_right _ hm, fun h c hc ↦ h3 _ hm _ (i1 (by omega)) c hc,
          fun h ↦ by rw [mul_comm, i2 (by omega) _ hm]⟩
      · have hm : δ.dpow (0 + 1 + 1) p.2 ∈ J := δ.dpow_mem (by simp) hp
        exact ⟨fun _ ↦ J.mul_mem_right _ hm,
          fun h c hc ↦ by rw [mul_assoc]; exact h2 _ hp _ (J.mul_mem_left _ hc),
          fun h ↦ h2 _ hp _ (i1 (by omega))⟩
      · rw [h _ (by omega) _ hp]; simp
  exact ⟨3, fun l hl ↦ (key l hl).2.2⟩
end Cube
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
def Bi : Type := B × Ω[B⁄R] × Ω[B⁄R] × Om R B 2
namespace Bi
variable {R B}
instance : AddCommGroup (Bi R B) := inferInstanceAs (AddCommGroup (B × Ω[B⁄R] × Ω[B⁄R] × Om R B 2))
instance : Module R (Bi R B) := inferInstanceAs (Module R (B × Ω[B⁄R] × Ω[B⁄R] × Om R B 2))
def mk (b : B) (α β : Ω[B⁄R]) (η : Om R B 2) : Bi R B := (b, α, β, η)
instance : Mul (Bi R B) := ⟨fun x y ↦ mk (x.1 * y.1) (x.1 • y.2.1 + y.1 • x.2.1)
  (x.1 • y.2.2.1 + y.1 • x.2.2.1)
  (x.1 • y.2.2.2 + y.1 • x.2.2.2 + wedge R B x.2.1 y.2.2.1 + wedge R B y.2.1 x.2.2.1)⟩
instance : One (Bi R B) := ⟨mk 1 0 0 0⟩
@[ext] theorem ext' {x y : Bi R B} (h0 : x.1 = y.1) (h1 : x.2.1 = y.2.1) (h2 : x.2.2.1 = y.2.2.1)
    (h3 : x.2.2.2 = y.2.2.2) : x = y := Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
section
variable (b : B) (α β : Ω[B⁄R]) (η : Om R B 2) (x y : Bi R B) (r : R)
@[simp] theorem mk_0 : (mk b α β η).1 = b := rfl
@[simp] theorem mul_0 : (x * y).1 =
    x.1 * y.1 := rfl
@[simp] theorem add_0 : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem sub_0 : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem smul_0 : (r • x).1 = r • x.1 := rfl
@[simp] theorem zero_0 : (0 : Bi R B).1 = 0 := rfl
@[simp] theorem one_0 : (1 : Bi R B).1 = 1 := rfl
@[simp] theorem mk_1 : (mk b α β η).2.1 = α := rfl
@[simp] theorem mul_1 : (x * y).2.1 =
    x.1 • y.2.1 + y.1 • x.2.1 := rfl
@[simp] theorem add_1 : (x + y).2.1 = x.2.1 + y.2.1 := rfl
@[simp] theorem sub_1 : (x - y).2.1 = x.2.1 - y.2.1 := rfl
@[simp] theorem smul_1 : (r • x).2.1 = r • x.2.1 := rfl
@[simp] theorem zero_1 : (0 : Bi R B).2.1 = 0 := rfl
@[simp] theorem one_1 : (1 : Bi R B).2.1 = 0 := rfl
@[simp] theorem mk_2 : (mk b α β η).2.2.1 = β := rfl
@[simp] theorem mul_2 : (x * y).2.2.1 =
    x.1 • y.2.2.1 + y.1 • x.2.2.1 := rfl
@[simp] theorem add_2 : (x + y).2.2.1 = x.2.2.1 + y.2.2.1 := rfl
@[simp] theorem sub_2 : (x - y).2.2.1 = x.2.2.1 - y.2.2.1 := rfl
@[simp] theorem smul_2 : (r • x).2.2.1 = r • x.2.2.1 := rfl
@[simp] theorem zero_2 : (0 : Bi R B).2.2.1 = 0 := rfl
@[simp] theorem one_2 : (1 : Bi R B).2.2.1 = 0 := rfl
@[simp] theorem mk_3 : (mk b α β η).2.2.2 = η := rfl
@[simp] theorem mul_3 : (x * y).2.2.2 =
    x.1 • y.2.2.2 + y.1 • x.2.2.2 + wedge R B x.2.1 y.2.2.1 + wedge R B y.2.1 x.2.2.1 := rfl
@[simp] theorem add_3 : (x + y).2.2.2 = x.2.2.2 + y.2.2.2 := rfl
@[simp] theorem sub_3 : (x - y).2.2.2 = x.2.2.2 - y.2.2.2 := rfl
@[simp] theorem smul_3 : (r • x).2.2.2 = r • x.2.2.2 := rfl
@[simp] theorem zero_3 : (0 : Bi R B).2.2.2 = 0 := rfl
@[simp] theorem one_3 : (1 : Bi R B).2.2.2 = 0 := rfl
end
instance : CommRing (Bi R B) :=
  { (inferInstance : AddCommGroup (Bi R B)), (inferInstance : Mul (Bi R B)),
    (inferInstance : One (Bi R B)) with
    left_distrib := fun a b c ↦ by ext1 <;> simp [mul_add, add_smul] <;> abel
    right_distrib := fun a b c ↦ by ext1 <;> simp [add_mul, add_smul] <;> abel
    zero_mul := fun a ↦ by ext1 <;> simp
    mul_zero := fun a ↦ by ext1 <;> simp
    mul_assoc := fun a b c ↦ by
      ext1
      · simp [mul_assoc]
      · simp; module
      · simp; module
      · simp; module
    one_mul := fun a ↦ by ext1 <;> simp
    mul_one := fun a ↦ by ext1 <;> simp
    mul_comm := fun a b ↦ by ext1 <;> simp [mul_comm] <;> abel }
instance : Algebra R (Bi R B) := Algebra.ofModule
  (fun r x y ↦ by ext1 <;> simp [wedge_smul_left, wedge_smul_right, smul_comm r])
  (fun r x y ↦ by ext1 <;> simp [wedge_smul_left, wedge_smul_right, smul_comm r])
theorem algebraMap_eq (r : R) : algebraMap R (Bi R B) r = mk (algebraMap R B r) 0 0 0 := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  ext1 <;> simp
def π : Bi R B →+* B where
  toFun x := x.1
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
theorem mem_ker {x : Bi R B} : x ∈ RingHom.ker π ↔ x.1 = 0 := Iff.rfl
def sq (x : Bi R B) : Bi R B := mk 0 0 0 (wedge R B x.2.1 x.2.2.1)
def dp : DividedPowers (RingHom.ker (π (R := R) (B := B))) :=
  cubeDP sq (fun _ _ ↦ rfl)
    (fun x hx y hy ↦ by rw [mem_ker] at hx hy; ext1 <;> simp [sq, hx, hy]; abel)
    (fun a x hx ↦ by rw [mem_ker] at hx; ext1 <;> simp [sq, hx, pow_two, mul_smul])
    (fun x hx ↦ by rw [mem_ker] at hx; rw [two_mul]; ext1 <;> simp [sq, hx])
    (fun x hx y hy ↦ by rw [mem_ker] at hx hy; ext1 <;> simp [sq, hy])
    (fun x _ ↦ by ext1 <;> simp [sq])
theorem dp_two {x : Bi R B} (hx : x.1 = 0) : dp.dpow 2 x = sq x := if_pos hx
theorem dp_high {n : ℕ} (hn : 3 ≤ n) (x : Bi R B) : dp.dpow n x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn; rfl
theorem isDPNilpotent_dp : IsNilDP (dp (R := R) (B := B)) :=
  isDPNilpotent_of_cube _ (fun x hx y hy z hz ↦ by rw [mem_ker] at hx hy hz; ext1 <;> simp [hx, hy, hz])
    (fun x hx y hy ↦ by rw [mem_ker] at hx hy; rw [dp_two hx]; ext1 <;> simp [sq, hy])
    fun n hn a _ ↦ dp_high hn a
end Bi
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler
variable {R B}
namespace Bi
def j1 : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] Bi R B where
  toFun c := mk c.fst c.snd 0 0
  map_one' := by ext1 <;> simp
  map_zero' := by ext1 <;> simp
  map_add' a b := by ext1 <;> simp
  map_mul' a b := by ext1 <;> simp
  commutes' r := by rw [algebraMap_eq]; ext1 <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
def j12 : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] Bi R B where
  toFun c := mk c.fst c.snd c.snd 0
  map_one' := by ext1 <;> simp
  map_zero' := by ext1 <;> simp
  map_add' a b := by ext1 <;> simp
  map_mul' a b := by ext1 <;> simp [wedge_swap a.snd]
  commutes' r := by rw [algebraMap_eq]; ext1 <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
def jd : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] Bi R B where
  toFun c := mk c.fst (D R B c.fst) c.snd (dOne R B c.snd)
  map_one' := by ext1 <;> simp
  map_zero' := by ext1 <;> simp
  map_add' a b := by ext1 <;> simp
  map_mul' a b := by ext1 <;> simp [dOne_smul]; abel
  commutes' r := by rw [algebraMap_eq]; ext1 <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
variable {X : Scheme.{0}} {s : X ⟶ Sp R} {x : Sp B ⟶ X} (hx : x ≫ s = spMap (algebraMap R B))
@[reducible] def thick : Thick (dp0 R) s where
  B := Bi R B
  J := RingHom.ker π
  δ := dp
  nil := isDPNilpotent_dp
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := B
  π := π
  surj := fun b ↦ ⟨mk b 0 0 0, rfl⟩
  ker := fun _ ↦ Iff.rfl
  x := x
  w := hx.trans (congrArg spMap (RingHom.ext fun r ↦ congrArg Prod.fst (algebraMap_eq r).symm))
def hom (j : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] Bi R B) (h1 : ∀ c, (j c).1 = c.fst)
    (h2 : ∀ c, c.fst = 0 → sq (j c) = 0) : (diagExt R B).thick x hx ⟶ thick hx where
  φ := j
  φ₀ := RingHom.id B
  comm c := (h1 c).symm
  dp := by
    refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun c hc ↦ (h1 c).trans hc,
      fun n hn a ha ↦ ?_⟩
    have ha' : (j a).1 = 0 := (h1 a).trans ha
    rcases n with _ | _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, DividedPowers.dpow_one _ ha]; exact dp.dpow_one ha'
    · rw [squareZeroDividedPowers_dpow _ (by omega), map_zero]; exact (dp_two ha').trans (h2 a ha)
    · rw [squareZeroDividedPowers_dpow _ (by omega), map_zero]; exact dp_high (by omega) _
  pt := by
    change spMap (RingHom.id B) ≫ x = x
    rw [spMap_id, Category.id_comp]
end Bi
variable {X : Scheme.{0}} {s : X ⟶ Sp R}
end GlobalTheory.CechDR


