-- Prove2me | Definitions.Def_DarpaH2Lifting_Solution
-- name    : DarpaH2Lifting_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:31:12.192336+00:00
-- url     : https://prove2.me/theorems/49032966-290f-5696-a4c9-54011b4293f5
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from AItoBit (AItoBit/DARPA-s-23-Mathematical-Challenges; see pinned Apache-2.0 LICENSE and README.md)'s pinned H2 obstruction to lifting discrete matrix representations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/DARPA-s-23-Mathematical-Challenges/blob/42b1d19b3d53ff5333725ef4410c1e0de84b22d2/Solution.lean

module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NoncommRing
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.TypeTags.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Darpa018.H2Core
variable {G M : Type}
variable [Group G] [AddCommGroup M] [DistribMulAction G M]
def HasSection (c : G × G → M) : Prop :=
  ∃ t : G → M, ∀ g h,
    t (g * h) = t g + g • t h + c (g, h)
noncomputable def obstructionClass
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G M) :=
  (CategoryTheory.ConcreteCategory.hom
    (groupCohomology.H2π (Rep.ofDistribMulAction ℤ G M)))
    (groupCohomology.cocyclesOfIsCocycle₂ (k := ℤ) hc)
end Darpa018.H2Core
namespace Darpa018.MatrixSquareZero
universe u v w
variable {R : Type u} {S : Type v} {n : Type w}
variable [CommRing R] [CommRing S] [Fintype n]
theorem mul_eq_zero_of_map_eq_zero
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (A B : Matrix n n R)
    (hA : A.map f = 0)
    (hB : B.map f = 0) :
    A * B = 0 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply hsq
  · have h := congrArg (fun C : Matrix n n S => C i k) hA
    simpa using h
  · have h := congrArg (fun C : Matrix n n S => C k j) hB
    simpa using h
variable [DecidableEq n]
theorem isUnit_of_square_zero_defects
    (A B : Matrix n n R)
    (hAB : (1 - A * B) * (1 - A * B) = 0)
    (hBA : (1 - B * A) * (1 - B * A) = 0) :
    IsUnit A := by
  let E : Matrix n n R := 1 - A * B
  let F : Matrix n n R := 1 - B * A
  let C : Matrix n n R := B * (1 + E)
  let D : Matrix n n R := (1 + F) * B
  have hright : A * C = 1 := by
    change A * (B * (1 + (1 - A * B))) = 1
    calc
      A * (B * (1 + (1 - A * B))) =
          1 - (1 - A * B) * (1 - A * B) := by noncomm_ring
      _ = 1 := by rw [hAB]; simp
  have hleft : D * A = 1 := by
    change ((1 + (1 - B * A)) * B) * A = 1
    calc
      ((1 + (1 - B * A)) * B) * A =
          1 - (1 - B * A) * (1 - B * A) := by noncomm_ring
      _ = 1 := by rw [hBA]; simp
  have hDC : D = C := by
    calc
      D = D * (A * C) := by rw [hright, mul_one]
      _ = (D * A) * C := (mul_assoc D A C).symm
      _ = C := by rw [hleft, one_mul]
  have hClef : C * A = 1 := by
    rw [← hDC]
    exact hleft
  exact ⟨{ val := A, inv := C, val_inv := hright, inv_val := hClef }, rfl⟩
theorem isUnit_of_squareZeroKernel_approxInverse
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (A B : Matrix n n R)
    (hAB : (1 - A * B).map f = 0)
    (hBA : (1 - B * A).map f = 0) :
    IsUnit A := by
  have h1 : (1 - A * B) * (1 - A * B) = 0 :=
    mul_eq_zero_of_map_eq_zero f hsq _ _ hAB hAB
  have h2 : (1 - B * A) * (1 - B * A) = 0 :=
    mul_eq_zero_of_map_eq_zero f hsq _ _ hBA hBA
  exact isUnit_of_square_zero_defects A B h1 h2
omit [Fintype n] [DecidableEq n] in
/-- A surjective map of coefficients is surjective on matrices. -/
theorem map_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (fun A : Matrix n n R => A.map f) := by
  classical
  intro A
  choose b hb using fun i j => hf (A i j)
  exact ⟨b, funext fun i => funext fun j => hb i j⟩
theorem isUnit_map_iff_of_squareZeroKernel
    (f : R →+* S) (hf : Function.Surjective f)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (A : Matrix n n R) :
    IsUnit (A.map f) ↔ IsUnit A := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨B, hB⟩ := map_surjective (n := n) f hf (↑(u⁻¹))
    change B.map f = (↑(u⁻¹) : Matrix n n S) at hB
    apply isUnit_of_squareZeroKernel_approxInverse f hsq A B
    · change f.mapMatrix (1 - A * B) = 0
      rw [map_sub, map_one, map_mul]
      change 1 - A.map f * B.map f = 0
      rw [hB, ← hu, Units.mul_inv, sub_self]
    · change f.mapMatrix (1 - B * A) = 0
      rw [map_sub, map_one, map_mul]
      change 1 - B.map f * A.map f = 0
      rw [hB, ← hu, Units.inv_mul, sub_self]
  · exact fun h => h.map f.mapMatrix
theorem units_map_surjective_of_squareZeroKernel
    (f : R →+* S) (hf : Function.Surjective f)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Function.Surjective
      (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom) := by
  intro u
  obtain ⟨A, hA⟩ := map_surjective (n := n) f hf (↑u)
  change A.map f = (↑u : Matrix n n S) at hA
  have hunit : IsUnit A :=
    (isUnit_map_iff_of_squareZeroKernel f hf hsq A).mp (hA.symm ▸ u.isUnit)
  obtain ⟨v, hv⟩ := hunit
  refine ⟨v, Units.ext ?_⟩
  change (↑v : Matrix n n R).map f = ↑u
  rw [hv, hA]
theorem units_commute_of_map_eq_one
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (u v : (Matrix n n R)ˣ)
    (hu : Units.map f.mapMatrix.toMonoidHom u = 1)
    (hv : Units.map f.mapMatrix.toMonoidHom v = 1) :
    Commute u v := by
  have hu' : (↑u : Matrix n n R).map f = 1 := congrArg Units.val hu
  have hv' : (↑v : Matrix n n R).map f = 1 := congrArg Units.val hv
  have hU : ((↑u : Matrix n n R) - 1).map f = 0 := by
    change f.mapMatrix ((↑u : Matrix n n R) - 1) = 0
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hu'
  have hV : ((↑v : Matrix n n R) - 1).map f = 0 := by
    change f.mapMatrix ((↑v : Matrix n n R) - 1) = 0
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hv'
  have hUV := mul_eq_zero_of_map_eq_zero f hsq _ _ hU hV
  have hVU := mul_eq_zero_of_map_eq_zero f hsq _ _ hV hU
  change u * v = v * u
  apply Units.ext
  change (↑u : Matrix n n R) * (↑v : Matrix n n R) =
    (↑v : Matrix n n R) * (↑u : Matrix n n R)
  calc
    (↑u : Matrix n n R) * (↑v : Matrix n n R) =
        ((↑u : Matrix n n R) - 1) * ((↑v : Matrix n n R) - 1) +
          (↑u : Matrix n n R) + (↑v : Matrix n n R) - 1 := by noncomm_ring
    _ = ((↑v : Matrix n n R) - 1) * ((↑u : Matrix n n R) - 1) +
          (↑v : Matrix n n R) + (↑u : Matrix n n R) - 1 := by rw [hUV, hVU]; abel
    _ = (↑v : Matrix n n R) * (↑u : Matrix n n R) := by noncomm_ring
theorem units_map_ker_isMulCommutative
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    IsMulCommutative
      (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom).ker := by
  rw [isMulCommutative_iff]
  intro u v
  apply Subtype.ext
  exact units_commute_of_map_eq_one (n := n) f hsq u.val v.val u.property v.property
end Darpa018.MatrixSquareZero
namespace Darpa018.GroupExtension
open scoped IsMulCommutative
variable {G E Q : Type} [Group G] [Group E] [Group Q]
variable (q : E →* Q) [IsMulCommutative q.ker]
theorem conj_eq_of_map_eq (a b : E) (hab : q a = q b) (x : q.ker) :
    a * x * a⁻¹ = b * x * b⁻¹ := by
  let k : q.ker := ⟨b⁻¹ * a, by simp [MonoidHom.mem_ker, hab]⟩
  have hk : (b⁻¹ * a) * (x : E) = (x : E) * (b⁻¹ * a) :=
    congrArg (fun y : q.ker => (y : E)) (mul_comm k x)
  calc
    a * x * a⁻¹ = b * ((b⁻¹ * a) * x) * a⁻¹ := by group
    _ = b * (x * (b⁻¹ * a)) * a⁻¹ := by rw [hk]
    _ = b * x * b⁻¹ := by group
variable (ρ : G →* Q) (l : G → E) (hl : ∀ g, q (l g) = ρ g)
abbrev kernelAction : DistribMulAction G (Additive q.ker) where
  smul g x := Additive.ofMul (MulAut.conjNormal (l g) x.toMul)
  one_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change l 1 * (x.toMul : E) * (l 1)⁻¹ = (x.toMul : E)
    simpa using conj_eq_of_map_eq q (l 1) 1 (by simp [hl]) x.toMul
  mul_smul g h x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change l (g * h) * (x.toMul : E) * (l (g * h))⁻¹ =
      l g * (l h * (x.toMul : E) * (l h)⁻¹) * (l g)⁻¹
    calc
      _ = (l g * l h) * (x.toMul : E) * (l g * l h)⁻¹ :=
        conj_eq_of_map_eq q _ _ (by simp [hl]) _
      _ = _ := by simp only [mul_inv_rev, mul_assoc]
  smul_zero g := by
    apply Additive.toMul.injective
    exact map_one (MulAut.conjNormal (l g))
  smul_add g x y := by
    apply Additive.toMul.injective
    exact map_mul (MulAut.conjNormal (l g)) x.toMul y.toMul
def defect (p : G × G) : Additive q.ker :=
  Additive.ofMul ⟨l p.1 * l p.2 * (l (p.1 * p.2))⁻¹,
    by simp [MonoidHom.mem_ker, hl]⟩
theorem defect_isCocycle :
    letI := kernelAction q ρ l hl
    groupCohomology.IsCocycle₂ (defect q ρ l hl) := by
  let := kernelAction q ρ l hl
  intro g h j
  apply Additive.toMul.injective
  change (defect q ρ l hl (g * h, j)).toMul * (defect q ρ l hl (g, h)).toMul = _
  rw [mul_comm (defect q ρ l hl (g * h, j)).toMul]
  apply Subtype.ext
  change (l g * l h * (l (g * h))⁻¹) *
      (l (g * h) * l j * (l ((g * h) * j))⁻¹) =
    (l g * (l h * l j * (l (h * j))⁻¹) * (l g)⁻¹) *
      (l g * l (h * j) * (l (g * (h * j)))⁻¹)
  rw [mul_assoc g h j]
  group
noncomputable def obstruction :
    letI := kernelAction q ρ l hl
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G (Additive q.ker)) :=
  letI := kernelAction q ρ l hl
  H2Core.obstructionClass (defect q ρ l hl) (defect_isCocycle q ρ l hl)
noncomputable def chosenLift (hq : Function.Surjective q) (g : G) : E :=
  Function.surjInv hq (ρ g)
omit [IsMulCommutative q.ker] in
/-- The chosen preimages lift the homomorphism pointwise. -/
theorem chosenLift_spec (hq : Function.Surjective q) (g : G) :
    q (chosenLift q ρ hq g) = ρ g :=
  Function.surjInv_eq hq (ρ g)
noncomputable abbrev liftingAction (hq : Function.Surjective q) :
    DistribMulAction G (Additive q.ker) :=
  kernelAction q ρ (chosenLift q ρ hq) (chosenLift_spec q ρ hq)
noncomputable def liftingObstruction (hq : Function.Surjective q) :
    letI := liftingAction q ρ hq
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G (Additive q.ker)) :=
  obstruction q ρ (chosenLift q ρ hq) (chosenLift_spec q ρ hq)
end Darpa018.GroupExtension
namespace Darpa018.KernelIdentification
universe u v w
variable {R : Type u} {S : Type v} {n : Type w}
variable [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
abbrev reduction (f : R →+* S) : (Matrix n n R)ˣ →* (Matrix n n S)ˣ :=
  Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom
def toRingKernel (f : R →+* S) (u : Additive (reduction (n := n) f).ker) :
    RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) := by
  refine ⟨(u.toMul.val : Matrix n n R) - 1, ?_⟩
  rw [RingHom.mem_ker, map_sub, map_one]
  have hu : reduction (n := n) f u.toMul.val = 1 := u.toMul.property
  exact sub_eq_zero.mpr (congrArg Units.val hu)
def fromRingKernel (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (X : RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S)) :
    Additive (reduction (n := n) f).ker := by
  have hx : (X.val : Matrix n n R).map f = 0 := X.property
  have hxx : (X.val : Matrix n n R) * X.val = 0 :=
    MatrixSquareZero.mul_eq_zero_of_map_eq_zero f hsq _ _ hx hx
  let v : (Matrix n n R)ˣ :=
    { val := 1 + X.val
      inv := 1 - X.val
      val_inv := by
        calc
          (1 + X.val) * (1 - X.val) = 1 - X.val * X.val := by noncomm_ring
          _ = 1 := by rw [hxx, sub_zero]
      inv_val := by
        calc
          (1 - X.val) * (1 + X.val) = 1 - X.val * X.val := by noncomm_ring
          _ = 1 := by rw [hxx, sub_zero] }
  refine Additive.ofMul ⟨v, ?_⟩
  apply Units.ext
  change f.mapMatrix (1 + X.val) = 1
  rw [map_add, map_one]
  change 1 + (X.val : Matrix n n R).map f = 1
  rw [hx, add_zero]
def kernelAddEquiv (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Additive (reduction (n := n) f).ker ≃+
      RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) where
  toFun := toRingKernel f
  invFun := fromRingKernel f hsq
  left_inv u := by
    apply Additive.ext
    apply Subtype.ext
    apply Units.ext
    change 1 + ((u.toMul.val : Matrix n n R) - 1) = u.toMul.val
    abel
  right_inv X := by
    apply Subtype.ext
    change (1 + (X.val : Matrix n n R)) - 1 = X.val
    abel
  map_add' u v := by
    apply Subtype.ext
    change (u.toMul.val : Matrix n n R) * v.toMul.val - 1 =
      ((u.toMul.val : Matrix n n R) - 1) + ((v.toMul.val : Matrix n n R) - 1)
    have hu : ((u.toMul.val : Matrix n n R) - 1).map f = 0 :=
      (toRingKernel f u).property
    have hv : ((v.toMul.val : Matrix n n R) - 1).map f = 0 :=
      (toRingKernel f v).property
    have huv := MatrixSquareZero.mul_eq_zero_of_map_eq_zero f hsq _ _ hu hv
    calc
      (u.toMul.val : Matrix n n R) * v.toMul.val - 1 =
          ((u.toMul.val : Matrix n n R) - 1) * ((v.toMul.val : Matrix n n R) - 1) +
            (((u.toMul.val : Matrix n n R) - 1) + ((v.toMul.val : Matrix n n R) - 1)) := by
        noncomm_ring
      _ = _ := by rw [huv, zero_add]
def matrixKernelAddEquiv (f : R →+* S) :
    RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) ≃+
      Matrix n n (RingHom.ker f) where
  toFun X i j := ⟨X.val i j, by
    have hx : (X.val : Matrix n n R).map f = 0 := X.property
    exact congrArg (fun A : Matrix n n S => A i j) hx⟩
  invFun X := ⟨fun i j => (X i j).val, by
    change f.mapMatrix (fun i j => (X i j).val) = 0
    ext i j
    exact (X i j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
def coefficientAddEquiv (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Additive (reduction (n := n) f).ker ≃+ Matrix n n (RingHom.ker f) :=
  (kernelAddEquiv f hsq).trans (matrixKernelAddEquiv f)
end Darpa018.KernelIdentification
namespace Darpa018.RepresentationLifting
open scoped IsMulCommutative
variable {G R S n : Type} [Group G] [CommRing R] [CommRing S]
variable [Fintype n] [DecidableEq n]
abbrev reduction (f : R →+* S) : (Matrix n n R)ˣ →* (Matrix n n S)ˣ :=
  Units.map f.mapMatrix.toMonoidHom
variable (f : R →+* S) (hf : Function.Surjective f)
variable (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
variable (ρ : G →* (Matrix n n S)ˣ)
noncomputable abbrev coefficientAction :
    letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
    DistribMulAction G (Additive (reduction (n := n) f).ker) :=
  letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
  GroupExtension.liftingAction (reduction f) ρ
    (MatrixSquareZero.units_map_surjective_of_squareZeroKernel f hf hsq)
noncomputable def obstruction :
    letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
    letI := coefficientAction f hf hsq ρ
    groupCohomology.H2
      (Rep.ofDistribMulAction ℤ G (Additive (reduction (n := n) f).ker)) :=
  letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
  GroupExtension.liftingObstruction (reduction f) ρ
    (MatrixSquareZero.units_map_surjective_of_squareZeroKernel f hf hsq)
end Darpa018.RepresentationLifting


