-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.subsingleton_smallEtale_additive_succ_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T01:50:31.88747+00:00
-- url     : https://prove2.me/submissions/cdce6f9a-be6a-4d44-a842-4ce04a3871a1

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Mathlib.Algebra.Homology.Functor

noncomputable section

section

open AlgebraicGeometry CategoryTheory

namespace PhilipponAffineEtaleTorsorCocycle
universe u
variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

abbrev baseMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

abbrev specMap (k : A →ₐ[R] B) := Spec.map (CommRingCat.ofHom k.toRingHom)

theorem specMap_over (k : A →ₐ[R] B) : specMap k ≫ baseMap R A = baseMap R B := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact k.commutes x

end PhilipponAffineEtaleTorsorCocycle

end

section

set_option autoImplicit false
set_option maxHeartbeats 600000

open scoped BigOperators TensorProduct
open PiTensorProduct LinearMap


namespace PhilipponAmitsur

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- Tensor powers indexed by the number of factors. The augmented degree is zero factors. -/
abbrev Terms (n : ℕ) := ⨂[A] _ : Fin n, B

variable {A B}

def insertOne {n : ℕ} (i : Fin (n + 1)) : Terms A B n →ₗ[A] Terms A B (n + 1) :=
  PiTensorProduct.lift ((PiTensorProduct.tprod A (s := fun _ : Fin (n + 1) => B)).curryMid i 1)

@[simp] theorem insertOne_tprod {n : ℕ} (i : Fin (n + 1)) (x : Fin n → B) :
    insertOne (A := A) i (PiTensorProduct.tprod A x) = PiTensorProduct.tprod A (i.insertNth 1 x) := by
  rw [insertOne, PiTensorProduct.lift.tprod]
  rfl

def prepend {n : ℕ} (b : B) : Terms A B n →ₗ[A] Terms A B (n + 1) :=
  PiTensorProduct.lift ((PiTensorProduct.tprod A (s := fun _ : Fin (n + 1) => B)).curryLeft b)

@[simp] theorem prepend_tprod {n : ℕ} (b : B) (x : Fin n → B) :
    prepend (A := A) b (PiTensorProduct.tprod A x) = PiTensorProduct.tprod A (Fin.cons b x) := by
  simp [prepend, PiTensorProduct.lift.tprod, MultilinearMap.curryLeft_apply]

private theorem prepend_one {n : ℕ} :
    prepend (A := A) (n := n) (1 : B) = insertOne 0 := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, prepend_tprod, insertOne_tprod]
  rw [Fin.insertNth_zero]
  rfl

private theorem insertOne_prepend {n : ℕ} (b : B) (i : Fin (n + 1)) :
    (insertOne (A := A) i.succ).comp (prepend b) =
      (prepend b).comp (insertOne i) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, insertOne_tprod,
    prepend_tprod, Fin.insertNth_succ_cons]

variable (A B)

/-- The alternating sum of all unit insertions in the augmented Amitsur complex. -/
def d (n : ℕ) : Terms A B n →ₗ[A] Terms A B (n + 1) :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • insertOne i

variable {A B}

theorem d_apply (n : ℕ) (z : Terms A B n) :
    d A B n z = ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • insertOne i z := by
  simp only [d, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact map_zsmul
    (LinearMap.evalAddMonoidHom (σ₁₂ := RingHom.id A) (M₂ := Terms A B (n + 1)) z)
    ((-1 : ℤ) ^ (i : ℕ)) (insertOne i)

theorem d_prepend {n : ℕ} (b : B) (z : Terms A B n) :
    d A B (n + 1) (prepend b z) =
      prepend 1 (prepend b z) - prepend b (d A B n z) := by
  have h (i : Fin (n + 1)) : insertOne i.succ (prepend (A := A) b z) =
      prepend b (insertOne i z) := DFunLike.congr_fun (insertOne_prepend b i) z
  rw [d_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, ← prepend_one, Fin.val_succ, h,
    pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [d_apply n z, map_sum]
  simp only [map_zsmul]

/-- Consecutive Amitsur differentials compose to zero. -/
theorem d_d (n : ℕ) : (d A B (n + 1)).comp (d A B n) = 0 := by
  induction n with
  | zero =>
    apply PiTensorProduct.ext
    ext x
    have h₁ : d A B 0 = prepend (1 : B) := by
      dsimp only [d]
      rw [Fin.sum_univ_one]
      simpa only [Fin.val_zero, pow_zero, one_zsmul] using prepend_one.symm
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      h₁, d_prepend, sub_self]
  | succ n ih =>
    apply PiTensorProduct.ext
    ext x
    have hx : PiTensorProduct.tprod A x = prepend (x 0) (PiTensorProduct.tprod A (Fin.tail x)) := by
      rw [prepend_tprod, Fin.cons_self_tail]
    rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hx, d_prepend, map_sub,
      d_prepend, d_prepend, d_prepend]
    have hz : d A B (n + 1) (d A B n (PiTensorProduct.tprod A (Fin.tail x))) = 0 :=
      DFunLike.congr_fun ih _
    rw [hz, map_sub, map_zero, LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
    abel

variable (A B)

/-- Splitting off the first factor by multilinearity. -/
private def splitHead (n : ℕ) : Terms A B (n + 1) →ₗ[A] B ⊗[A] Terms A B n :=
  PiTensorProduct.lift <| LinearMap.uncurryLeft
    ((PiTensorProduct.lift (R := A) (s := fun _ : Fin n => B)
      (E := B ⊗[A] Terms A B n)).symm.toLinearMap.comp (TensorProduct.mk A B (Terms A B n)))

private theorem splitHead_tprod (n : ℕ) (x : Fin (n + 1) → B) :
    splitHead A B n (PiTensorProduct.tprod A x) = x 0 ⊗ₜ[A] PiTensorProduct.tprod A (Fin.tail x) := by
  rw [splitHead, PiTensorProduct.lift.tprod]
  simp [LinearMap.uncurryLeft_apply, PiTensorProduct.lift_symm]

private def contraction (n : ℕ) : B ⊗[A] Terms A B (n + 1) →ₗ[A] B ⊗[A] Terms A B n :=
  (TensorProduct.map (LinearMap.mul' A B) LinearMap.id).comp
    ((TensorProduct.assoc A B B (Terms A B n)).symm.toLinearMap.comp
      (LinearMap.lTensor B (splitHead A B n)))

variable {A B}

private theorem contraction_tprod {n : ℕ} (b : B) (x : Fin (n + 1) → B) :
    contraction A B n (b ⊗ₜ[A] PiTensorProduct.tprod A x) = (b * x 0) ⊗ₜ[A] PiTensorProduct.tprod A (Fin.tail x) := by
  simp [contraction, splitHead_tprod]

private theorem contraction_prepend {n : ℕ} (b c : B) (z : Terms A B n) :
    contraction A B n (b ⊗ₜ[A] prepend c z) = (b * c) ⊗ₜ[A] z := by
  have h : (contraction A B n).comp ((TensorProduct.mk A B _) b |>.comp (prepend c)) =
      (TensorProduct.mk A B _) (b * c) := by
    apply PiTensorProduct.ext
    ext x
    simp [contraction_tprod]
  exact DFunLike.congr_fun h z

/-- Multiplying the first two factors contracts the Amitsur complex after tensoring with the cover. -/
private theorem contraction_identity (n : ℕ) :
    (contraction A B (n + 1)).comp (LinearMap.lTensor B (d A B (n + 1))) +
      (LinearMap.lTensor B (d A B n)).comp (contraction A B n) = LinearMap.id := by
  apply TensorProduct.ext
  ext b x
  have hx : PiTensorProduct.tprod A x = prepend (x 0) (PiTensorProduct.tprod A (Fin.tail x)) := by
    rw [prepend_tprod, Fin.cons_self_tail]
  change ((contraction A B (n + 1)).comp (LinearMap.lTensor B (d A B (n + 1))) +
    (LinearMap.lTensor B (d A B n)).comp (contraction A B n))
      (b ⊗ₜ[A] PiTensorProduct.tprod A x) = b ⊗ₜ[A] PiTensorProduct.tprod A x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul]
  rw [hx, d_prepend, TensorProduct.tmul_sub, map_sub, contraction_prepend, contraction_prepend,
    contraction_prepend, LinearMap.lTensor_tmul, mul_one, sub_add_cancel]

private theorem exact_of_contractions
    {P Q T : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
    [Module A P] [Module A Q] [Module A T]
    (f : P →ₗ[A] Q) (g : Q →ₗ[A] T) (r : Q →ₗ[A] P) (s : T →ₗ[A] Q)
    (hzero : g.comp f = 0) (hcontract : s.comp g + f.comp r = LinearMap.id) :
    Function.Exact f g := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · rintro x hx
    change g x = 0 at hx
    refine ⟨r x, ?_⟩
    have h := DFunLike.congr_fun hcontract x
    simpa [hx] using h
  · exact LinearMap.range_le_ker_iff.mpr hzero

/-- Faithfully flat descent gives exactness of the augmented Amitsur complex. -/
theorem exact [Module.FaithfullyFlat A B] (n : ℕ) :
    Function.Exact (d A B n) (d A B (n + 1)) := by
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).mp
  apply exact_of_contractions _ _ _ _ ?_ (contraction_identity n)
  rw [← LinearMap.lTensor_comp, d_d, LinearMap.lTensor_zero]

/-- The Amitsur complex with arbitrary module coefficients remains exact.
The contraction is constructed before tensoring with the coefficients. -/
theorem exactWithCoefficients [Module.FaithfullyFlat A B] (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Exact ((d A B n).rTensor M) ((d A B (n + 1)).rTensor M) := by
  refine (Module.FaithfullyFlat.lTensor_exact_iff_exact A B
    (N1 := Terms A B n ⊗[A] M) (N2 := Terms A B (n + 1) ⊗[A] M)
    (N3 := Terms A B (n + 2) ⊗[A] M)
    ((d A B n).rTensor M) ((d A B (n + 1)).rTensor M)).mp ?_
  have h : Function.Exact ((LinearMap.lTensor B (d A B n)).rTensor M)
      ((LinearMap.lTensor B (d A B (n + 1))).rTensor M) := by
    refine exact_of_contractions _ _
      (P := (B ⊗[A] Terms A B n) ⊗[A] M)
      (Q := (B ⊗[A] Terms A B (n + 1)) ⊗[A] M)
      (T := (B ⊗[A] Terms A B (n + 2)) ⊗[A] M)
      ((contraction A B n).rTensor M) ((contraction A B (n + 1)).rTensor M) ?_ ?_
    · rw [← LinearMap.rTensor_comp, ← LinearMap.lTensor_comp, d_d,
        LinearMap.lTensor_zero, LinearMap.rTensor_zero]
    · rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_add,
        contraction_identity, LinearMap.rTensor_id]
  exact h.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.assoc A B (Terms A B n) M)
    (e₂ := TensorProduct.assoc A B (Terms A B (n + 1)) M)
    (e₃ := TensorProduct.assoc A B (Terms A B (n + 1 + 1)) M)
    (LinearMap.lTensor_rTensor_comp_assoc (R := A) (P := B) (Q := M) (Terms A B n) (d A B n))
    (LinearMap.lTensor_rTensor_comp_assoc (R := A) (P := B) (Q := M) (Terms A B (n + 1)) (d A B (n + 1)))

end PhilipponAmitsur

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open AlgebraicGeometry CategoryTheory PiTensorProduct


namespace PhilipponAmitsur

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The unit insertions are algebra morphisms on the rings of the affine Čech terms. -/
def insertOneAlg {n : ℕ} (i : Fin (n + 1)) : Terms A B n →ₐ[A] Terms A B (n + 1) :=
  PiTensorProduct.liftAlgHom
    ((PiTensorProduct.tprod A (s := fun _ : Fin (n + 1) => B)).curryMid i 1)
    (by
      change PiTensorProduct.tprod A (i.insertNth 1 1 : Fin (n + 1) → B) = 1
      rw [PiTensorProduct.one_def]
      congr 1
      funext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp)
    (by
      intro x y
      change PiTensorProduct.tprod A (i.insertNth (α := fun _ => B) 1 (x * y)) =
        PiTensorProduct.tprod A (i.insertNth (α := fun _ => B) 1 x) *
          PiTensorProduct.tprod A (i.insertNth (α := fun _ => B) 1 y)
      rw [PiTensorProduct.tprod_mul_tprod]
      congr 1
      funext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp)

@[simp] theorem insertOneAlg_linear {n : ℕ} (i : Fin (n + 1)) :
    (insertOneAlg (A := A) (B := B) i).toLinearMap = insertOne i := rfl

/-- The maps from each factor into the chosen tensor power. -/
def coordinate {n : ℕ} (i : Fin n) : B →ₐ[A] Terms A B n :=
  PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin n => B) i

theorem insertOneAlg_coordinate {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (insertOneAlg (A := A) i).comp (coordinate (B := B) j) = coordinate (i.succAbove j) := by
  ext a
  change insertOne (A := A) i (PiTensorProduct.tprod A (MonoidHom.mulSingle _ j a)) =
    PiTensorProduct.tprod A (MonoidHom.mulSingle _ (i.succAbove j) a)
  rw [insertOne_tprod]
  congr 1
  funext k
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · simp [Fin.succAbove_ne]
  · simp only [Fin.insertNth_apply_succAbove]
    by_cases hk : k = j
    · subst k
      simp
    · have h' : i.succAbove k ≠ i.succAbove j :=
        fun e => hk (Fin.succAbove_right_injective e)
      simp [Pi.mulSingle_eq_of_ne, hk, h']

variable {S : Type*} [CommRing S] [Algebra A S]

/-- A family of algebra maps out of the factors induces the tensor-power map. -/
def liftCoordinates {n : ℕ} (a : Fin n → B →ₐ[A] S) : Terms A B n →ₐ[A] S :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra A (Fin n) S).compLinearMap fun i => (a i).toLinearMap)
    (by simp [MultilinearMap.mkPiAlgebra_apply])
    (by simp [MultilinearMap.mkPiAlgebra_apply, Finset.prod_mul_distrib])

private theorem liftCoordinates_tprod {n : ℕ} (a : Fin n → B →ₐ[A] S) (x : Fin n → B) :
    liftCoordinates a (PiTensorProduct.tprod A x) = ∏ i, a i (x i) := by
  simp [liftCoordinates, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply]

@[simp] theorem liftCoordinates_coordinate {n : ℕ} (a : Fin n → B →ₐ[A] S) (i : Fin n) :
    (liftCoordinates a).comp (coordinate i) = a i := by
  ext x
  change liftCoordinates a (PiTensorProduct.tprod A (MonoidHom.mulSingle _ i x)) = a i x
  rw [liftCoordinates_tprod, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne, hj]
  · simp

theorem existsUnique_liftCoordinates {n : ℕ} (a : Fin n → B →ₐ[A] S) :
    ∃! f : Terms A B n →ₐ[A] S, ∀ i, f.comp (coordinate i) = a i := by
  refine ⟨liftCoordinates a, liftCoordinates_coordinate a, fun g hg => ?_⟩
  exact PiTensorProduct.algHom_ext (fun i => (hg i).trans (liftCoordinates_coordinate a i).symm)

end PhilipponAmitsur

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponAffineEtaleTorsorCocycle (baseMap specMap specMap_over)


namespace PhilipponAmitsur

universe u

private def onFunctions {C : Type u} [CommRing C] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of C)) : C →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (.of C)).inv ≫ f.appTop).hom

private theorem onFunctions_comp {C D : Type u} [CommRing C] [CommRing D]
    {W : Scheme.{u}} (f : W ⟶ Spec (.of D)) (k : C →+* D) :
    onFunctions (f ≫ Spec.map (CommRingCat.ofHom k)) = (onFunctions f).comp k := by
  change ((Scheme.ΓSpecIso (.of C)).inv ≫
      (f ≫ Spec.map (CommRingCat.ofHom k)).appTop).hom =
    ((CommRingCat.ofHom k) ≫ (Scheme.ΓSpecIso (.of D)).inv ≫ f.appTop).hom
  rw [Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]

private theorem onFunctions_injective {C : Type u} [CommRing C] {W : Scheme.{u}} :
    Function.Injective (onFunctions (C := C) (W := W)) := by
  intro f g h
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

private def fromFunctions {C : Type u} [CommRing C] {W : Scheme.{u}}
    (k : C →+* Γ(W, ⊤)) : W ⟶ Spec (.of C) :=
  (ΓSpec.adjunction.homEquiv W (op (CommRingCat.of C))) (CommRingCat.ofHom k).op

@[simp] private theorem onFunctions_fromFunctions {C : Type u} [CommRing C]
    {W : Scheme.{u}} (k : C →+* Γ(W, ⊤)) : onFunctions (fromFunctions k) = k :=
  congrArg CommRingCat.Hom.hom (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom k))

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The spectrum of the `n`-fold tensor power is the `n`-fold fibre product
of `Spec B` over `Spec A`, specified by its projection maps. -/
theorem existsUnique_specLift {n : ℕ} {W : Scheme.{u}} (g : W ⟶ Spec (.of A))
    (f : Fin n → (W ⟶ Spec (.of B))) (hf : ∀ i, f i ≫ baseMap A B = g) :
    ∃! l : W ⟶ Spec (.of (Terms A B n)),
      l ≫ baseMap A (Terms A B n) = g ∧
        ∀ i : Fin n, l ≫ specMap (coordinate (A := A) (B := B) i) = f i := by
  let : Algebra A Γ(W, ⊤) := (onFunctions g).toAlgebra
  let a (i : Fin n) : B →ₐ[A] Γ(W, ⊤) :=
    { toRingHom := onFunctions (f i)
      commutes' := fun x => by
        have h := congrArg onFunctions (hf i)
        rw [onFunctions_comp] at h
        exact RingHom.congr_fun h x }
  let k := liftCoordinates a
  let l : W ⟶ Spec (.of (Terms A B n)) := fromFunctions k.toRingHom
  refine ⟨l, ⟨?_, fun i => ?_⟩, fun l' hl' => ?_⟩
  · apply onFunctions_injective
    rw [onFunctions_comp, onFunctions_fromFunctions]
    ext x
    exact k.commutes x
  · apply onFunctions_injective
    rw [onFunctions_comp, onFunctions_fromFunctions]
    exact congrArg AlgHom.toRingHom (liftCoordinates_coordinate a i)
  · let k' : Terms A B n →ₐ[A] Γ(W, ⊤) :=
      { toRingHom := onFunctions l'
        commutes' := fun x => by
          have h := congrArg onFunctions hl'.1
          rw [onFunctions_comp] at h
          exact RingHom.congr_fun h x }
    have hk : k' = k := (existsUnique_liftCoordinates a).unique
      (fun i => by
        apply AlgHom.coe_ringHom_injective
        have h := congrArg onFunctions (hl'.2 i)
        rw [onFunctions_comp] at h
        exact h)
      (liftCoordinates_coordinate a)
    apply onFunctions_injective
    rw [onFunctions_fromFunctions]
    exact congrArg AlgHom.toRingHom hk

/-- Deleting a coordinate induces the corresponding unit insertion on
global functions, and composes each projection with the matching index. -/
theorem specInsertOne_coordinate {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    specMap (insertOneAlg (A := A) (B := B) i) ≫ specMap (coordinate j) =
      specMap (coordinate (i.succAbove j)) := by
  rw [← Spec.map_comp]
  change specMap ((insertOneAlg (A := A) (B := B) i).comp (coordinate j)) = _
  rw [insertOneAlg_coordinate]

variable (A B)

/-- The affine cone presenting an iterated fibre product over `Spec A`. -/
def tensorCone (n : ℕ) : WidePullbackCone (fun _ : Fin n => baseMap A B) :=
  WidePullbackCone.mk (baseMap A (Terms A B n))
    (fun i => specMap (coordinate (A := A) (B := B) i)) (fun i => specMap_over (coordinate i))

/-- The tensor-power cone is a wide pullback in schemes. -/
def tensorConeIsLimit (n : ℕ) : IsLimit (tensorCone A B n) := by
  let lift := fun (s : WidePullbackCone (fun _ : Fin n => baseMap A B)) =>
    (existsUnique_specLift s.base s.π s.condition).exists.choose
  have hl (s : WidePullbackCone (fun _ : Fin n => baseMap A B)) :
      lift s ≫ (tensorCone A B n).base = s.base ∧
        ∀ i, lift s ≫ (tensorCone A B n).π i = s.π i :=
    (existsUnique_specLift s.base s.π s.condition).exists.choose_spec
  exact WidePullbackCone.IsLimit.mk _ lift (fun s => (hl s).1) (fun s => (hl s).2)
    (fun s l hb hπ => (existsUnique_specLift s.base s.π s.condition).unique ⟨hb, hπ⟩ (hl s))

/-- Splitting off the first factor of a tensor power presents the
corresponding spectrum as a pullback along `Spec B → Spec A`. -/
theorem tensorHead_isPullback (n : ℕ) :
    IsPullback (specMap (coordinate (A := A) (B := B) (0 : Fin (n + 1))))
      (specMap (insertOneAlg (A := A) (B := B) (0 : Fin (n + 1))))
      (baseMap A B) (baseMap A (Terms A B n)) := by
  let p (i : Fin (n + 1)) := specMap (coordinate (A := A) (B := B) i)
  let d := specMap (insertOneAlg (A := A) (B := B) (0 : Fin (n + 1)))
  let e (i : Fin n) := specMap (coordinate (A := A) (B := B) i)
  have hbase := specMap_over (insertOneAlg (A := A) (B := B) (0 : Fin (n + 1)))
  have hd (i : Fin n) : d ≫ e i = p i.succ := specInsertOne_coordinate 0 i
  let c := PullbackCone.mk (p 0) d ((specMap_over (coordinate 0)).trans hbase.symm)
  apply (IsPullback.of_isLimit (c := c))
  refine PullbackCone.isLimitAux' c (fun s => ?_)
  let a : Fin (n + 1) → (s.pt ⟶ Spec (.of B)) :=
    Fin.cases s.fst (fun i => s.snd ≫ e i)
  have ha (i : Fin (n + 1)) : a i ≫ baseMap A B = s.snd ≫ baseMap A (Terms A B n) := by
    cases i using Fin.cases with
    | zero => exact s.condition
    | succ i =>
        change (s.snd ≫ e i) ≫ baseMap A B = _
        rw [Category.assoc, show e i ≫ baseMap A B = _ from specMap_over (coordinate i)]
  have hex := existsUnique_specLift (s.snd ≫ baseMap A (Terms A B n)) a ha
  let l := hex.exists.choose
  have hl := hex.exists.choose_spec
  refine ⟨l, hl.2 0, ?_, fun {m} hm₁ hm₂ => ?_⟩
  · apply WidePullbackCone.IsLimit.hom_ext (tensorConeIsLimit A B n)
    · change (l ≫ d) ≫ baseMap A (Terms A B n) = s.snd ≫ baseMap A (Terms A B n)
      rw [Category.assoc, hbase]
      exact hl.1
    · intro i
      change (l ≫ d) ≫ e i = s.snd ≫ e i
      rw [Category.assoc, hd]
      exact hl.2 i.succ
  · refine hex.unique ?_ hl
    change m ≫ p 0 = s.fst at hm₁
    change m ≫ d = s.snd at hm₂
    constructor
    · rw [← hbase, ← Category.assoc, hm₂]
    · intro i
      cases i using Fin.cases with
      | zero => exact hm₁
      | succ i =>
          change m ≫ p i.succ = s.snd ≫ e i
          rw [← hd, ← Category.assoc, hm₂]

/-- Tensor powers of an étale algebra give étale affine schemes over the base. -/
theorem tensorBase_etale [Etale (baseMap A B)] : ∀ n : ℕ, Etale (baseMap A (Terms A B n))
  | 0 => by
      let a : Fin 0 → (Spec (.of A) ⟶ Spec (.of B)) := Fin.elim0
      have hex := existsUnique_specLift (𝟙 (Spec (.of A))) a (fun i => i.elim0)
      obtain ⟨l, hl, _⟩ := hex
      let p := baseMap A (Terms A B 0)
      have hl0 : l ≫ p = 𝟙 _ := hl.1
      have hl' : p ≫ l = 𝟙 _ := by
        apply WidePullbackCone.IsLimit.hom_ext (tensorConeIsLimit A B 0)
        · change (p ≫ l) ≫ p = 𝟙 _ ≫ p
          rw [Category.assoc, hl0, Category.comp_id, Category.id_comp]
        · intro i
          exact i.elim0
      have : IsIso p := ⟨⟨l, hl', hl0⟩⟩
      exact inferInstanceAs (Etale p)
  | n + 1 => by
      let d := specMap (insertOneAlg (A := A) (B := B) (0 : Fin (n + 1)))
      have : Etale d := MorphismProperty.of_isPullback (P := @Etale)
        (tensorHead_isPullback A B n) inferInstance
      have : Etale (baseMap A (Terms A B n)) := tensorBase_etale n
      rw [← specMap_over (insertOneAlg (A := A) (B := B) (0 : Fin (n + 1)))]
      exact inferInstanceAs (Etale (d ≫ baseMap A (Terms A B n)))

abbrev Sections (n : ℕ) := Γ(Spec (.of (Terms A B n)), ⊤)

/-- The differential on global functions given by the alternating sum
of pullbacks along the coordinate projections. -/
def sectionsD (n : ℕ) : Sections A B n →+ Sections A B (n + 1) :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) •
    (specMap (insertOneAlg (A := A) (B := B) i)).appTop.hom.toAddMonoidHom

private def sectionsEquiv (n : ℕ) : Sections A B n ≃+ Terms A B n :=
  (Scheme.ΓSpecIso (.of (Terms A B n))).commRingCatIsoToRingEquiv.toAddEquiv

private theorem sectionsD_comm (n : ℕ) :
    (d A B n).toAddMonoidHom.comp (sectionsEquiv A B n).toAddMonoidHom =
      (sectionsEquiv A B (n + 1)).toAddMonoidHom.comp (sectionsD A B n) := by
  ext x
  change d A B n (sectionsEquiv A B n x) = sectionsEquiv A B (n + 1) (sectionsD A B n x)
  rw [d_apply]
  simp only [sectionsD, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (insertOneAlg (A := A) (B := B) i).toRingHom)) x).symm

/-- The sequence of global functions on the affine Čech terms of a
surjective étale morphism of affine spectra is exact. -/
theorem sections_exact [Etale (baseMap A B)] [Surjective (baseMap A B)] (n : ℕ) :
    Function.Exact (sectionsD A B n) (sectionsD A B (n + 1)) := by
  have : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).mp
      ⟨inferInstance, inferInstance⟩)
  exact (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (sectionsD A B n) (sectionsD A B (n + 1)) (d A B n).toAddMonoidHom
    (d A B (n + 1)).toAddMonoidHom (sectionsEquiv A B n).toAddMonoidHom
    (sectionsEquiv A B (n + 1)).toAddMonoidHom (sectionsEquiv A B (n + 2)).toAddMonoidHom
    (sectionsD_comm A B n) (sectionsD_comm A B (n + 1))
    (sectionsEquiv A B n).surjective (sectionsEquiv A B (n + 1)).bijective
    (sectionsEquiv A B (n + 2)).injective).mpr (PhilipponAmitsur.exact n)

end PhilipponAmitsur

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short exact sequences obtained by cutting an augmented resolution
at its cycles. `cycles 0` is the object being resolved. -/
structure Resolution where
  terms : ℕ → C
  cycles : ℕ → C
  inclusion (j : ℕ) : cycles (j + 1) ⟶ terms j
  projection (j : ℕ) : terms j ⟶ cycles j
  zero (j : ℕ) : inclusion j ≫ projection j = 0
  shortExact (j : ℕ) : (ShortComplex.mk (inclusion j) (projection j) (zero j)).ShortExact

namespace Resolution

section OfExact

variable {A : ℕ → C} (d : ∀ k, A (k + 1) ⟶ A k)
  (dd : ∀ k, d (k + 1) ≫ d k = 0)

private def cyclesOfExact : ℕ → C
  | 0 => A 0
  | k + 1 => kernel (d k)

private def projectionOfExact : ∀ k, A (k + 1) ⟶ cyclesOfExact d k
  | 0 => d 0
  | k + 1 => kernel.lift (d k) (d (k + 1)) (dd k)

private lemma inclusion_projection_zero (k : ℕ) :
    kernel.ι (d k) ≫ projectionOfExact d dd k = 0 := by
  cases k with
  | zero => exact kernel.condition _
  | succ k =>
      apply (cancel_mono (kernel.ι (d k))).mp
      simp only [Category.assoc, projectionOfExact, kernel.lift_ι, kernel.condition, zero_comp]

/-- Cut an exact augmented chain into short exact sequences of cycles. The
first object `A 0` is the target of the epimorphic augmentation `d 0`. -/
def ofExact [Epi (d 0)]
    (h : ∀ k, (ShortComplex.mk (d (k + 1)) (d k) (dd k)).Exact) : Resolution (C := C) where
  terms k := A (k + 1)
  cycles := cyclesOfExact d
  inclusion k := kernel.ι (d k)
  projection := projectionOfExact d dd
  zero := inclusion_projection_zero d dd
  shortExact k := by
    cases k with
    | zero =>
        refine ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (d 0)) inferInstance ?_
        exact ‹Epi (d 0)›
    | succ k =>
        have he := (ShortComplex.exact_iff_epi_kernel_lift _).mp (h k)
        refine ShortComplex.ShortExact.mk' ?_ inferInstance he
        apply ShortComplex.exact_of_f_is_kernel
        refine KernelFork.IsLimit.ofι' (kernel.ι (d (k + 1)))
          (inclusion_projection_zero d dd (k + 1)) (fun s hs => ?_)
        have hs' : s ≫ d (k + 1) = 0 := by
          have hh := congrArg (fun z => z ≫ kernel.ι (d k)) hs
          simpa only [projectionOfExact, Category.assoc, kernel.lift_ι, zero_comp] using hh
        exact ⟨kernel.lift (d (k + 1)) s hs', kernel.lift_ι _ _ _⟩

@[simp] theorem ofExact_differential [Epi (d 0)]
    (h : ∀ k, (ShortComplex.mk (d (k + 1)) (d k) (dd k)).Exact) (j : ℕ) :
    (ofExact d dd h).projection (j + 1) ≫ (ofExact d dd h).inclusion j = d (j + 1) :=
  kernel.lift_ι _ _ _

end OfExact

variable (R : Resolution (C := C)) (F : C)

/-- The differential obtained by applying `Hom(-, F)` to the resolution. -/
def cochain (j : ℕ) (f : R.terms j ⟶ F) : R.terms (j + 1) ⟶ F :=
  R.projection (j + 1) ≫ R.inclusion j ≫ f

variable [HasExt.{w} C]

private theorem boundary_eq_zero_of_cochain_exact (j : ℕ)
    (h : Function.Exact (R.cochain F j) (R.cochain F (j + 1)))
    (a : Ext (R.cycles (j + 1)) F 0) :
    (R.shortExact j).extClass.comp a (rfl : 1 + 0 = 1) = 0 := by
  let b := Ext.addEquiv₀ a
  have hb : R.cochain F (j + 1) (R.projection (j + 1) ≫ b) = 0 := by
    unfold cochain
    rw [← Category.assoc (R.inclusion (j + 1)), R.zero, zero_comp, comp_zero]
  obtain ⟨c, hc⟩ := (h _).mp hb
  have : Epi (R.projection (j + 1)) := (R.shortExact (j + 1)).epi_g
  have he : R.inclusion j ≫ c = b := (cancel_epi (R.projection (j + 1))).mp hc
  have ha : a = (Ext.mk₀ (R.inclusion j)).comp (Ext.mk₀ c) (rfl : 0 + 0 = 0) := by
    rw [Ext.mk₀_comp_mk₀, he, Ext.mk₀_addEquiv₀_apply]
  rw [ha]
  exact (R.shortExact j).extClass_comp_assoc (Ext.mk₀ c)

/-- A positive-degree class that vanishes on the first term of the
resolution is zero if all smaller positive degrees vanish on its terms
and its complex of sections is exact in positive degrees. -/
theorem eq_zero_of_restrict_zero (n j : ℕ)
    (hvanish : ∀ k q, 0 < q → q ≤ n → Subsingleton (Ext (R.terms k) F q))
    (hcochain : ∀ k, Function.Exact (R.cochain F k) (R.cochain F (k + 1)))
    (x : Ext (R.cycles j) F (n + 1))
    (hx : (Ext.mk₀ (R.projection j)).comp x (zero_add (n + 1)) = 0) : x = 0 := by
  induction n generalizing j with
  | zero =>
      obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ (R.shortExact j) F x hx
        (rfl : 1 + 0 = 0 + 1)
      exact ha.symm.trans (R.boundary_eq_zero_of_cochain_exact F j (hcochain j) a)
  | succ n ih =>
      obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ (R.shortExact j) F x hx
        (Nat.add_comm 1 (n + 1))
      have hz : (Ext.mk₀ (R.projection (j + 1))).comp a (zero_add (n + 1)) = 0 :=
        (hvanish (j + 1) (n + 1) (Nat.succ_pos n) le_rfl).elim _ _
      have ha' := ih (j + 1)
        (fun k q hp hq => hvanish k q hp (hq.trans (Nat.le_succ n))) a hz
      rw [← ha, ha', Ext.comp_zero]

end Resolution

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v
variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) (W : C)

/-- The image of the covering arrow on the represented set at `W`. -/
abbrev Range := Set.range (fun a : W ⟶ V => a ≫ f)

/-- The arrow on represented sets with codomain restricted to its image. -/
def toRange : (W ⟶ V) ⟶ Range f W :=
  TypeCat.ofHom fun a => ⟨a ≫ f, a, rfl⟩

theorem toRange_surjective : Function.Surjective (toRange f W) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨a, rfl⟩

/-- The image augmentation of the evaluated nerve is split. -/
def rangeExtraDegeneracy :
    (Arrow.mk (toRange f W)).augmentedCechNerve.ExtraDegeneracy := by
  let h := toRange_surjective f W
  let s : SplitEpi (toRange f W) :=
    { section_ := TypeCat.ofHom (Function.surjInv h)
      id := by
        apply ConcreteCategory.hom_ext
        intro a
        exact Function.rightInverse_surjInv h a }
  exact Arrow.AugmentedCechNerve.extraDegeneracy _ s

variable [HasFiniteLimits C]

local notation "N" => Arrow.cechNerve (Arrow.mk f)
local notation "M" => Arrow.cechNerve (Arrow.mk (toRange f W))

private theorem nerve_map_π {n m : SimplexCategoryᵒᵖ} (k : n ⟶ m)
    (i : Fin (m.unop.len + 1)) :
    (N).map k ≫ WidePullback.π (fun _ => f) i =
      WidePullback.π (fun _ => f) (k.unop.toOrderHom i) :=
  WidePullback.lift_π _ _ _ _ _

private theorem nerve_map_base {n m : SimplexCategoryᵒᵖ} (k : n ⟶ m) :
    (N).map k ≫ WidePullback.base (fun _ : Fin (m.unop.len + 1) => f) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) :=
  WidePullback.lift_base _ _ _ _

/-- The zero-simplices of the Čech nerve are the source of the arrow. -/
def nerveZeroIso : (N).obj (op ⦋0⦌) ≅ V where
  hom := WidePullback.π (fun _ : Fin 1 => f) 0
  inv := WidePullback.lift f (fun _ : Fin 1 => 𝟙 V) (by simp)
  hom_inv_id := by
    change WidePullback.π (fun _ : Fin 1 => f) 0 ≫
      WidePullback.lift f (fun _ : Fin 1 => 𝟙 V) (by simp) =
      𝟙 (widePullback U (fun _ : Fin 1 => V) (fun _ => f))
    apply WidePullback.hom_ext
    · intro i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow (fun _ : Fin 1 => f) 0
  inv_hom_id := WidePullback.lift_π (fun _ : Fin 1 => f) _ _ _ 0

theorem nerveZeroIso_hom_comp :
    (nerveZeroIso f).hom ≫ f = (Arrow.mk f).augmentedCechNerve.hom.app (op ⦋0⦌) :=
  WidePullback.π_arrow (fun _ : Fin 1 => f) 0

private def toRangeBase (n : SimplexCategoryᵒᵖ) :
    (W ⟶ (N).obj n) ⟶ Range f W :=
  TypeCat.ofHom fun a => ⟨a ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) => f),
    a ≫ WidePullback.π (fun _ : Fin (n.unop.len + 1) => f) 0, by simp [Category.assoc]⟩

private def liftToRange (n : SimplexCategoryᵒᵖ) :
    (W ⟶ (N).obj n) ⟶ (M).obj n :=
  WidePullback.lift (toRangeBase f W n)
    (fun i => TypeCat.ofHom fun a => a ≫ WidePullback.π (fun _ => f) i) (by
      intro i
      apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      change (a ≫ WidePullback.π _ i) ≫ f = a ≫ WidePullback.base _
      rw [Category.assoc]
      exact congrArg (a ≫ ·) (WidePullback.π_arrow (fun _ => f) i))

private def liftFromRange (n : SimplexCategoryᵒᵖ) : (M).obj n ⟶ (W ⟶ (N).obj n) :=
  TypeCat.ofHom fun a => WidePullback.lift
    (WidePullback.base (fun _ : Fin (n.unop.len + 1) => toRange f W) a).val
    (fun i => WidePullback.π (fun _ => toRange f W) i a) (fun i => by
      have h := ConcreteCategory.congr_hom
        (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => toRange f W) i) a
      exact congrArg Subtype.val h)

private theorem liftToRange_π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1))
    (a : W ⟶ (N).obj n) :
    WidePullback.π (fun _ => toRange f W) i (liftToRange f W n a) =
      a ≫ WidePullback.π (fun _ => f) i :=
  ConcreteCategory.congr_hom (WidePullback.lift_π (fun _ => toRange f W) _ _ _ i) a

private theorem liftToRange_base (n : SimplexCategoryᵒᵖ) (a : W ⟶ (N).obj n) :
    WidePullback.base (fun _ : Fin (n.unop.len + 1) => toRange f W) (liftToRange f W n a) =
      toRangeBase f W n a :=
  ConcreteCategory.congr_hom
    (WidePullback.lift_base (fun _ : Fin (n.unop.len + 1) => toRange f W) _ _ _) a

private theorem liftFromRange_π (n : SimplexCategoryᵒᵖ) (a : (M).obj n)
    (i : Fin (n.unop.len + 1)) :
    liftFromRange f W n a ≫ WidePullback.π (fun _ => f) i =
      WidePullback.π (fun _ => toRange f W) i a :=
  WidePullback.lift_π _ _ _ _ i

private theorem liftFromRange_base (n : SimplexCategoryᵒᵖ) (a : (M).obj n) :
    liftFromRange f W n a ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) =
      (WidePullback.base (fun _ : Fin (n.unop.len + 1) => toRange f W) a).val :=
  WidePullback.lift_base _ _ _ _

/-- The Čech nerve evaluated at a test object is the Čech nerve of the
map to the image on the represented sets. -/
def evaluatedNerveIso : N ⋙ coyoneda.obj (op W) ≅ M :=
  NatIso.ofComponents (fun n =>
    { hom := liftToRange f W n
      inv := liftFromRange f W n
      hom_inv_id := by
        ext a
        change liftFromRange f W n (liftToRange f W n a) = a
        apply WidePullback.hom_ext
        · intro i
          change liftFromRange f W n (liftToRange f W n a) ≫
            WidePullback.π (fun _ => f) i = a ≫ WidePullback.π (fun _ => f) i
          rw [liftFromRange_π, liftToRange_π]
        · change liftFromRange f W n (liftToRange f W n a) ≫
            WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) = _
          rw [liftFromRange_base, liftToRange_base]
          rfl
      inv_hom_id := by
        apply WidePullback.hom_ext
        · intro i
          apply ConcreteCategory.hom_ext
          intro a
          change WidePullback.π (fun _ => toRange f W) i
            (liftToRange f W n (liftFromRange f W n a)) = _
          rw [liftToRange_π, liftFromRange_π]
          rfl
        · apply ConcreteCategory.hom_ext
          intro a
          apply Subtype.ext
          change (WidePullback.base (fun _ => toRange f W)
            (liftToRange f W n (liftFromRange f W n a))).val = _
          rw [liftToRange_base]
          exact liftFromRange_base f W n a }) (by
    intro n m k
    apply WidePullback.hom_ext
    · intro i
      apply ConcreteCategory.hom_ext
      intro a
      change WidePullback.π (fun _ => toRange f W) i
        (liftToRange f W m (a ≫ (N).map k)) =
        ((M).map k ≫ WidePullback.π (fun _ => toRange f W) i) (liftToRange f W n a)
      rw [liftToRange_π, Category.assoc, nerve_map_π, nerve_map_π]
      exact (liftToRange_π f W n (k.unop.toOrderHom i) a).symm
    · apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      change (WidePullback.base (fun _ => toRange f W)
        (liftToRange f W m (a ≫ (N).map k))).val =
        (((M).map k ≫ WidePullback.base (fun _ => toRange f W)) (liftToRange f W n a)).val
      rw [liftToRange_base, nerve_map_base]
      refine Eq.trans ?_ (congrArg Subtype.val (liftToRange_base f W n a)).symm
      change (a ≫ (N).map k) ≫ WidePullback.base _ = a ≫ WidePullback.base _
      rw [Category.assoc]
      exact congrArg (a ≫ ·) (nerve_map_base f k))

/-- The split image augmentation maps to the full evaluated augmentation by
the identity on its represented tuples and inclusion on its target. -/
def evaluatedImageComparison : (Arrow.mk (toRange f W)).augmentedCechNerve ⟶
    (SimplicialObject.Augmented.whiskeringObj C (Type v) (coyoneda.obj (op W))).obj
      (Arrow.mk f).augmentedCechNerve where
  left := (evaluatedNerveIso f W).inv
  right := TypeCat.ofHom Subtype.val
  w := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    exact liftFromRange_base f W n a

instance : IsIso (evaluatedImageComparison f W).left := by
  change IsIso (evaluatedNerveIso f W).inv
  infer_instance

instance : Mono (evaluatedImageComparison f W).right := by
  apply (mono_iff_injective _).mpr
  exact Subtype.val_injective

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

open AlgebraicTopology.AlternatingFaceMapComplex

/-- The augmented chain numbered with the augmentation target in degree zero. -/
def augmentedTerm (X : SimplicialObject.Augmented A) (i : ℕ) : A :=
  match i with
  | 0 => X.right
  | n + 1 => X.left.obj (op ⦋n⦌)

def augmentedD (X : SimplicialObject.Augmented A) (i : ℕ) :
    augmentedTerm X (i + 1) ⟶ augmentedTerm X i :=
  match i with
  | 0 => X.hom.app (op ⦋0⦌)
  | n + 1 => (obj X.left).d (n + 1) n

theorem augmentedD_comp (X : SimplicialObject.Augmented A) (n : ℕ) :
    augmentedD X (n + 1) ≫ augmentedD X n = 0 := by
  cases n with
  | zero =>
      have h := (ε.app X).comm 1 0
      simpa [augmentedD] using h.symm
  | succ n => exact (obj X.left).d_comp_d _ _ _

/-- The consecutive pair of differentials at an augmented Čech term. -/
def augmentedSC (X : SimplicialObject.Augmented A) (n : ℕ) : ShortComplex A :=
  ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n)

/-- Additive functors carry the augmented alternating face maps to the
augmented alternating face maps of the image simplicial object. -/
def mapAugmentedSC {B : Type*} [Category* B] [Abelian B] (G : A ⥤ B) [G.Additive]
    (X : SimplicialObject.Augmented A) (n : ℕ) :
    (augmentedSC X n).map G ≅
      augmentedSC ((SimplicialObject.Augmented.whiskeringObj A B G).obj X) n := by
  cases n <;> refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  all_goals
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ShortComplex.map_f,
      ShortComplex.map_g, augmentedSC, augmentedD,
      obj_d_eq, Functor.map_sum, Functor.map_zsmul]
    first
    | rfl
    | simp [SimplicialObject.Augmented.whiskeringObj]

private def augmentedMap {X Y : SimplicialObject.Augmented A} (φ : X ⟶ Y) (i : ℕ) :
    augmentedTerm X i ⟶ augmentedTerm Y i :=
  match i with
  | 0 => φ.right
  | n + 1 => φ.left.app (op ⦋n⦌)

private theorem augmentedMap_comm {X Y : SimplicialObject.Augmented A} (φ : X ⟶ Y) (n : ℕ) :
    augmentedMap φ (n + 1) ≫ augmentedD Y n = augmentedD X n ≫ augmentedMap φ n := by
  cases n with
  | zero => exact SimplicialObject.Augmented.w₀ φ
  | succ n =>
      exact ((AlgebraicTopology.alternatingFaceMapComplex A).map φ.left).comm (n + 1) n

/-- An isomorphism on simplices preserves and reflects exactness of the
augmented complexes when the map on augmentation targets is a monomorphism. -/
theorem augmented_exact_iff_of_iso_of_mono {X Y : SimplicialObject.Augmented A}
    (φ : X ⟶ Y) [IsIso φ.left] [Mono φ.right] (n : ℕ) :
    (ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n)).Exact ↔
      (ShortComplex.mk (augmentedD Y (n + 1)) (augmentedD Y n) (augmentedD_comp Y n)).Exact := by
  let ψ : ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n) ⟶
      ShortComplex.mk (augmentedD Y (n + 1)) (augmentedD Y n) (augmentedD_comp Y n) :=
    { τ₁ := augmentedMap φ (n + 2)
      τ₂ := augmentedMap φ (n + 1)
      τ₃ := augmentedMap φ n
      comm₁₂ := augmentedMap_comm φ (n + 1)
      comm₂₃ := augmentedMap_comm φ n }
  have : Epi ψ.τ₁ := by
    change Epi (φ.left.app (op ⦋n + 1⦌))
    infer_instance
  have : IsIso ψ.τ₂ := by
    change IsIso (φ.left.app (op ⦋n⦌))
    infer_instance
  have : Mono ψ.τ₃ := by
    cases n with
    | zero => exact ‹Mono φ.right›
    | succ n =>
        change Mono (φ.left.app (op ⦋n⦌))
        infer_instance
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ

/-- An extra degeneracy splits the augmented alternating face map complex
and implies exactness in every degree of its simplicial terms. -/
theorem augmented_exact_of_extraDegeneracy {X : SimplicialObject.Augmented A}
    (e : X.ExtraDegeneracy) (n : ℕ) :
    (ShortComplex.mk (augmentedD X (n + 1)) (augmentedD X n) (augmentedD_comp X n)).Exact := by
  cases n with
  | zero =>
      let S := ShortComplex.mk (augmentedD X 1) (augmentedD X 0) (augmentedD_comp X 0)
      apply (S.exact_iff_epi_kernel_lift).mpr
      let p := kernel.lift S.g S.f S.zero
      have h : e.s 0 ≫ S.f = 𝟙 _ - S.g ≫ e.s' := by
        let a : X.left.obj (op ⦋0⦌) ⟶ X.right := X.hom.app (op ⦋0⦌)
        change e.s 0 ≫ (obj X.left).d 1 0 = 𝟙 (X.left.obj (op ⦋0⦌)) - a ≫ e.s'
        rw [obj_d_eq, Fin.sum_univ_two]
        simp [comp_add, sub_eq_add_neg, a, e.s_comp_δ₀, e.s₀_comp_δ₁]
      have hp : (kernel.ι S.g ≫ e.s 0) ≫ p = 𝟙 _ := by
        apply (cancel_mono (kernel.ι S.g)).mp
        simp only [Category.assoc, p, kernel.lift_ι, h, comp_sub, Category.comp_id,
          kernel.condition_assoc, zero_comp, sub_zero, Category.id_comp]
      exact epi_of_epi_fac hp
  | succ n =>
      let K := obj X.left
      let h := e.homotopyEquiv
      have : QuasiIso h.hom := h.quasiIso_hom
      have hexact : K.ExactAt (n + 1) := by
        apply (exactAt_iff_of_quasiIsoAt h.hom (n + 1)).mpr
        apply HomologicalComplex.ExactAt.of_isZero
        exact HomologicalComplex.isZero_single_obj_X _ 0 _ _ (Nat.succ_ne_zero n)
      have hprev : (ComplexShape.down ℕ).prev (n + 1) = n + 2 := by
        apply ComplexShape.prev_eq'
        rfl
      have hnext : (ComplexShape.down ℕ).next (n + 1) = n := by
        apply ComplexShape.next_eq'
        rfl
      exact (K.exactAt_iff' (n + 2) (n + 1) n hprev hnext).mp hexact

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite


namespace PhilipponSheafCohomology

universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]


private def freePresheaf :=
  (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free

/-- The free abelian sheaf on the representable presheaf of an object. -/
def freeOn : C ⥤ (Sheaf J AddCommGrpCat.{v}) :=
  yoneda ⋙ freePresheaf (C := C) ⋙ presheafToSheaf J _

private def freeAdjunction :
    (freePresheaf (C := C) ⋙ presheafToSheaf J _) ⊣
      (sheafToPresheaf J AddCommGrpCat.{v} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} (Type v)).obj (forget AddCommGrpCat.{v})) :=
  (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J _)

/-- Maps out of a free representable sheaf correspond to sections. -/
def representedSections (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    ((freeOn J).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((freeAdjunction J).homEquiv (yoneda.obj U) F).trans yonedaEquiv

theorem representedSections_restrict {F : Sheaf J AddCommGrpCat.{v}} {U V : C}
    (f : V ⟶ U) (x : (freeOn J).obj U ⟶ F) :
    representedSections J F V ((freeOn J).map f ≫ x) =
      F.obj.map f.op (representedSections J F U x) := by
  unfold representedSections
  change yonedaEquiv ((freeAdjunction J).homEquiv _ _
    ((freePresheaf ⋙ presheafToSheaf J _).map (yoneda.map f) ≫ x)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

/-- The augmentation of the free abelian Čech complex of a covering
arrow is an epimorphism of sheaves. -/
theorem freeOn_map_epi_of_cover [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {U V : C} (f : V ⟶ U) (h : Sieve.generate (.singleton f) ∈ J U) :
    Epi ((freeOn J).map f) := by
  constructor
  intro F a b hab
  apply (representedSections J F U).injective
  have hs := Presheaf.isSheaf_comp_of_isSheaf J F.obj (forget AddCommGrpCat) F.property
  have hs' := (Presieve.isSheafFor_iff_generate (.singleton f)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ h)
  apply hs'.isSeparatedFor.ext
  rintro _ _ ⟨⟩
  change F.obj.map f.op (representedSections J F U a) =
    F.obj.map f.op (representedSections J F U b)
  rw [← representedSections_restrict, ← representedSections_restrict, hab]

private theorem representedSections_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C)
    (x : (freeOn J).obj U ⟶ F) :
    representedSections J G U (x ≫ f) =
      f.hom.app (op U) (representedSections J F U x) := by
  unfold representedSections
  change yonedaEquiv ((freeAdjunction J).homEquiv _ _ (x ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

/-- The representability equivalence is additive in the sheaf morphism. -/
def representedSectionsAddEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    ((freeOn J).obj U ⟶ F) ≃+ F.obj.obj (op U) :=
  { representedSections J F U with
    map_add' := by
      intro a b
      change representedSections J F U (a + b) =
        representedSections J F U a + representedSections J F U b
      let G := (freeOn J).obj U
      have happ (c : G ⟶ F) : representedSections J F U c =
          c.hom.app (op U) (representedSections J G U (𝟙 G)) := by
        rw [← representedSections_map, Category.id_comp]
      rw [happ (a + b), happ a, happ b]
      rfl }

private def constantIntegers : Sheaf J AddCommGrpCat.{v} :=
  (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))

private def constantSections {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) :
    (constantIntegers J ⟶ F) ≃ F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

private theorem constantSections_map {T : C} (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (x : constantIntegers J ⟶ F) :
    constantSections J hT G (x ≫ f) = f.hom.app (op T) (constantSections J hT F x) := by
  unfold constantSections
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _ (x ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private def freeTerminalIso {T : C} (hT : IsTerminal T) :
    (freeOn J).obj T ≅ constantIntegers J := by
  let Y := (freeOn J).obj T
  let Z := constantIntegers J
  let a : Y ⟶ Z := (representedSections J Z T).symm (constantSections J hT Z (𝟙 Z))
  let b : Z ⟶ Y := (constantSections J hT Y).symm (representedSections J Y T (𝟙 Y))
  have ha : representedSections J Z T a = constantSections J hT Z (𝟙 Z) :=
    (representedSections J Z T).apply_symm_apply _
  have hb : constantSections J hT Y b = representedSections J Y T (𝟙 Y) :=
    (constantSections J hT Y).apply_symm_apply _
  refine ⟨a, b, ?_, ?_⟩
  · apply (representedSections J Y T).injective
    rw [representedSections_map, ha, ← constantSections_map, Category.id_comp, hb]
  · apply (constantSections J hT Z).injective
    rw [constantSections_map, hb, ← representedSections_map, Category.id_comp, ha]

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Evaluation of the cohomology presheaf at a terminal object gives the
same cohomology as taking Ext from the constant sheaf of integers. -/
def terminalComparison {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) (q : ℕ) :
    F.H q ≃+ F.H' q T := by
  let e := freeTerminalIso J hT
  refine
    { toFun := fun x => (Ext.mk₀ e.hom).comp x (zero_add q)
      invFun := fun x => (Ext.mk₀ e.inv).comp x (zero_add q)
      map_add' := fun x y => Ext.comp_add _ _ _ _
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  · intro x
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

private theorem restrict_apply {F : Sheaf J AddCommGrpCat.{v}} {U V : C} (f : V ⟶ U) (q : ℕ) (x : F.H' q U) :
    (F.cohomologyPresheaf q).map f.op x =
      (Ext.mk₀ ((freeOn J).map f)).comp x (zero_add q) := rfl

/-- If all abelian sheaves glue arbitrary tuples of sections over a finite
family, cohomology on its target is the product of cohomology on its members. -/
theorem class_eq_zero_of_disjoint_gluing {ι : Type*} [Fintype ι] {U : C} {V : ι → C}
    (f : ∀ i, V i ⟶ U)
    (h : ∀ F : Sheaf J AddCommGrpCat.{v}, Function.Bijective
      (fun x : F.obj.obj (op U) => fun i => F.obj.map (f i).op x))
    (F : Sheaf J AddCommGrpCat.{v}) (q : ℕ) (x : F.H' q U)
    (hx : ∀ i, (F.cohomologyPresheaf q).map (f i).op x = 0) : x = 0 := by
  classical
  let c : Cofan (fun i => (freeOn J).obj (V i)) :=
    Cofan.mk ((freeOn J).obj U) (fun i => (freeOn J).map (f i))
  let d (t : Cofan (fun i => (freeOn J).obj (V i))) : c.pt ⟶ t.pt :=
    (representedSections J t.pt U).symm
      ((Equiv.ofBijective _ (h t.pt)).symm
        (fun i => representedSections J t.pt (V i) (t.inj i)))
  have hd (t : Cofan (fun i => (freeOn J).obj (V i))) (i : ι) :
      c.inj i ≫ d t = t.inj i := by
    apply (representedSections J t.pt (V i)).injective
    change representedSections J t.pt (V i) ((freeOn J).map (f i) ≫ d t) = _
    rw [representedSections_restrict]
    change ((Equiv.ofBijective _ (h t.pt)) (representedSections J t.pt U (d t))) i = _
    simp only [d, Equiv.apply_symm_apply]
  let hc : IsColimit c := Cofan.IsColimit.mk c d hd (fun t m hm => by
    apply (representedSections J t.pt U).injective
    apply (h t.pt).injective
    funext i
    have hi := congrArg (representedSections J t.pt (V i)) ((hm i).trans (hd t i).symm)
    change representedSections J t.pt (V i) ((freeOn J).map (f i) ≫ m) =
      representedSections J t.pt (V i) ((freeOn J).map (f i) ≫ d t) at hi
    simpa only [representedSections_restrict] using hi)
  let e := Ext.biproductAddEquiv (biconeIsBilimitOfColimitCoconeOfIsColimit hc) F q
  apply e.injective
  rw [map_zero]
  funext i
  exact hx i

private theorem restrict_boundary {F G : Sheaf J AddCommGrpCat.{v}} {U V : C} (f : V ⟶ U)
    (n : ℕ) (δ : Ext G F 1) (y : Ext ((freeOn J).obj U) G n) :
    (Ext.mk₀ ((freeOn J).map f)).comp (y.comp δ rfl) (zero_add (n + 1)) =
      ((Ext.mk₀ ((freeOn J).map f)).comp y (zero_add n)).comp δ rfl := by
  symm
  exact Ext.comp_assoc _ _ _ (zero_add n) (rfl : n + 1 = _) (by simp)

private theorem evaluate_mk₀ {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) :
    (Ext.addEquiv₀ (Ext.mk₀ f) : F ⟶ G) = f :=
  Ext.addEquiv₀.apply_symm_apply f

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Every individual positive-degree sheaf cohomology class restricts to zero
on a covering sieve. The proof uses dimension shifting and local lifting along
an epimorphism for the last shift in degree zero. -/
theorem cohomologyClass_locally_zero (q : ℕ) (F : Sheaf J AddCommGrpCat.{v}) (U : C) (x : F.H' (q + 1) U) :
    Presheaf.equalizerSieve (F := F.cohomologyPresheaf (q + 1)) (X := op U) x 0 ∈ J U := by
  induction q generalizing F U with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ ((freeOn J).obj U) hS x
      (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
    let t := representedSections J S.X₃ U (Ext.addEquiv₀ y)
    letI : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v} S.g).mpr hS.epi_g
    apply J.superset_covering _ (Presheaf.imageSieve_mem J S.g.hom (U := op U) t)
    intro V f hf
    obtain ⟨s, hs⟩ := hf
    let z := Ext.mk₀ ((representedSections J S.X₂ V).symm s)
    have hz : z.comp (Ext.mk₀ S.g) (add_zero 0) =
        (Ext.mk₀ ((freeOn J).map f)).comp y (zero_add 0) := by
      apply Ext.addEquiv₀.injective
      apply (representedSections J S.X₃ V).injective
      let y₀ := Ext.addEquiv₀ y
      have hy0 : Ext.mk₀ y₀ = y := Ext.mk₀_addEquiv₀_apply y
      rw [← hy0]
      simp only [z, Ext.mk₀_comp_mk₀, evaluate_mk₀ J]
      rw [representedSections_restrict, representedSections_map, Equiv.apply_symm_apply]
      exact hs
    change (F.cohomologyPresheaf 1).map f.op x = (F.cohomologyPresheaf 1).map f.op 0
    rw [map_zero, restrict_apply, ← hy, restrict_boundary, ← hz]
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
      Ext.comp_zero]
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ ((freeOn J).obj U) hS x
      (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
    apply J.superset_covering _ (ih S.X₃ U y)
    intro V f hf
    change (S.X₃.cohomologyPresheaf (n + 1)).map f.op y =
      (S.X₃.cohomologyPresheaf (n + 1)).map f.op 0 at hf
    rw [map_zero, restrict_apply] at hf
    change (F.cohomologyPresheaf (n + 1 + 1)).map f.op x =
      (F.cohomologyPresheaf (n + 1 + 1)).map f.op 0
    rw [map_zero, restrict_apply, ← hy, restrict_boundary, hf, Ext.zero_comp]

end PhilipponSheafCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme

universe u
variable {X : Scheme.{u}} {U : X.Etale}

private theorem contains_arrow_over_point (S : Sieve U)
    (hS : S ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (V : X.Etale) (f : V ⟶ U), S f ∧ x ∈ Set.range f.left := by
  let ι := Σ V : X.Etale, {f : V ⟶ U // S f}
  let V : ι → X.Etale := fun i => i.1
  let f (i : ι) : V i ⟶ U := i.2.val
  have he : Sieve.ofArrows V f = S := by
    apply le_antisymm
    · apply (Sieve.generate_le_iff _ _).mpr
      rintro _ _ ⟨i⟩
      exact i.2.property
    · intro W g hg
      exact Sieve.ofArrows_mk V f (⟨W, ⟨g, hg⟩⟩ : ι)
  have hcover := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp (he.symm ▸ hS)
  have hx : x ∈ ⋃ i : ι, Set.range (f i).left := hcover.symm ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨V i, f i, i.2.property, hi⟩

private theorem contains_affine_arrow_over_point (S : Sieve U)
    (hS : S ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (V : X.Etale) (f : V ⟶ U), S f ∧ IsAffine V.left ∧ x ∈ Set.range f.left := by
  obtain ⟨V, f, hf, y, rfl⟩ := contains_arrow_over_point S hS x
  obtain ⟨i, z, rfl⟩ := V.left.affineCover.exists_eq y
  let W : X.Etale := Scheme.Etale.mk ((V.left.affineCover.f i) ≫ V.hom)
  let g : W ⟶ V := MorphismProperty.Over.homMk (V.left.affineCover.f i) rfl trivial
  refine ⟨W, g ≫ f, S.downward_closed hf g, ?_, ⟨z, rfl⟩⟩
  change IsAffine (V.left.affineCover.X i)
  infer_instance

/-- A covering sieve on a quasi-compact object in the small étale site
has a finite refinement consisting of affine objects. -/
theorem exists_finite_affine_refinement [CompactSpace U.left] (S : Sieve U)
    (hS : S ∈ X.smallEtaleTopology U) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, S (f i)) ∧ (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U := by
  classical
  choose V f hf ha hr using fun x : U.left => contains_affine_arrow_over_point S hS x
  have hopen (x : U.left) : IsOpen (Set.range (f x).left) :=
    (f x).left.isOpenMap.isOpen_range
  have hcover : (Set.univ : Set U.left) ⊆ ⋃ x : U.left, Set.range (f x).left :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hr x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨s, inferInstance, fun i => V i.val, fun i => f i.val,
    fun i => hf i.val, fun i => ha i.val, ?_⟩
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩

end AlgebraicGeometry.Scheme

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- An individual higher étale cohomology class on a quasi-compact object is
killed by a finite family of affine étale charts. -/
theorem exists_finite_affine_cover_killing_class {X : Scheme.{u}} (U : X.Etale)
    [CompactSpace U.left] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (x : F.H' (q + 1) U) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      ∀ i, (F.cohomologyPresheaf (q + 1)).map (f i).op x = 0 := by
  let S := Presheaf.equalizerSieve (F := F.cohomologyPresheaf (q + 1)) (X := op U) x 0
  have hS : S ∈ X.smallEtaleTopology U :=
    PhilipponSheafCohomology.cohomologyClass_locally_zero X.smallEtaleTopology q F U x
  obtain ⟨ι, hι, V, f, hf, hV, hcover⟩ := Scheme.exists_finite_affine_refinement S hS
  refine ⟨ι, hι, V, f, hV, hcover, fun i => ?_⟩
  have hi := hf i
  change (F.cohomologyPresheaf (q + 1)).map (f i).op x =
    (F.cohomologyPresheaf (q + 1)).map (f i).op 0 at hi
  simpa only [map_zero] using hi

/-- A higher cohomology class on a quasi-compact scheme restricts to zero on
the members of some finite affine étale covering of the scheme. -/
theorem exists_finite_affine_cover_killing_global_class (X : Scheme.{u}) [CompactSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H (q + 1)) :
    let T := Scheme.Etale.mk (𝟙 X)
    let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _
      Over.mkIdTerminal
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (f : ∀ i, V i ⟶ T),
      (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology T ∧
      ∀ i, (F.cohomologyPresheaf (q + 1)).map (f i).op
        (PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology hT F (q + 1) x) = 0 := by
  intro T hT
  let : CompactSpace T.left := ‹CompactSpace X›
  exact Scheme.exists_finite_affine_cover_killing_class T F q
    (PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology hT F (q + 1) x)

private theorem subsingleton_sections_of_isEmpty {X : Scheme.{u}} {W : X.Etale}
    (hW : IsEmpty W.left) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Subsingleton (F.obj.obj (op W)) := by
  let V : Empty → X.Etale := Empty.elim
  let p (i : Empty) : V i ⟶ W := Empty.elim i
  have hCover : Sieve.ofArrows V p ∈ X.smallEtaleTopology W :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mpr (Set.ext fun x => (hW.false x).elim)
  have hBot : (⊥ : Sieve W) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Empty.elim i
  refine ⟨fun x y => ?_⟩
  have hs := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp hs _ hBot).isSeparatedFor.ext
  intro _ _ h
  exact h.elim

/-- A single surjective affine étale morphism suffices to kill any given
higher cohomology class on a quasi-compact object of the small étale site. -/
theorem exists_surjective_affine_arrow_killing_class {X : Scheme.{u}} (U : X.Etale)
    [CompactSpace U.left] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (x : F.H' (q + 1) U) :
    ∃ (E : X.Etale) (g : E ⟶ U), IsAffine E.left ∧ Function.Surjective g.left ∧
      (F.cohomologyPresheaf (q + 1)).map g.op x = 0 := by
  obtain ⟨ι, hι, V, f, ha, hcover, hx⟩ := exists_finite_affine_cover_killing_class U F q x
  let : Fintype ι := hι
  let Y := fun i => (V i).left
  let : ∀ i, IsAffine (Y i) := ha
  let p : (∐ Y) ⟶ U.left := Sigma.desc (fun i => (f i).left)
  let t : (∐ Y) ⟶ X := Sigma.desc (fun i => (V i).hom)
  let : Etale t := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover Y)).mpr
    intro i
    change Etale (Sigma.ι Y i ≫ t)
    rw [Sigma.ι_desc]
    exact (V i).prop
  let E : X.Etale := Scheme.Etale.mk t
  let g : E ⟶ U := MorphismProperty.Over.homMk p (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι Y i ≫ p ≫ U.hom = Sigma.ι Y i ≫ t
    rw [← Category.assoc]
    unfold p t
    rw [Sigma.ι_desc, Sigma.ι_desc]
    exact MorphismProperty.Over.w (f i)) trivial
  let j (i : ι) : V i ⟶ E :=
    MorphismProperty.Over.homMk (Sigma.ι Y i) (Sigma.ι_desc _ _) trivial
  have hj (i : ι) : j i ≫ g = f i := by
    apply MorphismProperty.Over.Hom.ext
    exact Sigma.ι_desc _ _
  refine ⟨E, g, inferInstanceAs (IsAffine (∐ Y)), ?_, ?_⟩
  · intro u
    have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hcover
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (h.symm ▸ (Set.mem_univ u))
    refine ⟨Sigma.ι Y i y, ?_⟩
    change (Sigma.ι Y i ≫ p) y = u
    rw [Sigma.ι_desc]
    exact hy
  · have hCover : Sieve.ofArrows V j ∈ X.smallEtaleTopology E := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
      ext y
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      let oc := sigmaOpenCover Y
      obtain ⟨z, hz⟩ := oc.covers y
      exact ⟨oc.idx y, z, hz⟩
    refine PhilipponSheafCohomology.class_eq_zero_of_disjoint_gluing X.smallEtaleTopology j
      ?_ F (q + 1) ((F.cohomologyPresheaf (q + 1)).map g.op x) ?_
    · intro G
      let P := G.obj ⋙ CategoryTheory.forget AddCommGrpCat
      have hP := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology G.obj
        (CategoryTheory.forget AddCommGrpCat) G.property
      have hSheaf : Presieve.IsSheafFor P (.ofArrows V j) :=
        (Presieve.isSheafFor_iff_generate (.ofArrows V j)).mpr
          ((isSheaf_iff_isSheaf_of_type _ _).mp hP _ hCover)
      constructor
      · intro s s' h
        apply hSheaf.isSeparatedFor.ext
        rintro _ _ ⟨i⟩
        exact congrFun h i
      · intro s
        have hCompat : Presieve.Arrows.Compatible P j s := by
          intro i k W a b h
          have hh : a.left ≫ Sigma.ι Y i = b.left ≫ Sigma.ι Y k :=
            congrArg (fun t : W ⟶ E => t.left) h
          by_cases he : i = k
          · subst k
            have hSame : a = b := MorphismProperty.Over.Hom.ext
              ((cancel_mono (Sigma.ι Y i)).mp hh)
            rw [hSame]
          · exact (subsingleton_sections_of_isEmpty
              (isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ he) G).elim _ _
        obtain ⟨s', hs', _⟩ :=
          (Presieve.isSheafFor_arrows_iff (π := j) (P := P)).mp hSheaf s hCompat
        exact ⟨s', funext hs'⟩
    · intro i
      let P := F.cohomologyPresheaf (q + 1)
      change P.map (j i).op (P.map g.op x) = 0
      rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, hj]
      exact hx i

end AlgebraicGeometry.Scheme

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v w
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {U V : C} (f : V ⟶ U)

private theorem evaluated_free_exact (W : C) (n : ℕ) :
    (augmentedSC ((SimplicialObject.Augmented.whiskeringObj C AddCommGrpCat.{v}
      (coyoneda.obj (op W) ⋙ AddCommGrpCat.free)).obj (Arrow.mk f).augmentedCechNerve) n).Exact := by
  let G := SimplicialObject.Augmented.whiskeringObj (Type v) AddCommGrpCat.{v} AddCommGrpCat.free
  let φ := G.map (evaluatedImageComparison f W)
  have : IsIso φ.left := by
    change IsIso (((SimplicialObject.whiskering (Type v) AddCommGrpCat.{v}).obj
      AddCommGrpCat.free).map (evaluatedImageComparison f W).left)
    infer_instance
  have : Mono φ.right := by
    change Mono (AddCommGrpCat.free.map (evaluatedImageComparison f W).right)
    infer_instance
  exact (augmented_exact_iff_of_iso_of_mono φ n).mp
    (augmented_exact_of_extraDegeneracy ((rangeExtraDegeneracy f W).map AddCommGrpCat.free) n)

private theorem exact_of_evaluation {D : Type*} [Category* D]
    (S : ShortComplex (D ⥤ AddCommGrpCat.{v}))
    (h : ∀ W : D, (S.map ((evaluation D AddCommGrpCat.{v}).obj W)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro W
  let G := (evaluation D AddCommGrpCat.{v}).obj W
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (h W))
    ((ShortComplex.homologyFunctorIso G).app S).symm

private def representedFree : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free

private theorem represented_free_exact (n : ℕ) :
    (augmentedSC ((SimplicialObject.Augmented.whiskeringObj C (Cᵒᵖ ⥤ AddCommGrpCat.{v})
      (representedFree (C := C))).obj (Arrow.mk f).augmentedCechNerve) n).Exact := by
  let N := (Arrow.mk f).augmentedCechNerve
  let F := SimplicialObject.Augmented.whiskeringObj C (Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (representedFree (C := C))
  apply exact_of_evaluation
  intro W
  exact (ShortComplex.exact_iff_of_iso
    (mapAugmentedSC ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj W) (F.obj N) n)).mpr
    (evaluated_free_exact f W.unop n)

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- The Čech nerve mapped to free abelian sheaves. -/
abbrev freeSheafNerve : SimplicialObject.Augmented (Sheaf J AddCommGrpCat.{v}) :=
  (SimplicialObject.Augmented.whiskeringObj C (Sheaf J AddCommGrpCat.{v})
    (PhilipponSheafCohomology.freeOn J)).obj (Arrow.mk f).augmentedCechNerve

/-- The augmented Čech nerve with free abelian sheaf coefficients is exact
at all the terms attached to simplices. -/
theorem free_sheaf_nerve_exact (n : ℕ) : (augmentedSC (freeSheafNerve f J) n).Exact := by
  let N := (Arrow.mk f).augmentedCechNerve
  let F := SimplicialObject.Augmented.whiskeringObj C (Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (representedFree (C := C))
  let G := presheafToSheaf J AddCommGrpCat.{v}
  exact ShortComplex.exact_of_iso (mapAugmentedSC G (F.obj N) n)
    ((represented_free_exact f n).map G)

private theorem freeSheafNerve_aug_eq :
    augmentedD (freeSheafNerve f J) 0 =
      (PhilipponSheafCohomology.freeOn J).map (nerveZeroIso f).hom ≫
        (PhilipponSheafCohomology.freeOn J).map f := by
  rw [← Functor.map_comp, nerveZeroIso_hom_comp]
  simp [freeSheafNerve, augmentedD, SimplicialObject.Augmented.whiskeringObj]

variable [J.HasSheafCompose (forget AddCommGrpCat.{v})]

private theorem free_sheaf_augmentation_epi
    (h : Sieve.generate (Presieve.singleton f) ∈ J U) :
    Epi (augmentedD (freeSheafNerve f J) 0) := by
  have := PhilipponSheafCohomology.freeOn_map_epi_of_cover J f h
  rw [freeSheafNerve_aug_eq]
  infer_instance

/-- The sequence of short exact sequences of cycles in the free abelian
Čech resolution of a covering arrow. -/
def freeCechResolution (h : Sieve.generate (Presieve.singleton f) ∈ J U) :
    Resolution (C := Sheaf J AddCommGrpCat.{v}) := by
  let : Epi (augmentedD (freeSheafNerve f J) 0) := free_sheaf_augmentation_epi f J h
  exact Resolution.ofExact _ (augmentedD_comp _) (free_sheaf_nerve_exact f J)

/-- The usual alternating differential on sections over the Čech nerve. -/
def sectionCechD (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) :
    F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))) →+
      F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j + 1⦌))) :=
  ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) •
    (F.obj.map ((Arrow.mk f).cechNerve.δ i).op).hom

private def cechSectionsEquiv (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) :
    ((freeCechResolution f J h).terms j ⟶ F) ≃+
      F.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))) :=
  PhilipponSheafCohomology.representedSectionsAddEquiv J F _

private theorem cechSectionsEquiv_cochain (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ) (s : (freeCechResolution f J h).terms j ⟶ F) :
    cechSectionsEquiv f J h F (j + 1) ((freeCechResolution f J h).cochain F j s) =
      sectionCechD f J F j (cechSectionsEquiv f J h F j s) := by
  have hd : (freeCechResolution f J h).projection (j + 1) ≫ (freeCechResolution f J h).inclusion j =
      ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (PhilipponSheafCohomology.freeOn J).map ((Arrow.mk f).cechNerve.δ i) := by
    unfold freeCechResolution
    rw [Resolution.ofExact_differential, augmentedD,
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    rfl
  rw [Resolution.cochain, ← Category.assoc, hd, sum_comp]
  simp only [zsmul_comp, map_sum, map_zsmul, sectionCechD, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact PhilipponSheafCohomology.representedSections_restrict J ((Arrow.mk f).cechNerve.δ i) s

private theorem cochain_exact_of_sections_exact (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ)
    (he : Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1))) :
    Function.Exact ((freeCechResolution f J h).cochain F j)
      ((freeCechResolution f J h).cochain F (j + 1)) := by
  intro y
  constructor
  · intro hy
    have hy' : sectionCechD f J F (j + 1) (cechSectionsEquiv f J h F (j + 1) y) = 0 := by
      rw [← cechSectionsEquiv_cochain, hy, map_zero]
    obtain ⟨x, hx⟩ := (he _).mp hy'
    refine ⟨(cechSectionsEquiv f J h F j).symm x, (cechSectionsEquiv f J h F (j + 1)).injective ?_⟩
    rw [cechSectionsEquiv_cochain, AddEquiv.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    apply (cechSectionsEquiv f J h F (j + 2)).injective
    rw [cechSectionsEquiv_cochain, cechSectionsEquiv_cochain, map_zero]
    exact (he _).mpr ⟨_, rfl⟩

/-- Exactness of Čech cochains and the vanishing of lower positive degrees
on the Čech terms imply that restriction along the cover is injective. -/
theorem class_eq_zero_of_cech_exact [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (h : Sieve.generate (Presieve.singleton f) ∈ J U)
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (hvanish : ∀ j q, 0 < q → q ≤ n →
      Subsingleton (F.H' q ((Arrow.mk f).cechNerve.obj (op ⦋j⦌))))
    (hcochain : ∀ j, Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1)))
    (x : F.H' (n + 1) U) (hx : (F.cohomologyPresheaf (n + 1)).map f.op x = 0) : x = 0 := by
  let R := freeCechResolution f J h
  apply R.eq_zero_of_restrict_zero F n 0 hvanish
    (fun j => cochain_exact_of_sections_exact f J h F j (hcochain j)) x
  change (Ext.mk₀ (augmentedD (freeSheafNerve f J) 0)).comp x (zero_add (n + 1)) = 0
  change (Ext.mk₀ ((PhilipponSheafCohomology.freeOn J).map f)).comp x (zero_add (n + 1)) = 0 at hx
  rw [freeSheafNerve_aug_eq, ← Ext.mk₀_comp_mk₀_assoc, hx, Ext.comp_zero]

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponAffineEtaleTorsorCocycle (baseMap specMap specMap_over)
open scoped Simplicial


namespace PhilipponAmitsur

universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Etale (baseMap A B)] {X : Scheme.{u}} (g : Spec (.of A) ⟶ X) [Etale g]

abbrev siteBase : X.Etale := Scheme.Etale.mk g
abbrev siteSource : X.Etale := Scheme.Etale.mk (baseMap A B ≫ g)

/-- A morphism of affine spectra viewed in the small étale site of `X`. -/
def siteArrow : siteSource (B := B) g ⟶ siteBase g :=
  MorphismProperty.Over.homMk (baseMap A B) rfl trivial

/-- An affine tensor power, viewed as an object of the small étale site. -/
abbrev siteTensor (n : ℕ) : X.Etale := by
  let : Etale (baseMap A (Terms A B n)) := tensorBase_etale A B n
  exact Scheme.Etale.mk (baseMap A (Terms A B n) ≫ g)

private def siteTensorBase (n : ℕ) : siteTensor (B := B) g n ⟶ siteBase g :=
  MorphismProperty.Over.homMk (baseMap A (Terms A B n)) rfl trivial

private def siteTensorProjection {n : ℕ} (i : Fin n) :
    siteTensor (B := B) g n ⟶ siteSource (B := B) g :=
  MorphismProperty.Over.homMk (specMap (coordinate i))
    (by
      change specMap (coordinate i) ≫ baseMap A B ≫ g = baseMap A (Terms A B n) ≫ g
      rw [← Category.assoc, specMap_over]) trivial

private def siteTensorCone (n : ℕ) : WidePullbackCone (fun _ : Fin n => siteArrow (B := B) g) :=
  WidePullbackCone.mk (siteTensorBase (B := B) g n) (siteTensorProjection (B := B) g)
    (fun i => MorphismProperty.Over.Hom.ext (specMap_over (coordinate i)))

private def siteTensorConeIsLimit (n : ℕ) : IsLimit (siteTensorCone (B := B) g n) := by
  let h (s : WidePullbackCone (fun _ : Fin n => siteArrow (B := B) g)) :=
    existsUnique_specLift s.base.left (fun i => (s.π i).left) (fun i =>
      congrArg (fun a : s.pt ⟶ siteBase g => a.left) (s.condition i))
  let lift (s : WidePullbackCone (fun _ : Fin n => siteArrow (B := B) g)) :
      s.pt ⟶ siteTensor (B := B) g n :=
    MorphismProperty.Over.homMk (h s).exists.choose (by
      change (h s).exists.choose ≫ baseMap A (Terms A B n) ≫ g = s.pt.hom
      rw [← Category.assoc, (h s).exists.choose_spec.1]
      exact MorphismProperty.Over.w s.base) trivial
  refine WidePullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    exact MorphismProperty.Over.Hom.ext (h s).exists.choose_spec.1
  · intro s i
    exact MorphismProperty.Over.Hom.ext ((h s).exists.choose_spec.2 i)
  · intro s m hb hp
    apply MorphismProperty.Over.Hom.ext
    refine (h s).unique ?_ (h s).exists.choose_spec
    exact ⟨congrArg (fun a : s.pt ⟶ siteBase g => a.left) hb, fun i =>
      congrArg (fun a : s.pt ⟶ siteSource (B := B) g => a.left) (hp i)⟩

/-- The simplices of the actual small étale Čech nerve are the spectra of
the repeated tensor powers of the affine covering algebra. -/
def siteNerveTensorIso (j : ℕ) :
    (Arrow.mk (siteArrow (B := B) g)).cechNerve.obj (op ⦋j⦌) ≅ siteTensor (B := B) g (j + 1) :=
  (limit.isLimit _).conePointUniqueUpToIso (siteTensorConeIsLimit (B := B) g (j + 1))

private theorem siteNerveTensorIso_base (j : ℕ) :
    (siteNerveTensorIso (B := B) g j).hom ≫ siteTensorBase (B := B) g (j + 1) =
      WidePullback.base (fun _ : Fin (j + 1) => siteArrow (B := B) g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ (siteTensorConeIsLimit (B := B) g _) none

private theorem siteNerveTensorIso_π (j : ℕ) (i : Fin (j + 1)) :
    (siteNerveTensorIso (B := B) g j).hom ≫ siteTensorProjection (B := B) g i =
      WidePullback.π (fun _ : Fin (j + 1) => siteArrow (B := B) g) i :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ (siteTensorConeIsLimit (B := B) g _) (some i)

/-- A coordinate deletion on tensor powers is an arrow of the small étale site. -/
def siteTensorDelete {n : ℕ} (i : Fin (n + 1)) :
    siteTensor (B := B) g (n + 1) ⟶ siteTensor (B := B) g n :=
  MorphismProperty.Over.homMk (specMap (insertOneAlg i))
    (by
      change specMap (insertOneAlg (A := A) (B := B) i) ≫ baseMap A (Terms A B n) ≫ g =
        baseMap A (Terms A B (n + 1)) ≫ g
      rw [← Category.assoc, specMap_over]) trivial

/-- The affine presentation carries each actual Čech face to deletion of
the matching coordinate in the affine tensor powers. -/
theorem siteNerveTensorIso_face (j : ℕ) (i : Fin (j + 2)) :
    (siteNerveTensorIso (B := B) g (j + 1)).hom ≫ siteTensorDelete (B := B) g i =
      (Arrow.mk (siteArrow (B := B) g)).cechNerve.δ i ≫ (siteNerveTensorIso (B := B) g j).hom := by
  let f := siteArrow (B := B) g
  let d := (Arrow.mk f).cechNerve.δ i
  apply WidePullbackCone.IsLimit.hom_ext (siteTensorConeIsLimit (B := B) g (j + 1))
  · have h : siteTensorDelete (B := B) g i ≫ siteTensorBase (B := B) g (j + 1) =
        siteTensorBase (B := B) g (j + 2) :=
      MorphismProperty.Over.Hom.ext (specMap_over (insertOneAlg i))
    change (_ ≫ _) ≫ siteTensorBase (B := B) g (j + 1) =
      (d ≫ _) ≫ siteTensorBase (B := B) g (j + 1)
    rw [Category.assoc, Category.assoc, h, siteNerveTensorIso_base, siteNerveTensorIso_base]
    exact (WidePullback.lift_base _ _ _ _).symm
  · intro k
    have h : siteTensorDelete (B := B) g i ≫ siteTensorProjection (B := B) g k =
        siteTensorProjection (B := B) g (i.succAbove k) :=
      MorphismProperty.Over.Hom.ext (specInsertOne_coordinate i k)
    change (_ ≫ _) ≫ siteTensorProjection (B := B) g k =
      (d ≫ _) ≫ siteTensorProjection (B := B) g k
    rw [Category.assoc, Category.assoc, h, siteNerveTensorIso_π, siteNerveTensorIso_π]
    symm
    change WidePullback.lift (WidePullback.base (fun _ : Fin (j + 2) => f))
        (fun k' : Fin (j + 1) => WidePullback.π (fun _ : Fin (j + 2) => f) (i.succAbove k'))
        (by simp) ≫ WidePullback.π (fun _ : Fin (j + 1) => f) k = _
    exact WidePullback.lift_π _ _ _ _ _

private def siteNerveSectionsEquiv (j : ℕ) :
    Sections A B (j + 1) ≃+
      (SmallEtaleAdditive.sheaf X).obj.obj
        (op ((Arrow.mk (siteArrow (B := B) g)).cechNerve.obj (op ⦋j⦌))) :=
  ((SmallEtaleAdditive.sheaf X).obj.mapIso
    (siteNerveTensorIso (B := B) g j).op).addCommGroupIsoToAddEquiv

private theorem siteNerveSectionsEquiv_d (j : ℕ) :
    (PhilipponCech.sectionCechD (siteArrow (B := B) g) X.smallEtaleTopology
      (SmallEtaleAdditive.sheaf X) j).comp (siteNerveSectionsEquiv (B := B) g j).toAddMonoidHom =
      (siteNerveSectionsEquiv (B := B) g (j + 1)).toAddMonoidHom.comp (sectionsD A B (j + 1)) := by
  ext x
  change PhilipponCech.sectionCechD (siteArrow (B := B) g) X.smallEtaleTopology
    (SmallEtaleAdditive.sheaf X) j (siteNerveSectionsEquiv (B := B) g j x) =
      siteNerveSectionsEquiv (B := B) g (j + 1) (sectionsD A B (j + 1) x)
  simp only [PhilipponCech.sectionCechD, sectionsD, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.zsmul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  let P := (SmallEtaleAdditive.sheaf X).obj
  have h := congrArg (fun k => P.map k.op) (siteNerveTensorIso_face (B := B) g j i)
  rw [op_comp, op_comp, P.map_comp, P.map_comp] at h
  exact (ConcreteCategory.congr_hom h x).symm

/-- On a surjective étale arrow of affine spectra, the actual Čech
complex of the additive sheaf is exact in positive degrees. -/
theorem site_sectionCechD_exact [Surjective (baseMap A B)] (j : ℕ) :
    Function.Exact (PhilipponCech.sectionCechD (siteArrow (B := B) g) X.smallEtaleTopology
      (SmallEtaleAdditive.sheaf X) j) (PhilipponCech.sectionCechD (siteArrow (B := B) g)
      X.smallEtaleTopology (SmallEtaleAdditive.sheaf X) (j + 1)) :=
  (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (sectionsD A B (j + 1)) (sectionsD A B (j + 2)) _ _
    (siteNerveSectionsEquiv (B := B) g j).toAddMonoidHom
    (siteNerveSectionsEquiv (B := B) g (j + 1)).toAddMonoidHom
    (siteNerveSectionsEquiv (B := B) g (j + 2)).toAddMonoidHom
    (siteNerveSectionsEquiv_d (B := B) g j) (siteNerveSectionsEquiv_d (B := B) g (j + 1))
    (siteNerveSectionsEquiv (B := B) g j).surjective
    (siteNerveSectionsEquiv (B := B) g (j + 1)).bijective
    (siteNerveSectionsEquiv (B := B) g (j + 2)).injective).mp (sections_exact A B (j + 1))

end PhilipponAmitsur

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace PhilipponCech

universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  (J : GrothendieckTopology C) {U V U' V' : C} {f : V ⟶ U} {g : V' ⟶ U'}

/-- Exactness of the section complex is invariant under an isomorphism of
Čech nerves. -/
theorem sectionCechD_exact_of_iso (e : (Arrow.mk f).cechNerve ≅ (Arrow.mk g).cechNerve)
    (F : Sheaf J AddCommGrpCat.{v}) (j : ℕ)
    (h : Function.Exact (sectionCechD g J F j) (sectionCechD g J F (j + 1))) :
    Function.Exact (sectionCechD f J F j) (sectionCechD f J F (j + 1)) := by
  let r (k : ℕ) := (F.obj.mapIso (e.app (op ⦋k⦌)).op).addCommGroupIsoToAddEquiv
  have hr (k : ℕ) : (sectionCechD f J F k).comp (r k).toAddMonoidHom =
      (r (k + 1)).toAddMonoidHom.comp (sectionCechD g J F k) := by
    ext x
    change sectionCechD f J F k (r k x) = r (k + 1) (sectionCechD g J F k x)
    simp only [sectionCechD, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply,
      map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hn := congrArg (fun a => F.obj.map a.op) (e.hom.naturality (SimplexCategory.δ i).op)
    rw [op_comp, op_comp, F.obj.map_comp, F.obj.map_comp] at hn
    exact ConcreteCategory.congr_hom hn x
  exact (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (sectionCechD g J F j) (sectionCechD g J F (j + 1)) _ _
    (r j).toAddMonoidHom (r (j + 1)).toAddMonoidHom (r (j + 2)).toAddMonoidHom
    (hr j) (hr (j + 1)) (r j).surjective (r (j + 1)).bijective (r (j + 2)).injective).mp h

end PhilipponCech

namespace AlgebraicGeometry.Scheme

universe u

open PhilipponAffineEtaleTorsorCocycle (baseMap)

/-- A surjective arrow between affine objects has affine Čech terms and
an exact additive Čech complex in positive degrees. -/
theorem affine_etale_nerve_and_sections_exact {X : Scheme.{u}} {U E : X.Etale}
    (f : E ⟶ U) (hU : IsAffine U.left) (hE : IsAffine E.left) (hsurj : Function.Surjective f.left) :
    (∀ j : ℕ, IsAffine ((Arrow.mk f).cechNerve.obj (op ⦋j⦌)).left) ∧
      ∀ j, Function.Exact (PhilipponCech.sectionCechD f X.smallEtaleTopology (SmallEtaleAdditive.sheaf X) j)
        (PhilipponCech.sectionCechD f X.smallEtaleTopology (SmallEtaleAdditive.sheaf X) (j + 1)) := by
  let A := Γ(U.left, ⊤)
  let B := Γ(E.left, ⊤)
  let : IsAffine U.left := hU
  let : IsAffine E.left := hE
  let : Algebra A B := f.left.appTop.hom.toAlgebra
  have hb : baseMap A B = Spec.map f.left.appTop := rfl
  let e := arrowIsoSpecΓOfIsAffine f.left
  have : Etale (baseMap A B) := by
    rw [hb]
    exact (MorphismProperty.arrow_mk_iso_iff @Etale e).mp (inferInstanceAs (Etale f.left))
  have : Surjective (baseMap A B) := by
    rw [hb]
    exact (MorphismProperty.arrow_mk_iso_iff @Surjective e).mp ⟨hsurj⟩
  let g : Spec (.of A) ⟶ X := U.left.isoSpec.inv ≫ U.hom
  have : Etale g := inferInstanceAs (Etale (U.left.isoSpec.inv ≫ U.hom))
  let uIso : U ≅ PhilipponAmitsur.siteBase g :=
    MorphismProperty.Over.isoMk U.left.isoSpec (by
      change U.left.isoSpec.hom ≫ U.left.isoSpec.inv ≫ U.hom = U.hom
      rw [Iso.hom_inv_id_assoc])
  let vIso : E ≅ PhilipponAmitsur.siteSource (B := B) g :=
    MorphismProperty.Over.isoMk E.left.isoSpec (by
      change E.left.isoSpec.hom ≫ baseMap A B ≫ U.left.isoSpec.inv ≫ U.hom = E.hom
      rw [hb, ← Category.assoc E.left.isoSpec.hom, Scheme.isoSpec_hom_naturality,
        Category.assoc, Iso.hom_inv_id_assoc]
      exact MorphismProperty.Over.w f)
  let φ : Arrow.mk f ≅ Arrow.mk (PhilipponAmitsur.siteArrow (B := B) g) :=
    Arrow.isoMk vIso uIso (MorphismProperty.Over.Hom.ext (by
      change E.left.isoSpec.hom ≫ baseMap A B = f.left ≫ U.left.isoSpec.hom
      rw [hb, Scheme.isoSpec_hom_naturality]))
  let ε := (SimplicialObject.cechNerve (C := X.Etale)).mapIso φ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · let s := ε.app (op ⦋j⦌) ≪≫ PhilipponAmitsur.siteNerveTensorIso (B := B) g j
    let i : ((Arrow.mk f).cechNerve.obj (op ⦋j⦌)).left ≅
        Spec (.of (PhilipponAmitsur.Terms A B (j + 1))) :=
      (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).mapIso s
    exact IsAffine.of_isIso i.hom
  · exact PhilipponCech.sectionCechD_exact_of_iso X.smallEtaleTopology ε (SmallEtaleAdditive.sheaf X) j
      (PhilipponAmitsur.site_sectionCechD_exact (B := B) g j)

/-- Affine vanishing follows from the geometry and the exact complex of
global functions of each surjective affine étale arrow. The induction runs
simultaneously on every affine object of the fixed small étale site. -/
theorem subsingleton_smallEtale_additive_of_affineCech (X : Scheme.{u})
    (h : ∀ {U E : X.Etale} (f : E ⟶ U), IsAffine U.left → IsAffine E.left →
      Function.Surjective f.left →
      (∀ j : ℕ, IsAffine ((Arrow.mk f).cechNerve.obj (op ⦋j⦌)).left) ∧
        ∀ j, Function.Exact (PhilipponCech.sectionCechD f X.smallEtaleTopology
          (SmallEtaleAdditive.sheaf X) j) (PhilipponCech.sectionCechD f X.smallEtaleTopology
          (SmallEtaleAdditive.sheaf X) (j + 1)))
    (q : ℕ) : ∀ U : X.Etale, IsAffine U.left →
      Subsingleton ((SmallEtaleAdditive.sheaf X).H' (q + 1) U) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro U hU
      let : IsAffine U.left := hU
      let F := SmallEtaleAdditive.sheaf X
      refine subsingleton_of_forall_eq 0 (fun x => ?_)
      obtain ⟨E, f, hE, hsurj, hx⟩ := exists_surjective_affine_arrow_killing_class U F q x
      obtain ⟨haff, hexact⟩ := h f hU hE hsurj
      have hcover : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology U := by
        rw [← Presieve.ofArrows_pUnit.{0} f]
        apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit => f)).mpr
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_iUnion.mpr ⟨PUnit.unit, hsurj x⟩
      apply PhilipponCech.class_eq_zero_of_cech_exact f X.smallEtaleTopology hcover F q
        ?_ hexact x hx
      intro j k hk hle
      cases k with
      | zero => exact (Nat.not_lt_zero _ hk).elim
      | succ k =>
          exact ih k (Nat.lt_of_succ_le hle) _ (haff j)

/-- The additive sheaf has no positive-degree étale cohomology on an affine scheme. -/
theorem smallEtale_additive_affine_vanishing (X : Scheme.{u}) [IsAffine X] (q : ℕ) :
    Subsingleton ((SmallEtaleAdditive.sheaf X).H (q + 1)) := by
  let T := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let e := PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology hT
    (SmallEtaleAdditive.sheaf X) (q + 1)
  have h := subsingleton_smallEtale_additive_of_affineCech X
    (fun f => affine_etale_nerve_and_sections_exact f) q T (inferInstanceAs (IsAffine X))
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

end AlgebraicGeometry.Scheme

end

open AlgebraicGeometry CategoryTheory

universe u

theorem solution (X : Scheme.{u}) [IsAffine X] (q : ℕ) :
    Subsingleton ((SmallEtaleAdditive.sheaf X).H (q + 1)) :=
  Scheme.smallEtale_additive_affine_vanishing X q
