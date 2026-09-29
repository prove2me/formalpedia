-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/17b138a0-dcd1-5c87-a873-34be5d9c92ff

import Mathlib
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

noncomputable section

namespace F6ea14e94

open Opposite DirectSum

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)

theorem app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  exact (congrFun (congrArg (fun k => (ConcreteCategory.hom k : Γ(M, U) → Γ(N, V))) h) s).symm

set_option linter.unusedVariables false in

def Sec (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules) (n : ℕ) : Type u := Γ(L.tensorPow n, ⊤)

scoped instance (n : ℕ) : AddCommGroup (Sec f L n) := inferInstanceAs (AddCommGroup Γ(L.tensorPow n, ⊤))

scoped instance (n : ℕ) : Module Γ(X, ⊤) (Sec f L n) := inferInstanceAs (Module Γ(X, ⊤) Γ(L.tensorPow n, ⊤))

def baseHom : S →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom

theorem baseHom_apply (s : S) : baseHom f s = GradedOAlgebra.baseScalar f s := rfl

scoped instance (n : ℕ) : Module S (Sec f L n) := Module.compHom (Sec f L n) (baseHom f)

theorem smul_def (n : ℕ) (s : S) (a : Sec f L n) :
    s • a = (GradedOAlgebra.baseScalar f s • (a : Γ(L.tensorPow n, ⊤)) : Γ(L.tensorPow n, ⊤)) := rfl

def mulSec {m n : ℕ} (a : Sec f L m) (b : Sec f L n) : Sec f L (m + n) :=
  ((tensorPowAdd L m n).hom.app ⊤ (tensorSections (L := L.tensorPow m) (M := L.tensorPow n) a b) :
    Γ(L.tensorPow (m + n), ⊤))

scoped instance : GradedMonoid.GMul (Sec f L) where
  mul a b := mulSec f L a b

scoped instance : GradedMonoid.GOne (Sec f L) where
  one := (unitSection ⊤ : Γ(𝟙_ X.Modules, ⊤))

theorem gmul_def {m n : ℕ} (a : Sec f L m) (b : Sec f L n) :
    GradedMonoid.GMul.mul a b =
      ((tensorPowAdd L m n).hom.app ⊤ (tensorSections (L := L.tensorPow m) (M := L.tensorPow n) a b) :
        Γ(L.tensorPow (m + n), ⊤)) := rfl

theorem gone_def : (GradedMonoid.GOne.one : Sec f L 0) = (unitSection ⊤ : Γ(𝟙_ X.Modules, ⊤)) := rfl

scoped instance : DirectSum.GNonUnitalNonAssocSemiring (Sec f L) where
  mul_zero a := by
    rw [gmul_def]
    erw [tensorSections_zero_right]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_zero
  zero_mul b := by
    rw [gmul_def]
    erw [tensorSections_zero_left]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_zero
  mul_add a b c := by
    rw [gmul_def, gmul_def, gmul_def]
    erw [tensorSections_add_right]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_add _ _
  add_mul a b c := by
    rw [gmul_def, gmul_def, gmul_def]
    erw [tensorSections_add_left]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_add _ _

section Frames

variable [Fact (Scheme.Modules.IsInvertible L)]

def frU (x : X) : X.Opens :=
  (IsInvertible.exists_isFrameOn_monoidalV2 (Fact.out : Scheme.Modules.IsInvertible L) x).choose

def frG (x : X) : Γ(L, frU L x) :=
  (IsInvertible.exists_isFrameOn_monoidalV2 (Fact.out : Scheme.Modules.IsInvertible L) x).choose_spec.choose

theorem mem_frU (x : X) : x ∈ frU L x :=
  (IsInvertible.exists_isFrameOn_monoidalV2 (Fact.out : Scheme.Modules.IsInvertible L) x).choose_spec.choose_spec.1

theorem isFrameOn_frG (x : X) : IsFrameOn (frG L x) (frU L x) :=
  (IsInvertible.exists_isFrameOn_monoidalV2 (Fact.out : Scheme.Modules.IsInvertible L) x).choose_spec.choose_spec.2

theorem iSup_frU : (⊤ : X.Opens) ≤ ⨆ x, frU L x :=
  fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, mem_frU L y⟩

def frG' (x : X) : Γ(L, frU L x) := L.presheaf.map (homOfLE (le_refl (frU L x))).op (frG L x)

def frE (x : X) (n : ℕ) : Γ(L.tensorPow n, frU L x) := tensorPowSection (frG' L x) n

theorem bijective_smul_frE (x : X) (n : ℕ) :
    Function.Bijective fun g : Γ(X, frU L x) => g • frE L x n := by
  have h := ((isFrameOn_frG L x).tensorPowSection_monoidalV2 n) (le_refl _) (le_refl _)
  have e : (L.tensorPow n).presheaf.map (homOfLE (le_refl (frU L x))).op (tensorPowSection (frG L x) n) =
      frE L x n := map_tensorPowSection _ _ _
  simpa only [e] using h

def resU (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) : Γ(L.tensorPow n, frU L x) :=
  (L.tensorPow n).presheaf.map (homOfLE (le_top : frU L x ≤ ⊤)).op c

def coef (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) : Γ(X, frU L x) :=
  (Equiv.ofBijective _ (bijective_smul_frE L x n)).symm (resU L x n c)

theorem coef_smul_frE (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) :
    coef L x n c • frE L x n = resU L x n c :=
  (Equiv.ofBijective _ (bijective_smul_frE L x n)).apply_symm_apply (resU L x n c)

theorem coef_eq_of_smul_eq (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) (a : Γ(X, frU L x))
    (h : a • frE L x n = resU L x n c) : coef L x n c = a :=
  (bijective_smul_frE L x n).1 ((coef_smul_frE L x n c).trans h.symm)

theorem coef_zero (x : X) (n : ℕ) : coef L x n 0 = 0 :=
  coef_eq_of_smul_eq L x n 0 0 (by rw [zero_smul, resU, map_zero])

theorem coef_add (x : X) (n : ℕ) (c d : Γ(L.tensorPow n, ⊤)) :
    coef L x n (c + d) = coef L x n c + coef L x n d :=
  coef_eq_of_smul_eq L x n _ _ (by rw [add_smul, coef_smul_frE, coef_smul_frE, resU, resU, resU, map_add])

theorem coef_smul (x : X) (n : ℕ) (r : Γ(X, ⊤)) (c : Γ(L.tensorPow n, ⊤)) :
    coef L x n (r • c) = X.presheaf.map (homOfLE (le_top : frU L x ≤ ⊤)).op r * coef L x n c :=
  coef_eq_of_smul_eq L x n _ _ (by rw [mul_smul, coef_smul_frE, resU, resU, Scheme.Modules.map_smul])

theorem coef_gmul (x : X) {m n : ℕ} (a : Sec f L m) (b : Sec f L n) :
    coef L x (m + n) (GradedMonoid.GMul.mul a b) = coef L x m a * coef L x n b := by
  apply coef_eq_of_smul_eq
  rw [resU, gmul_def, app_map, map_homOfLE_tensorSections]
  change (coef L x m a * coef L x n b) • frE L x (m + n) =
    (tensorPowAdd L m n).hom.app (frU L x) (tensorSections (resU L x m a) (resU L x n b))
  rw [← coef_smul_frE, ← coef_smul_frE, tensorSections_smul_left, tensorSections_smul_right, Hom.app_smul,
    Hom.app_smul, smul_smul]
  simp only [frE]
  rw [tensorPowAdd_hom_app_tensorSections_tensorPowSection]

theorem coef_gone (x : X) : coef L x 0 (GradedMonoid.GOne.one : Sec f L 0) = 1 :=
  coef_eq_of_smul_eq L x 0 _ _ (by
    rw [one_smul, gone_def, resU]
    exact (map_unitSection (homOfLE (le_top : frU L x ≤ ⊤))).symm)

theorem eq_zero_of_forall_coef_eq_zero {n : ℕ} (c : Γ(L.tensorPow n, ⊤)) (h : ∀ x, coef L x n c = 0) : c = 0 := by
  refine (AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible (L.tensorPow n)
    (frU L) ⊤ (fun _ => le_top) (iSup_frU L)).1 c 0 fun x => ?_
  rw [map_zero]
  change resU L x n c = 0
  rw [← coef_smul_frE, h x, zero_smul]

abbrev Tgt : Type u := ∀ x : X, Polynomial Γ(X, frU L x)

def coefHom (n : ℕ) : Sec f L n →+ Tgt L where
  toFun c := fun x => Polynomial.monomial n (coef L x n c)
  map_zero' := by funext x; simp only [Pi.zero_apply]; erw [coef_zero]; exact map_zero _
  map_add' c d := by funext x; simp only [Pi.add_apply]; erw [coef_add]; exact map_add _ _ _

theorem coefHom_apply (n : ℕ) (c : Sec f L n) (x : X) :
    coefHom f L n c x = Polynomial.monomial n (coef L x n c) := rfl

def F : (⨁ n, Sec f L n) →+ Tgt L := DirectSum.toAddMonoid (coefHom f L)

theorem F_of (n : ℕ) (c : Sec f L n) : F f L (DirectSum.of (Sec f L) n c) = coefHom f L n c :=
  DirectSum.toAddMonoid_of _ _ _

theorem F_mul (r s : ⨁ n, Sec f L n) : F f L (r * s) = F f L r * F f L s := by
  induction r using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add r₁ r₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]
  | of m a =>
    induction s using DirectSum.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add s₁ s₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
    | of n b =>
      rw [DirectSum.of_mul_of, F_of, F_of, F_of]
      funext x
      rw [Pi.mul_apply, coefHom_apply, coefHom_apply, coefHom_apply, Polynomial.monomial_mul_monomial,
        coef_gmul]

theorem F_one : F f L 1 = 1 := by
  rw [DirectSum.one_def, F_of]
  funext x
  rw [coefHom_apply, Pi.one_apply, coef_gone, Polynomial.monomial_zero_one]

theorem F_apply_coeff (r : ⨁ n, Sec f L n) (x : X) (n : ℕ) :
    (F f L r x).coeff n = coef L x n (r n) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of r]
  rw [map_sum, Finset.sum_apply, Polynomial.finsetSum_coeff]
  simp only [F_of, coefHom_apply, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' r.support n]
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h]
    exact (coef_zero L x n).symm

theorem F_injective : Function.Injective (F f L) := by
  intro r s h
  rw [← sub_eq_zero]
  have h0 : F f L (r - s) = 0 := by rw [map_sub, h, sub_self]
  ext n
  change ((r - s) n : Γ(L.tensorPow n, ⊤)) = 0
  apply eq_zero_of_forall_coef_eq_zero L
  intro x
  rw [← F_apply_coeff, h0, Pi.zero_apply, Polynomial.coeff_zero]

end Frames

end F6ea14e94
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.F6ea14e94"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.F6ea14e94"

noncomputable section

namespace F6ea14e94

open Opposite DirectSum

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
variable [Fact (Scheme.Modules.IsInvertible L)]

theorem one_mul' (a : ⨁ n, Sec f L n) : 1 * a = a :=
  F_injective f L (by rw [F_mul, F_one, one_mul])

theorem mul_one' (a : ⨁ n, Sec f L n) : a * 1 = a :=
  F_injective f L (by rw [F_mul, F_one, mul_one])

theorem mul_assoc' (a b c : ⨁ n, Sec f L n) : a * b * c = a * (b * c) :=
  F_injective f L (by rw [F_mul, F_mul, F_mul, F_mul, mul_assoc])

theorem mul_comm' (a b : ⨁ n, Sec f L n) : a * b = b * a :=
  F_injective f L (by rw [F_mul, F_mul, mul_comm])

scoped instance instCommRing : CommRing (⨁ n, Sec f L n) :=
  { (inferInstance : NonUnitalNonAssocSemiring (⨁ n, Sec f L n)),
    (inferInstance : AddCommGroup (⨁ n, Sec f L n)),
    (inferInstance : One (⨁ n, Sec f L n)) with
    one_mul := one_mul' f L
    mul_one := mul_one' f L
    mul_assoc := mul_assoc' f L
    mul_comm := mul_comm' f L }

def cS (s : S) : Tgt L := fun x =>
  Polynomial.C (X.presheaf.map (homOfLE (le_top : frU L x ≤ ⊤)).op (GradedOAlgebra.baseScalar f s))

theorem F_smul (s : S) (r : ⨁ n, Sec f L n) : F f L (s • r) = cS f L s * F f L r := by
  induction r using DirectSum.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | add r₁ r₂ h₁ h₂ => rw [smul_add, map_add, map_add, mul_add, h₁, h₂]
  | of n a =>
    rw [← DirectSum.of_smul, F_of, F_of]
    funext x
    rw [Pi.mul_apply, coefHom_apply, coefHom_apply, cS, Polynomial.C_mul_monomial, smul_def]
    erw [coef_smul]

theorem smul_mul' (s : S) (a b : ⨁ n, Sec f L n) : s • a * b = s • (a * b) :=
  F_injective f L (by rw [F_mul, F_smul, F_smul, F_mul, mul_assoc])

theorem mul_smul' (s : S) (a b : ⨁ n, Sec f L n) : a * s • b = s • (a * b) :=
  F_injective f L (by rw [F_mul, F_smul, F_smul, F_mul, mul_left_comm])

scoped instance instAlgebra : Algebra S (⨁ n, Sec f L n) := Algebra.ofModule (smul_mul' f L) (mul_smul' f L)

def 𝓡 (n : ℕ) : Submodule S (⨁ n, Sec f L n) where
  carrier := Set.range (DirectSum.of (Sec f L) n)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  smul_mem' := by
    rintro s _ ⟨a, rfl⟩
    exact ⟨s • a, DirectSum.of_smul _ _ _ _⟩

omit [Fact (Scheme.Modules.IsInvertible L)] in
theorem mem_𝓡_iff {n : ℕ} (r : ⨁ n, Sec f L n) : r ∈ 𝓡 f L n ↔ ∃ a, DirectSum.of (Sec f L) n a = r := Iff.rfl

scoped instance : SetLike.GradedMonoid (𝓡 f L) where
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨GradedMonoid.GMul.mul a b, (DirectSum.of_mul_of a b).symm⟩

def toPiece (n : ℕ) : Sec f L n →+ 𝓡 f L n where
  toFun a := ⟨DirectSum.of (Sec f L) n a, a, rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

def decomposeHom : (⨁ n, Sec f L n) →+ ⨁ n, 𝓡 f L n :=
  DirectSum.toAddMonoid fun n => (DirectSum.of (fun n => 𝓡 f L n) n).comp (toPiece f L n)

theorem decomposeHom_of (n : ℕ) (a : Sec f L n) :
    decomposeHom f L (DirectSum.of (Sec f L) n a) = DirectSum.of (fun n => 𝓡 f L n) n (toPiece f L n a) :=
  DirectSum.toAddMonoid_of _ _ _

theorem coe_comp_decomposeHom :
    (DirectSum.coeAddMonoidHom (𝓡 f L)).comp (decomposeHom f L) = AddMonoidHom.id _ := by
  classical
  refine DirectSum.addHom_ext fun n a => ?_
  rw [AddMonoidHom.comp_apply, decomposeHom_of, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
  rfl

theorem decomposeHom_comp_coe :
    (decomposeHom f L).comp (DirectSum.coeAddMonoidHom (𝓡 f L)) = AddMonoidHom.id _ := by
  classical
  refine DirectSum.addHom_ext fun n y => ?_
  obtain ⟨_, a, rfl⟩ := y
  rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
  exact decomposeHom_of f L n a

scoped instance : DirectSum.Decomposition (𝓡 f L) where
  decompose' := decomposeHom f L
  left_inv r := by
    have := congrArg (fun k => k r) (coe_comp_decomposeHom f L)
    exact this
  right_inv y := by
    have := congrArg (fun k => k y) (decomposeHom_comp_coe f L)
    exact this

scoped instance instGradedAlgebra : GradedAlgebra (𝓡 f L) :=
  { (inferInstance : SetLike.GradedMonoid (𝓡 f L)), (inferInstance : DirectSum.Decomposition (𝓡 f L)) with }

def ι (n : ℕ) (x : 𝓡 f L n) : Γ(L.tensorPow n, ⊤) := ((x : ⨁ n, Sec f L n) n : Sec f L n)

omit [Fact (Scheme.Modules.IsInvertible L)] in
theorem ι_of (n : ℕ) (a : Sec f L n) (h : DirectSum.of (Sec f L) n a ∈ 𝓡 f L n) :
    ι f L n ⟨DirectSum.of (Sec f L) n a, h⟩ = a :=
  DirectSum.of_eq_same n a

theorem isSectionRing : GradedOAlgebra.IsSectionRing f L (⨁ n, Sec f L n) (𝓡 f L) (ι f L) where
  bijective n := by
    constructor
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
      rw [ι_of, ι_of] at h
      subst h
      rfl
    · intro c
      exact ⟨⟨DirectSum.of (Sec f L) n c, c, rfl⟩, ι_of f L n c _⟩
  map_add n x y := DirectSum.add_apply _ _ _
  map_smul n s x := by
    change ((s • (x : ⨁ n, Sec f L n)) n : Sec f L n) = GradedOAlgebra.baseScalar f s • ι f L n x
    rw [DirectSum.smul_apply]
    rfl
  map_one := by
    change ((1 : ⨁ n, Sec f L n) 0 : Sec f L 0) = unitSection ⊤
    rw [DirectSum.one_def, DirectSum.of_eq_same]
    rfl
  map_mul m n x y := by
    obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    change ((DirectSum.of (Sec f L) m a * DirectSum.of (Sec f L) n b) (m + n) : Sec f L (m + n)) =
      (tensorPowAdd L m n).hom.app ⊤ (tensorSections (ι f L m ⟨_, a, rfl⟩) (ι f L n ⟨_, b, rfl⟩))
    rw [DirectSum.of_mul_of, DirectSum.of_eq_same, ι_of, ι_of]
    rfl

end F6ea14e94
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.F6ea14e94"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.F6ea14e94"

open scoped DirectSum in

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra S R) (𝓡 : ℕ → Submodule S R) (_ : GradedAlgebra 𝓡)
      (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)), AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι := by
  haveI : Fact (Scheme.Modules.IsInvertible L) := ⟨hL⟩
  exact ⟨⨁ n, F6ea14e94.Sec f L n, inferInstance, inferInstance, F6ea14e94.𝓡 f L, inferInstance,
    F6ea14e94.ι f L, F6ea14e94.isSectionRing f L⟩

end S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing (solution)
