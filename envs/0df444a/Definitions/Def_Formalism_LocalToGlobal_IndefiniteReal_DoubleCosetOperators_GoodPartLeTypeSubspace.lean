-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace
-- name    : Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:57.848134+00:00
-- url     : https://prove2.me/theorems/b4f316bb-499e-4386-b5bc-b63a7fd93b86
-- title:
--   Good Part Le Type Subspace
-- statement:
--   Definitions and structural lemmas for Good Part Le Type Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField TensorProduct
namespace Formalism.IndefR.NX.Core
structure RatCore where
  L0 : Type
  [fieldBase : Field L0]
  [numberFieldBase : NumberField L0]
  Ks : Type
  [fKs : Field Ks]
  [nfKs : NumberField Ks]
  [algKs : Algebra Ks L0]

  Tw : Type
  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]

  fractionRingMaps : ∀ (i : Tw) (_b : Bool), L0 →+* FractionRing (O i)

  G : Type
  [grpG : Group G]
  [finG : Fintype G]
  WL : ℕ → Type
  [acgWL : ∀ j, AddCommGroup (WL j)]
  [modWL : ∀ j, Module L0 (WL j)]
  [modKsWL : ∀ j, Module Ks (WL j)]
  [towWL : ∀ j, IsScalarTower Ks L0 (WL j)]
  [modOLWL : ∀ j, Module (𝓞 L0) (WL j)]
  [towOLWL : ∀ j, IsScalarTower (𝓞 L0) L0 (WL j)]
  [modOKsWL : ∀ j, Module (𝓞 Ks) (WL j)]
  [towOKsWL : ∀ j, IsScalarTower (𝓞 Ks) Ks (WL j)]
  W : ℕ → (L0 →+* ℂ) → Type
  [nW : ∀ j σ, NormedAddCommGroup (W j σ)]
  [ipW : ∀ j σ, InnerProductSpace ℂ (W j σ)]

  A : ∀ j, Arith.FormsL L0 Ks (WL j) (W j) G
attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW
variable (C : RatCore)
def KB (_C : RatCore) (i : _C.Tw) (_b : Bool) : Type := FractionRing (_C.O i)
instance (i : C.Tw) (b : Bool) : Field (KB C i b) := inferInstanceAs (Field (FractionRing (C.O i)))
def rd (i : C.Tw) (b : Bool) : C.L0 →+* KB C i b := C.fractionRingMaps i b
def ιK (i : C.Tw) (b : Bool) : C.Ks →+* KB C i b := (rd C i b).comp (algebraMap C.Ks C.L0)
instance (i : C.Tw) (b : Bool) : Algebra C.Ks (KB C i b) := (ιK C i b).toAlgebra
def FmK (j : ℕ) : Type := ↥(C.A j).WK
instance (j : ℕ) : AddCommGroup (FmK C j) := inferInstanceAs (AddCommGroup ↥(C.A j).WK)
instance (j : ℕ) : Module C.Ks (FmK C j) := inferInstanceAs (Module C.Ks ↥(C.A j).WK)
def Fm (i : C.Tw) (j : ℕ) (b : Bool) : Type := KB C i b ⊗[C.Ks] FmK C j
instance acgFm (i : C.Tw) (j : ℕ) (b : Bool) : AddCommGroup (Fm C i j b) :=
  inferInstanceAs (AddCommGroup (KB C i b ⊗[C.Ks] FmK C j))
instance modKB (i : C.Tw) (j : ℕ) (b : Bool) : Module (KB C i b) (Fm C i j b) :=
  inferInstanceAs (Module (KB C i b) (KB C i b ⊗[C.Ks] FmK C j))
instance modFmK (i : C.Tw) (j : ℕ) (b : Bool) : Module (FractionRing (C.O i)) (Fm C i j b) := modKB C i j b
instance modFmO (i : C.Tw) (j : ℕ) (b : Bool) : Module (C.O i) (Fm C i j b) :=
  Module.compHom (Fm C i j b) (algebraMap (C.O i) (FractionRing (C.O i)))
instance towFm (i : C.Tw) (j : ℕ) (b : Bool) : IsScalarTower (C.O i) (FractionRing (C.O i)) (Fm C i j b) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
def Bsup (i : C.Tw) (j : ℕ) (b : Bool) : Submodule (C.O i) (Fm C i j b) :=
  Submodule.span (C.O i)
    {f | ∃ x : FmK C j, (show ↥(C.A j).WK from x).1 ∈ (C.A j).MK ∧
      f = ((1 : KB C i b) ⊗ₜ[C.Ks] x : KB C i b ⊗[C.Ks] FmK C j)}
def RhoStab (j : ℕ) : Prop := ∀ (g : C.G) (x : C.WL j), x ∈ (C.A j).WK → (C.A j).ρ g x ∈ (C.A j).WK
def rhoKG (j : ℕ) (hst : RhoStab C j) : C.G →* Module.End C.Ks (FmK C j) where
  toFun g := (((C.A j).ρ g).restrictScalars C.Ks).restrict (p := (C.A j).WK) (q := (C.A j).WK)
    fun x hx => hst g x hx
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (C.A j).ρ 1 (show ↥(C.A j).WK from x).1 = (show ↥(C.A j).WK from x).1
    rw [map_one]
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (C.A j).ρ (g * h) (show ↥(C.A j).WK from x).1 =
      (C.A j).ρ g ((C.A j).ρ h (show ↥(C.A j).WK from x).1)
    rw [map_mul]
    rfl
def actEnd (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) :
    C.G →* Module.End (KB C i b) (KB C i b ⊗[C.Ks] FmK C j) where
  toFun g := (rd C i b (((C.A j).chi g : C.L0ˣ) : C.L0))⁻¹ •
    Module.End.baseChangeHom C.Ks (KB C i b) (FmK C j) (rhoKG C j hst g)
  map_one' := by
    rw [map_one, Units.val_one, map_one, inv_one, one_smul, map_one, map_one]
  map_mul' g h := by
    rw [map_mul, Units.val_mul, map_mul, mul_inv, map_mul, map_mul]
    exact (smul_mul_smul_comm _ _ _ _).symm
def actG (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) :
    C.G →* (Fm C i j b ≃ₗ[FractionRing (C.O i)] Fm C i j b) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (KB C i b) (KB C i b ⊗[C.Ks] FmK C j)).toMonoidHom.comp
    (MonoidHom.toHomUnits (actEnd C i j b hst))
def Fm0 (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (U : Subgroup C.G)
    (psiU : U →* (FractionRing (C.O i))ˣ) : Submodule (FractionRing (C.O i)) (Fm C i j b) :=
  ⨅ u : U, LinearMap.ker ((actG C i j b hst u).toLinearMap -
    ((psiU u : (FractionRing (C.O i))ˣ) : FractionRing (C.O i)) • LinearMap.id)
def eEnd (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (eC : C.G → C.L0) :
    Module.End (FractionRing (C.O i)) (Fm C i j b) :=
  ∑ g, C.fractionRingMaps i b (eC g) • (actG C i j b hst g).toLinearMap
def V0 (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (U : Subgroup C.G)
    (psiU : U →* (FractionRing (C.O i))ˣ) (eC : C.G → C.L0) : Submodule (FractionRing (C.O i)) (Fm C i j b) :=
  (Fm0 C i j b hst U psiU).map (eEnd C i j b hst eC)
def AO (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (eC : C.G → C.L0) : Module.End (C.O i) (Fm C i j b) :=
  ((Fintype.card C.G : ℕ) : C.O i) • (eEnd C i j b hst eC).restrictScalars (C.O i)
def Bgood (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (U : Subgroup C.G)
    (psiU : U →* (FractionRing (C.O i))ˣ) (eC : C.G → C.L0) : Submodule (C.O i) (Fm C i j b) :=
  Bsup C i j b ⊓ ((Fm0 C i j b hst U psiU) ⊓ (V0 C i j b hst U psiU eC)).restrictScalars (C.O i)
def inWL (j : ℕ) : C.L0 ⊗[C.Ks] FmK C j →ₗ[C.Ks] C.WL j :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => x • (show ↥(C.A j).WK from f).1
          map_add' := fun f f' => by
            change x • ((show ↥(C.A j).WK from f).1 + (show ↥(C.A j).WK from f').1) = _
            rw [smul_add]
          map_smul' := fun c f => by
            change x • (c • (show ↥(C.A j).WK from f).1) = c • (x • _)
            rw [smul_comm] }
      map_add' := fun x y => by
        ext f
        simp [add_smul]
      map_smul' := fun c x => by
        ext f
        change (c • x) • (show ↥(C.A j).WK from f).1 = c • (x • (show ↥(C.A j).WK from f).1)
        rw [smul_assoc] }
def IsThOf (j : ℕ) (σ0 : C.L0 →+* ℂ) (thC : C.W j σ0) (x : C.L0 ⊗[C.Ks] FmK C j) : Prop :=
  (C.A j).j σ0 (inWL C j x) = thC
def ThExists {Dat : Type} (j : ℕ) (σ0 : C.L0 →+* ℂ) (thC : Dat → C.W j σ0) : Prop :=
  ∀ d, ∃ x : C.L0 ⊗[C.Ks] FmK C j, IsThOf C j σ0 (thC d) x
def thK {Dat : Type} (j : ℕ) (σ0 : C.L0 →+* ℂ) (thC : Dat → C.W j σ0) (h : ThExists C j σ0 thC) (d : Dat) :
    C.L0 ⊗[C.Ks] FmK C j :=
  (h d).choose
def rdKs (i : C.Tw) (b : Bool) : C.L0 →ₗ[C.Ks] KB C i b where
  toFun := rd C i b
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
def thOf {Dat : Type} (i : C.Tw) (j : ℕ) (b : Bool) (σ0 : C.L0 →+* ℂ) (thC : Dat → C.W j σ0)
    (h : ThExists C j σ0 thC) (d : Dat) : Fm C i j b :=
  (LinearMap.rTensor (FmK C j) (rdKs C i b) (thK C j σ0 thC h d) : KB C i b ⊗[C.Ks] FmK C j)
end Formalism.IndefR.NX.Core


