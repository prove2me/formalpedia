-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:42.611873+00:00
-- url     : https://prove2.me/theorems/4434b82e-6b2f-4140-b5b4-11c40331b671
-- title:
--   Self Dual Lattice Actions
-- statement:
--   Definitions and structural lemmas for Self Dual Lattice Actions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualLatticeActions.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
section Defs
variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
abbrev Ev : Type := Fv F v ⊗[F] E
abbrev OEv : Subalgebra (v.adicCompletionIntegers F) (Ev E v) :=
  integralClosure (v.adicCompletionIntegers F) (Ev E v)
abbrev Wv (M : ℕ) : Type := Fin M → Ev E v
variable {E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def IsSelfDualIn (U : Submodule (Ev E v) (Wv E v M)) (L : Submodule (OEv E v) (Wv E v M)) : Prop :=
  L.FG ∧ Submodule.span (Ev E v) (L : Set (Wv E v M)) = U ∧
    ∀ y : Wv E v M, y ∈ L ↔ (y ∈ U ∧ ∀ z ∈ L, hR (Fv F v) σ J z y ∈ OEv E v)
def IsSelfDualLat (L : Submodule (OEv E v) (Wv E v M)) : Prop := IsSelfDualIn v σ J ⊤ L
def perp (x : Wv E v M) : Submodule (Ev E v) (Wv E v M) where
  carrier := {y | hR (Fv F v) σ J x y = 0}
  zero_mem' := by simp [hR, Formalism.UG.hform]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    have : ∀ i j, sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * (c • a) j =
        c * (sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * a j) := by
      intro i j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [this, ← Finset.mul_sum, ha, mul_zero]
def perpLat (x : Wv E v M) (L : Submodule (OEv E v) (Wv E v M)) :
    Submodule (OEv E v) (Wv E v M) :=
  (perp v σ J x).restrictScalars (OEv E v) ⊓ L
def act (g : HA (Fv F v) σ J) (y : Wv E v M) : Wv E v M :=
  (HA.mat (Fv F v) σ J g : Matrix (Fin M) (Fin M) (Ev E v)).mulVec y
open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) in
variable {E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act_one (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Wv E v M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J 1 y = y := by
  have h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J 1 = 1 := rfl
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act, h, Units.val_one, Matrix.one_mulVec]
open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) in
variable {E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act_mul (g g' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J)
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Wv E v M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J (g * g') y =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J g' y) := by
  have h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J (g * g') =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J g * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J g' := rfl
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act,
    h, Units.val_mul, Matrix.mulVec_mulVec]
def latStab (L : Submodule (OEv E v) (Wv E v M)) : Subgroup (HA (Fv F v) σ J) where
  carrier := {g | ∀ y, y ∈ L ↔ act v σ J g y ∈ L}
  one_mem' := by intro y; rw [act_one]
  mul_mem' := by
    intro a b ha hb y
    rw [act_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (act v σ J g⁻¹ y)
    rw [← act_mul, mul_inv_cancel, act_one] at this
    exact this.symm
def vecStab (x : Wv E v M) : Subgroup (HA (Fv F v) σ J) :=
  MulAction.stabilizer (HA (Fv F v) σ J) (fun _ : Fin 1 => x)
def latUnitaryIn (U : Submodule (Ev E v) (Wv E v M)) (L' : Submodule (OEv E v) (Wv E v M)) :
    Subgroup (U ≃ₗ[Ev E v] U) where
  carrier := {u | (∀ y z : U, hR (Fv F v) σ J (u y : Wv E v M) (u z : Wv E v M) =
      hR (Fv F v) σ J (y : Wv E v M) (z : Wv E v M)) ∧
    ∀ y : U, (y : Wv E v M) ∈ L' ↔ (u y : Wv E v M) ∈ L'}
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨fun y z => (ha.1 (b y) (b z)).trans (hb.1 y z), fun y => (hb.2 y).trans (ha.2 (b y))⟩
  inv_mem' := by
    intro u hu
    refine ⟨fun y z => ?_, fun y => ?_⟩
    · have := hu.1 (u.symm y) (u.symm z)
      rw [u.apply_symm_apply, u.apply_symm_apply] at this
      exact this.symm
    · have := hu.2 (u.symm y)
      rw [u.apply_symm_apply] at this
      exact this.symm
def Xbeta (β : Fv F v) : Set (Wv E v M) := {x | x ≠ 0 ∧ qR (Fv F v) σ J x = β}
def sphere (L : Submodule (OEv E v) (Wv E v M)) (β : Fv F v) : Set (Wv E v M) :=
  {x | x ∈ L ∧ qR (Fv F v) σ J x = β}
def HasOrthonormalBasis (L : Submodule (OEv E v) (Wv E v M)) : Prop :=
  ∃ e : Module.Basis (Fin M) (OEv E v) L,
    gramR (Fv F v) σ J (fun i => (e i : Wv E v M)) = 1
def UnitVectorClaims (L : Submodule (OEv E v) (Wv E v M)) (β : Fv F v) : Prop :=

  (sphere v σ J L β).Nonempty ∧

  (∀ x ∈ sphere v σ J L β,
    Submodule.span (OEv E v) {x} ⊔ perpLat v σ J x L = L ∧
    Disjoint (Submodule.span (OEv E v) {x}) (perpLat v σ J x L) ∧
    IsSelfDualIn v σ J (perp v σ J x) (perpLat v σ J x L)) ∧

  (∀ x ∈ sphere v σ J L β, ∀ x' ∈ sphere v σ J L β,
    ∃ g ∈ latStab v σ J L, act v σ J g x = x') ∧

  (∀ x ∈ sphere v σ J L β,
    latStab v σ J L ⊓ vecStab v σ J x = latStab v σ J (perpLat v σ J x L) ⊓ vecStab v σ J x ∧
    ∃ φ : ↥(latStab v σ J L ⊓ vecStab v σ J x) ≃*
        latUnitaryIn v σ J (perp v σ J x) (perpLat v σ J x L),
      ∀ (g : ↥(latStab v σ J L ⊓ vecStab v σ J x)) (y : perp v σ J x),
        (((φ g : perp v σ J x ≃ₗ[Ev E v] perp v σ J x) y : perp v σ J x) : Wv E v M) =
          act v σ J g y) ∧

  (∀ x ∈ Xbeta v σ J β, ∀ x' ∈ Xbeta v σ J β, ∃ g : HA (Fv F v) σ J, act v σ J g x = x') ∧

  (∀ x ∈ Xbeta v σ J β,
    (∃ L₁, IsSelfDualLat v σ J L₁ ∧ x ∈ L₁) ∧ ∃ L₂, IsSelfDualIn v σ J (perp v σ J x) L₂)
end Defs
def UnramifiedOrSplit {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal
def SelfDualLatticeLemmas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 1 ≤ M → IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)), UnramifiedOrSplit E v →
  ∀ (L : Submodule (OEv E v) (Wv E v M)), IsSelfDualLat v σ J L →
    HasOrthonormalBasis v σ J L ∧
    (∀ L' : Submodule (OEv E v) (Wv E v M), IsSelfDualLat v σ J L' →
      ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ act v σ J g y ∈ L') ∧
    ∀ β : (v.adicCompletionIntegers F)ˣ,
      UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)
section Basic₂
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
example (a : v.adicCompletionIntegers F) :
    algebraMap (v.adicCompletionIntegers F) (Ev E v) a = (a : Fv F v) ⊗ₜ[F] (1 : E) := rfl
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions


