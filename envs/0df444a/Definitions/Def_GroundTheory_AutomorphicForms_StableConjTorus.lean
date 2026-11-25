-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
-- name    : GroundTheory_AutomorphicForms_StableConjTorus
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:23.809797+00:00
-- url     : https://prove2.me/theorems/fd7bb3b8-1bbe-434f-845e-d3e347d06e66
-- title:
--   Stable Conj Torus
-- statement:
--   Definitions and structural lemmas for Stable Conj Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_commute_of_commute_of_separable
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module
section CommuteField
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
theorem commute_of_commute_of_separable_charpoly {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  let K := AlgebraicClosure E
  let φ : E →+* K := algebraMap E K
  let Φ : Module.End E V →+* Matrix (Fin n) (Fin n) K :=
    φ.mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom
  let Ψ : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toRingHom
  have hsep : (Ψ (Φ f)).charpoly.Separable := by
    change (Matrix.toLin' ((LinearMap.toMatrix b b f).map φ)).charpoly.Separable
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    exact hf.map
  have hc := commute_of_commute_of_separable hsep ((hg.map Φ).map Ψ) ((hg'.map Φ).map Ψ)
  have hinj : Function.Injective (Ψ.comp Φ) := by
    intro x y hxy
    have h1 : Φ x = Φ y := (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective hxy
    have h2 : LinearMap.toMatrixAlgEquiv b x = LinearMap.toMatrixAlgEquiv b y := by
      ext i j
      exact φ.injective (congrFun (congrFun h1 i) j)
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  change g * g' = g' * g
  apply hinj
  rw [map_mul, map_mul]
  exact hc.eq
end CommuteField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
namespace HermitianForm
variable (h : HermitianForm F E V)
noncomputable def adjoint (A : Module.End E V) : Module.End E V where
  toFun y := (Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)
  map_add' x y := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, map_add, LinearMap.add_comp]
  map_smul' c x := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_comp,
      RingHom.id_apply]
theorem toSesq_adjoint_left (A : Module.End E V) (y x : V) :
    h.toSesq (h.adjoint A y) x = h.toSesq y (A x) := by
  change h.toSesq ((Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)) x = _
  rw [Equiv.ofBijective_apply_symm_apply (⇑h.toSesq) h.nonsingular]
  rfl
theorem eq_adjoint_iff (A B : Module.End E V) :
    B = h.adjoint A ↔ ∀ y x, h.toSesq (B y) x = h.toSesq y (A x) := by
  refine ⟨fun hB y x => hB ▸ h.toSesq_adjoint_left A y x, fun hB => LinearMap.ext fun y => ?_⟩
  apply h.nonsingular.1
  ext x
  rw [hB, toSesq_adjoint_left]
theorem adjoint_mul (A B : Module.End E V) : h.adjoint (A * B) = h.adjoint B * h.adjoint A := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rw [Module.End.mul_apply, toSesq_adjoint_left, toSesq_adjoint_left, Module.End.mul_apply]
theorem adjoint_one : h.adjoint 1 = 1 := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rfl
noncomputable def adjointEquiv (g : V ≃ₗ[E] V) : V ≃ₗ[E] V where
  toLinearMap := h.adjoint g.toLinearMap
  invFun := h.adjoint g.symm.toLinearMap
  left_inv x := by
    change (h.adjoint g.symm.toLinearMap * h.adjoint g.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.toLinearMap * g.symm.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
  right_inv x := by
    change (h.adjoint g.toLinearMap * h.adjoint g.symm.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.symm.toLinearMap * g.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
theorem toSesq_adjointEquiv_left (g : V ≃ₗ[E] V) (y x : V) :
    h.toSesq (h.adjointEquiv g y) x = h.toSesq y (g x) :=
  h.toSesq_adjoint_left _ y x
noncomputable def twist (c : V ≃ₗ[E] V) (hc : h.adjointEquiv c = c) : HermitianForm F E V where
  toSesq := h.toSesq.comp c.toLinearMap
  isSymm := ⟨fun x y => by
    change conjHom F E (h.toSesq (c x) y) = h.toSesq (c y) x
    rw [conjHom_apply, h.conj_toSesq, ← hc, toSesq_adjointEquiv_left, hc]⟩
  nonsingular := h.nonsingular.comp c.bijective
end HermitianForm
section Stable
variable [FiniteDimensional E V]
def IsRegularSemisimple (γ : V ≃ₗ[E] V) : Prop :=
  (γ.toLinearMap).charpoly.Separable
def StablyConjugate (γ γ' : V ≃ₗ[E] V) : Prop :=
  ∃ g : V ≃ₗ[E] V, g * γ * g⁻¹ = γ'
def torusE (γ : V ≃ₗ[E] V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.centralizer {γ}
omit [FiniteDimensional E V] in
theorem mem_torusE {γ t : V ≃ₗ[E] V} : t ∈ torusE γ ↔ γ * t = t * γ := by
  simp [torusE, Subgroup.mem_centralizer_iff]
omit [FiniteDimensional E V] in
theorem commute_toLinearMap {a b : V ≃ₗ[E] V} (hab : a * b = b * a) :
    Commute a.toLinearMap b.toLinearMap :=
  LinearMap.ext fun x => DFunLike.congr_fun hab x
theorem torusE_mul_comm {γ a b : V ≃ₗ[E] V} (hγ : IsRegularSemisimple γ) (ha : a ∈ torusE γ)
    (hb : b ∈ torusE γ) : a * b = b * a := by
  have hc := commute_of_commute_of_separable_charpoly hγ
    (commute_toLinearMap (mem_torusE.1 ha)) (commute_toLinearMap (mem_torusE.1 hb))
  exact LinearEquiv.ext fun x => LinearMap.congr_fun hc.eq x
def TorusE (γ : V ≃ₗ[E] V) : Type _ := torusE γ
namespace TorusE
variable {γ : V ≃ₗ[E] V}
instance [Fact (IsRegularSemisimple γ)] : CommGroup (TorusE γ) :=
  { (inferInstance : Group (torusE γ)) with
    mul_comm := fun a b => Subtype.ext (torusE_mul_comm Fact.out a.2 b.2) }
def val (t : TorusE γ) : V ≃ₗ[E] V := Subtype.val (p := (· ∈ torusE γ)) t
def mk (t : V ≃ₗ[E] V) (ht : t ∈ torusE γ) : TorusE γ := (⟨t, ht⟩ : torusE γ)
variable [Fact (IsRegularSemisimple γ)]
end TorusE
end Stable
end GroundTheory.Automorphic


