-- Prove2me | solution 1 for AutomorphicForm.semilocal_central_transfer_peel_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/91393c5b-d4a6-5e85-b29e-6ef0cd402066

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
import Theorems.Thm_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_isInvInvariant_of_coupled_of_isInvInvariant
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled
import Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

namespace S30SemilocalCent

section GroupOrbitalFurniture

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

namespace GroupOrbital

section Defs

variable {G : Type} [Group G] [TopologicalSpace G]

def IsSection (θ : G →* G) (δ : G)
    (τ : @Measure (AutomorphicForm.sigmaCentralizer θ δ) (borel _)) (f : G → ℂ) (w : G → ℝ) : Prop :=
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ δ) := borel _
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, f (x⁻¹ * δ * θ x) ≠ 0 → ∫ t : AutomorphicForm.sigmaCentralizer θ δ, w (t * x) ∂τ = 1

def IsValue (θ : G →* G) (μ : @Measure G (borel G)) (δ : G)
    (τ : @Measure (AutomorphicForm.sigmaCentralizer θ δ) (borel _)) (f : G → ℂ) (I : ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  ∃ w : G → ℝ, IsSection θ δ τ f w ∧ I = ∫ x, f (x⁻¹ * δ * θ x) * (w x : ℂ) ∂μ

end Defs

section Bridges

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

theorem isTwistedSectionFnOn_iff (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L ⊗[K] A) → ℝ) :
    AutomorphicForm.IsTwistedSectionFnOn K L A σ δ τ' φ w ↔
      IsSection (AutomorphicForm.sigmaGL K L A σ) δ τ' φ w :=
  Iff.rfl

theorem isTwistedOrbitalIntegralOn_iff
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I' : ℂ) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I' ↔
      IsValue (AutomorphicForm.sigmaGL K L A σ) μ δ τ' φ I' :=
  Iff.rfl

end Bridges

section Transport

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem mem_sigmaCentralizer_map (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x))
    {δ t : G} (ht : t ∈ AutomorphicForm.sigmaCentralizer θ δ) :
    e t ∈ AutomorphicForm.sigmaCentralizer θ' (e δ) := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff] at ht ⊢
  rw [← he, ← map_inv, ← map_mul e t δ, ← map_mul, ht]

theorem symm_apply_twist (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x)) (y : H) :
    e.symm (θ' y) = θ (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

theorem mem_sigmaCentralizer_symm (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x))
    (δ : G) {t : H} (ht : t ∈ AutomorphicForm.sigmaCentralizer θ' (e δ)) :
    e.symm t ∈ AutomorphicForm.sigmaCentralizer θ δ := by
  have h := mem_sigmaCentralizer_map e.symm (symm_apply_twist e he) ht
  rwa [e.symm_apply_apply] at h

def torusMulEquiv (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x)) (δ : G) :
    AutomorphicForm.sigmaCentralizer θ δ ≃* AutomorphicForm.sigmaCentralizer θ' (e δ) :=
  { toFun := fun t => ⟨e t, mem_sigmaCentralizer_map e he t.2⟩
    invFun := fun t => ⟨e.symm t, mem_sigmaCentralizer_symm e he δ t.2⟩
    left_inv := fun _ => Subtype.ext (e.symm_apply_apply _)
    right_inv := fun _ => Subtype.ext (e.apply_symm_apply _)
    map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }

def torusEquiv (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x)) (δ : G) :
    AutomorphicForm.sigmaCentralizer θ δ ≃ₜ* AutomorphicForm.sigmaCentralizer θ' (e δ) :=
  { toMulEquiv := torusMulEquiv e he δ
    continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

theorem torusEquiv_apply_coe (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x))
    (δ : G) (t : AutomorphicForm.sigmaCentralizer θ δ) :
    ((torusEquiv e he δ t : AutomorphicForm.sigmaCentralizer θ' (e δ)) : H) = e t :=
  rfl

theorem IsSection.comp_symm (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x))
    (δ : G) (τ : @Measure (AutomorphicForm.sigmaCentralizer θ δ) (borel _)) (f : G → ℂ) (w : G → ℝ)
    (h : IsSection θ δ τ f w) :
    IsSection θ' (e δ) (@Measure.map _ _ (borel _) (borel _) (torusEquiv e he δ) τ) (f ∘ e.symm) (w ∘ e.symm) := by
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ δ) := borel _
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ' (e δ)) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ δ) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ' (e δ)) := ⟨rfl⟩
  obtain ⟨h0, hm, hc, h1⟩ := h
  refine ⟨fun x => h0 _, hm.comp e.symm.continuous.measurable,
    hc.comp_isClosedEmbedding e.symm.toHomeomorph.isClosedEmbedding, fun x hx => ?_⟩
  have hx' : f ((e.symm x)⁻¹ * δ * θ (e.symm x)) ≠ 0 := by
    have : e.symm (x⁻¹ * e δ * θ' x) = (e.symm x)⁻¹ * δ * θ (e.symm x) := by
      rw [map_mul, map_mul, map_inv, e.symm_apply_apply, symm_apply_twist e he]
    simpa only [Function.comp_apply, this] using hx
  have key := h1 (e.symm x) hx'
  have hmap : (Measure.map (torusEquiv e he δ) τ) =
      Measure.map ((torusEquiv e he δ).toHomeomorph.toMeasurableEquiv) τ := rfl
  rw [hmap, integral_map_equiv]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) key
  show w (e.symm ((e t : H) * x)) = w (t * e.symm x)
  rw [map_mul, e.symm_apply_apply]

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem IsValue.map (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x))
    (μ : @Measure G (borel G)) (δ : G) (τ : @Measure (AutomorphicForm.sigmaCentralizer θ δ) (borel _))
    (f : G → ℂ) (I : ℂ) (h : IsValue θ μ δ τ f I) :
    IsValue θ' (@Measure.map _ _ (borel G) (borel H) e μ) (e δ)
      (@Measure.map _ _ (borel _) (borel _) (torusEquiv e he δ) τ) (f ∘ e.symm) I := by
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : BorelSpace H := ⟨rfl⟩
  obtain ⟨w, hw, hI⟩ := h
  refine ⟨w ∘ e.symm, hw.comp_symm e he δ τ f, ?_⟩
  have hmap : (Measure.map e μ) = Measure.map (e.toHomeomorph.toMeasurableEquiv) μ := rfl
  rw [hI, hmap, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show f (x⁻¹ * δ * θ x) * (w x : ℂ) = f (e.symm ((e x)⁻¹ * e δ * θ' (e x))) * (w (e.symm (e x)) : ℂ)
  rw [← he, ← map_inv, ← map_mul, ← map_mul, e.symm_apply_apply, e.symm_apply_apply]

end Transport

end GroupOrbital

end GroupOrbitalFurniture

namespace GroupOrbital

section PiSplit

variable {ι : Type} [DecidableEq ι] (G : ι → Type) [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)] (i₀ : ι)

def piSplitEquiv : (∀ j, G j) ≃ₜ* G i₀ × (∀ j : {j // j ≠ i₀}, G j) :=
  { Homeomorph.piSplitAt i₀ G with map_mul' := fun _ _ => rfl }

theorem piSplitEquiv_apply (x : ∀ j, G j) : piSplitEquiv G i₀ x = (x i₀, fun j : {j // j ≠ i₀} => x j) := rfl

theorem piSplitEquiv_symm_apply_self (a : G i₀) (b : ∀ j : {j // j ≠ i₀}, G j) :
    (piSplitEquiv G i₀).symm (a, b) i₀ = a := by
  show (Equiv.piSplitAt i₀ G).symm (a, b) i₀ = a
  simp [Equiv.piSplitAt_symm_apply]

theorem piSplitEquiv_symm_apply_of_ne (a : G i₀) (b : ∀ j : {j // j ≠ i₀}, G j) (j : {j // j ≠ i₀}) :
    (piSplitEquiv G i₀).symm (a, b) j = b j := by
  show (Equiv.piSplitAt i₀ G).symm (a, b) j = b j
  simp [Equiv.piSplitAt_symm_apply, j.2]

end PiSplit

end GroupOrbital

end S30SemilocalCent

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

namespace GroupOrbital

section PeelTwist

variable {ι : Type} [DecidableEq ι] (G : ι → Type) [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)] (i₀ : ι)
  (θ : ∀ j, G j →* G j)

def piTwist : (∀ j, G j) →* (∀ j, G j) :=
  MonoidHom.pi fun j => (θ j).comp (Pi.evalMonoidHom G j)

@[scoped simp] theorem piTwist_apply (x : ∀ j, G j) (j : ι) : piTwist G θ x j = θ j (x j) := rfl

def piTwist' : (∀ j : {j // j ≠ i₀}, G j) →* (∀ j : {j // j ≠ i₀}, G j) :=
  MonoidHom.pi fun j => (θ j).comp (Pi.evalMonoidHom (fun j : {j // j ≠ i₀} => G j) j)

@[scoped simp] theorem piTwist'_apply (x : ∀ j : {j // j ≠ i₀}, G j) (j : {j // j ≠ i₀}) :
    piTwist' G i₀ θ x j = θ j (x j) := rfl

theorem piSplitEquiv_twist (x : ∀ j, G j) :
    piSplitEquiv G i₀ (piTwist G θ x) = ((θ i₀).prodMap (piTwist' G i₀ θ)) (piSplitEquiv G i₀ x) := rfl

end PeelTwist

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

namespace Carriers

section CentralizerRing

open AutomorphicForm

namespace RegularCentralizer

section Ring

variable {A : Type*} [CommRing A]

theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {G X : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X) :
    ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • G := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨u, hu⟩ := hd
  have hu1 : (↑u⁻¹ : A) * ↑u = 1 := u.inv_mul
  have h00 : (X * G) 0 0 = (G * X) 0 0 := by rw [hX]
  have h01 : (X * G) 0 1 = (G * X) 0 1 := by rw [hX]
  have h10 : (X * G) 1 0 = (G * X) 1 0 := by rw [hX]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  obtain ⟨Z, hZ⟩ : ∃ Z : A,
      Z = (G 0 0 - G 1 1) * (X 0 0 - X 1 1) + 2 * (G 1 0 * X 0 1 + G 0 1 * X 1 0) := ⟨_, rfl⟩
  refine ⟨X 0 0 - (↑u⁻¹ : A) * Z * G 0 0, (↑u⁻¹ : A) * Z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination (-(X 0 1)) * hu1 + (X 0 1 * (↑u⁻¹ : A)) * hu -
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h00 -
      ((↑u⁻¹ : A) * G 0 1) * hZ
  · simp
    linear_combination (-(X 1 0)) * hu1 + (X 1 0 * (↑u⁻¹ : A)) * hu +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h10 - (2 * (↑u⁻¹ : A) * G 1 0) * h00 -
      ((↑u⁻¹ : A) * G 1 0) * hZ
  · simp
    linear_combination (X 0 0 - X 1 1) * hu1 - ((X 0 0 - X 1 1) * (↑u⁻¹ : A)) * hu -
      (2 * (↑u⁻¹ : A) * G 1 0) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h10 +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * hZ

theorem commute_of_mul_eq_mul_of_mul_eq_mul {G X Y : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X)
    (hY : Y * G = G * Y) :
    Commute X Y := by
  obtain ⟨l, m, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hX
  obtain ⟨l', m', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hY
  have c1 : Commute (1 : Matrix (Fin 2) (Fin 2) A) (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_left _).smul_right l').add_right ((Commute.one_left G).smul_right m')
  have c2 : Commute G (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_right G).smul_right l').add_right ((Commute.refl G).smul_right m')
  exact (c1.smul_left l).add_left (c2.smul_left m)

theorem commute_of_mem_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) {x y : GL (Fin 2) A}
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := congrArg Units.val hx
  have hy' : (y : Matrix (Fin 2) (Fin 2) A) * g = g * y := congrArg Units.val hy
  exact Units.ext (commute_of_mul_eq_mul_of_mul_eq_mul hg hx' hy').eq

theorem isMulCommutative_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) :
    IsMulCommutative (Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_centralizer_of_isRegularSemisimple hg x.2 y.2).eq⟩⟩

end Ring
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end RegularCentralizer
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CentralizerRing
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section CentralizerCommutative

open AutomorphicForm
open scoped TensorProduct

namespace RegularCentralizer

section Generic

variable {G : Type*} [Group G]

theorem mul_prod_range_iterate (f : G →* G) {t δ : G} (h : t * δ = δ * f t) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑f)^[i] δ).prod =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc, ih, mul_assoc, mul_assoc, Function.iterate_succ_apply]
    congr 1
    have h' := congrArg ((⇑f)^[n]) h
    rwa [iterate_map_mul, iterate_map_mul] at h'

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem twistedCentralizer_le_centralizer_normString_of_iterate (σ : L ≃ₐ[K] L)
    (hσ : ∀ t : GL (Fin 2) (L ⊗[K] A), (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  have key := mul_prod_range_iterate (sigmaGL K L A σ) (mul_inv_eq_iff_eq_mul.mp ht')
    (Module.finrank K L)
  rw [hσ t] at key
  exact key

theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one, sigmaGL_one_apply]

theorem twistedCentralizer_le_centralizer_normString [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  twistedCentralizer_le_centralizer_normString_of_iterate K L A σ
    (sigmaGL_iterate_finrank K L A σ) δ

end Twisted
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end RegularCentralizer
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CentralizerCommutative
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section OrbitalCarriersBlock

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct Topology
open scoped TensorProduct.RightActions
open AutomorphicForm

namespace OrbitalCarriers

section GLCarrier

variable (A : Type) [CommRing A] [TopologicalSpace A]

theorem secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sigmaCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : SigmaCompactSpace (GL (Fin 2) A) := by
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

private theorem _root_.S30SemilocalCent.Carriers.OrbitalCarriers.isClosed_centralizer [IsTopologicalRing A] [T2Space A] (γ : GL (Fin 2) A) :
    IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : T2Space (GL (Fin 2) A) := Units.isEmbedding_embedProduct.t2Space
  have h : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A)) = {x | x * γ = γ * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

p2m_export "S30SemilocalCent.Carriers.OrbitalCarriers" "isClosed_centralizer"
end GLCarrier
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section TwistedClosed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (σ : L ≃ₐ[K] L)

theorem isClosed_twistedCentralizer (hσc : Continuous (sigmaGL K L A σ))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensorGL K L A
  have h : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul hσc.inv) continuous_const

end TwistedClosed
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Torus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G]

theorem regular_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    @Measure.Regular T (borel T) _ τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := hτ
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : T)
  exact Measure.regular_of_isMulLeftInvariant hC ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩
    hC.measure_lt_top.ne

open scoped IsMulCommutative in

theorem isInvInvariant_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (hcomm : IsMulCommutative T) (τ : @Measure T (borel T))
    (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) : @Measure.IsInvInvariant T (borel T) _ τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI := hτ
  haveI := hcomm
  haveI := regular_of_isHaarMeasure_of_isClosed T hT τ hτ
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular τ

omit [IsTopologicalGroup G] in
theorem sfinite_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    @SFinite T (borel T) τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := hτ
  infer_instance

end Torus
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section PiBorel

variable (A : Type) [CommRing A] [TopologicalSpace A] [SecondCountableTopology A]

theorem borelSpace_pi_gl (m : ℕ) :
    @BorelSpace (Fin m → GL (Fin 2) A) _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  haveI := borelSpace_glBorelOf A
  haveI := secondCountableTopology_gl A
  infer_instance

end PiBorel
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end OrbitalCarriers
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end OrbitalCarriersBlock
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section HaarScalarBlock

open MeasureTheory

namespace HaarScalar

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
  [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]

example (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure] : SigmaFinite (Measure.pi ν) := inferInstance

example (ν : ∀ i, Measure (H i)) [∀ i, (ν i).IsHaarMeasure] : (Measure.pi ν).IsMulLeftInvariant := inferInstance

example : MeasurableMul₂ (∀ i, H i) := inferInstance

theorem exists_map_eq_smul_pi (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i))
    [∀ i, (ν i).IsHaarMeasure] (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν := by
  haveI : (Measure.map Θ μ).IsHaarMeasure := Θ.isHaarMeasure_map μ hΘ hΘs
  exact ⟨Measure.haarScalarFactor (Measure.map Θ μ) (Measure.pi ν),
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end HaarScalar
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end HaarScalarBlock
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section CentralizerEmbeddingBlock

open MeasureTheory Topology AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace CentralizerEmbedding

section Embed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_algebraMap_tensor : Continuous (algebraMap A (L ⊗[K] A)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
      = (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) := by
  ext i j
  simp [toTensorGL, Matrix.GeneralLinearGroup.map_apply, TensorProduct.RightActions.algebraMap_eval]

theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ toTensorGL K L A) =
        fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => coe_toTensorGL K L A g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_algebraMap_tensor K L A)
  · have h : (fun g : GL (Fin 2) A => ((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)).val) =
        fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => by rw [← map_inv, coe_toTensorGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_algebraMap_tensor K L A)

theorem measurable_toTensorGL :
    @Measurable _ _ (glBorelOf A) (glBorelOf (L ⊗[K] A)) (toTensorGL K L A) := by
  letI := glBorelOf A
  letI := glBorelOf (L ⊗[K] A)
  haveI := borelSpace_glBorelOf A
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  exact (continuous_toTensorGL K L A).measurable

theorem measurableEmbedding_conj (y : GL (Fin 2) (L ⊗[K] A)) :
    @MeasurableEmbedding _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))
      (fun t : GL (Fin 2) (L ⊗[K] A) => y⁻¹ * t * y) := by
  letI := glBorelOf (L ⊗[K] A)
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  exact ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).measurableEmbedding

end Embed
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Tori

variable (A : Type) [CommRing A] [TopologicalSpace A]

theorem measurableEmbedding_centralizer_val (γ : GL (Fin 2) A)
    (hc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A))) :
    @MeasurableEmbedding _ _ (centralizerBorel A γ) (glBorelOf A)
      ((↑) : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) A) := by
  letI := glBorelOf A
  letI := centralizerBorel A γ
  haveI := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  have he : IsClosedEmbedding ((↑) : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
    hc.isClosedEmbedding_subtypeVal
  exact he.measurableEmbedding

end Tori
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section TwistedTori

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

theorem measurableEmbedding_twistedCentralizer_val (δ : GL (Fin 2) (L ⊗[K] A))
    (hc : IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A)))) :
    @MeasurableEmbedding _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
      ((↑) : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A)) := by
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ δ
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  have he : IsClosedEmbedding ((↑) : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A)) :=
    hc.isClosedEmbedding_subtypeVal
  exact he.measurableEmbedding

end TwistedTori
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CentralizerEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CentralizerEmbeddingBlock
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section CoupledProjectionBlock

open MeasureTheory NumberField

open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace CoupledProjection

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

open AutomorphicForm in

theorem map_conj_eq_map_val_of_coupled (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hc : Coupled K L A σ γ δ y τ τ')
    (ρ : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) A)
    (hρ : @Measurable _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf A) ρ)
    (hρi : ∀ s : GL (Fin 2) A, ρ (toTensorGL K L A s) = s)
    (hρy : ∀ g, ρ (y⁻¹ * g * y) = (ρ y)⁻¹ * ρ g * ρ y)
    (hval' : @Measurable _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
      (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))))
    (hval : @Measurable _ _ (centralizerBorel A γ) (glBorelOf A)
      (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)))
    (htor : @Measurable _ _ (glBorelOf A) (glBorelOf (L ⊗[K] A)) (toTensorGL K L A)) :
    @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf A)
        (fun t : twistedCentralizer K L A σ δ => (ρ y)⁻¹ * ρ (t : GL (Fin 2) (L ⊗[K] A)) * ρ y) τ' =
      @Measure.map _ _ (centralizerBorel A γ) (glBorelOf A)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) τ := by
  letI := glBorelOf (L ⊗[K] A)
  letI := glBorelOf A
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  have hconj : Measurable (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) :=
    (hval'.const_mul y⁻¹).mul_const y
  dsimp only [Coupled] at hc
  have h := congrArg (Measure.map ρ) hc
  have hts : Measurable (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      toTensorGL K L A (s : GL (Fin 2) A)) := htor.comp hval
  rw [Measure.map_map hρ hconj, Measure.map_map hρ hts] at h
  convert h using 2 <;> funext t <;> simp only [Function.comp_def, hρy, hρi]

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CoupledProjection
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CoupledProjectionBlock
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section TensorBlock

open AutomorphicForm

namespace TensorFacts

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] : SecondCountableTopology (L ⊗[K] A) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (L ⊗[K] A)
  have hq : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  exact hq.isQuotientMap.secondCountableTopology hq.isOpenMap

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section SigmaContinuous

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem sigmaTensor_tmul (x : L) (a : A) : sigmaTensor K L A σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

omit [IsTopologicalRing A] in
theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  have hs : ∀ (a : A) (x : L) (b : A), a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
    intro a x b
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
  let f : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := fun x y => map_add (sigmaTensor K L A σ) x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [hs, sigmaTensor_tmul K L A σ, sigmaTensor_tmul K L A σ, hs]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  exact IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_map (continuous_sigmaTensor K L A σ),
    Units.continuous_coe_inv.matrix_map (continuous_sigmaTensor K L A σ)⟩

end SigmaContinuous
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end TensorFacts
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end TensorBlock
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section CutoffBlock

namespace Cutoff

variable {G : Type} [TopologicalSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [OpensMeasurableSpace G] (μ : Measure G)

theorem exists_cutoff {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (hc : HasCompactSupport Φ)
    [IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin n => μ)] :
    ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1 := by
  set S : Set (Fin n → G) := (fun x : Fin (n + 1) → G => (Fin.init x : Fin n → G)) '' tsupport Φ
    with hS_def
  have hScompact : IsCompact S := hc.image (continuous_pi fun i => continuous_apply _)
  have hSm : MeasurableSet S := hScompact.isClosed.measurableSet
  refine ⟨S.indicator fun _ => (1 : ℝ), fun c => Set.indicator_nonneg (fun _ _ => zero_le_one) c,
    measurable_const.indicator hSm, ?_, fun c h hne => ?_⟩
  · rw [integrable_indicator_iff hSm]
    exact integrableOn_const hScompact.measure_lt_top.ne
  · have hcS : c ∈ S := ⟨Fin.snoc c h, subset_tsupport Φ hne, Fin.init_snoc _ _⟩
    exact Set.indicator_of_mem hcS _

end Cutoff
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end CutoffBlock
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end Carriers
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

namespace GroupOrbital

section CentBridge

variable {G : Type} [Group G] [TopologicalSpace G]

def centEquiv (γ : G) : Subgroup.centralizer ({γ} : Set G) ≃ₜ* sigmaCentralizer (MonoidHom.id G) γ :=
  { MulEquiv.subgroupCongr (sigmaCentralizer_id γ).symm with
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }

@[scoped simp] theorem centEquiv_apply_coe (γ : G) (s : Subgroup.centralizer ({γ} : Set G)) :
    ((centEquiv γ s : sigmaCentralizer (MonoidHom.id G) γ) : G) = (s : G) := rfl

@[scoped simp] theorem centEquiv_symm_apply_coe (γ : G) (t : sigmaCentralizer (MonoidHom.id G) γ) :
    (((centEquiv γ).symm t : Subgroup.centralizer ({γ} : Set G)) : G) = (t : G) := rfl

theorem integral_map_centEquiv (γ : G) (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _))
    (g : G → ℝ) :
    @integral _ ℝ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (centEquiv γ) τ)
        (fun t : sigmaCentralizer (MonoidHom.id G) γ => g (t : G)) =
      @integral _ ℝ _ _ (borel _) τ (fun s : Subgroup.centralizer ({γ} : Set G) => g (s : G)) := by
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer (MonoidHom.id G) γ) := borel _
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G) γ) := ⟨rfl⟩
  have hmap : @Measure.map _ _ (borel _) (borel _) (centEquiv γ) τ =
      Measure.map ((centEquiv γ).toHomeomorph.toMeasurableEquiv) τ := rfl
  rw [hmap, integral_map_equiv]
  rfl

theorem map_comp_coe_centEquiv {X : Type} [MeasurableSpace X] (γ : G)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _)) (f : G → X) (hf : Measurable[borel G] f) :
    @Measure.map _ _ (borel _) _ (fun t : sigmaCentralizer (MonoidHom.id G) γ => f (t : G))
        (@Measure.map _ _ (borel _) (borel _) (centEquiv γ) τ) =
      @Measure.map _ _ (borel _) _ (fun s : Subgroup.centralizer ({γ} : Set G) => f (s : G)) τ := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer (MonoidHom.id G) γ) := borel _
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G) γ) := ⟨rfl⟩
  have h1 : Measurable (fun t : sigmaCentralizer (MonoidHom.id G) γ => f (t : G)) :=
    hf.comp continuous_subtype_val.measurable
  have h2 : Measurable (centEquiv γ : Subgroup.centralizer ({γ} : Set G) → sigmaCentralizer (MonoidHom.id G) γ) :=
    (centEquiv γ).continuous.measurable
  rw [Measure.map_map h1 h2]
  rfl

variable [IsTopologicalGroup G]

theorem isHaarMeasure_map_centEquiv (γ : G) (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) :
    @Measure.IsHaarMeasure _ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (centEquiv γ) τ) := by
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer (MonoidHom.id G) γ) := borel _
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G) γ) := ⟨rfl⟩
  haveI := hτ
  exact (centEquiv γ).isHaarMeasure_map τ

theorem isInvInvariant_map_centEquiv (γ : G) (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _))
    (hτ : @Measure.IsInvInvariant _ (borel _) _ τ) :
    @Measure.IsInvInvariant _ (borel _) _ (@Measure.map _ _ (borel _) (borel _) (centEquiv γ) τ) := by
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer (MonoidHom.id G) γ) := borel _
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G) γ) := ⟨rfl⟩
  haveI := hτ
  have hem : Measurable (centEquiv γ) := (centEquiv γ).continuous.measurable
  refine ⟨?_⟩
  show Measure.map Inv.inv (Measure.map (centEquiv γ) τ) = Measure.map (centEquiv γ) τ
  rw [Measure.map_map measurable_inv hem]
  have : (Inv.inv ∘ (centEquiv γ)) = (centEquiv γ) ∘ Inv.inv := by
    funext s; simp only [Function.comp_apply, map_inv]
  rw [this, ← Measure.map_map hem measurable_inv, Measure.map_inv_eq_self]

end CentBridge
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section ClosedEmb

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] in
theorem rightActions_smul_tmul (a : A) (x : L) (b : A) : a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
  simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
  rw [TensorProduct.smul_tmul']
  simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]

theorem exists_continuous_leftInverse_algebraMap_tensor :
    ∃ r : L ⊗[K] A → A, Continuous r ∧ Function.LeftInverse r (algebraMap A (L ⊗[K] A)) := by
  have hinj : Function.Injective (Algebra.linearMap K L) := (algebraMap K L).injective
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L) (LinearMap.ker_eq_bot.2 hinj)
  have hℓ1 : ℓ 1 = 1 := by
    have := LinearMap.congr_fun hℓ (1 : K)
    simpa using this
  let r₀ : L ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ TensorProduct.map ℓ LinearMap.id
  have hr₀ : ∀ (x : L) (a : A), r₀ (x ⊗ₜ a) = ℓ x • a := fun x a => by
    simp [r₀, TensorProduct.map_tmul, TensorProduct.lid_tmul]

  let r : L ⊗[K] A →ₗ[A] A :=
    { toFun := r₀
      map_add' := fun x y => map_add r₀ x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [rightActions_smul_tmul K L A, hr₀, hr₀, smul_eq_mul, Algebra.smul_def, Algebra.smul_def,
            mul_left_comm]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  refine ⟨r, IsModuleTopology.continuous_of_linearMap r, fun a => ?_⟩
  show r₀ (algebraMap A (L ⊗[K] A) a) = a
  have ha : algebraMap A (L ⊗[K] A) a = (1 : L) ⊗ₜ[K] a := by
    first
      | rfl
      | simp [TensorProduct.RightActions.algebraMap_eval]
  rw [ha, hr₀, hℓ1, one_smul]

theorem isClosedEmbedding_algebraMap_tensor : IsClosedEmbedding (algebraMap A (L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  obtain ⟨r, hr, hl⟩ := exists_continuous_leftInverse_algebraMap_tensor K L A
  exact hl.isClosedEmbedding hr (Carriers.CentralizerEmbedding.continuous_algebraMap_tensor K L A)

theorem isClosedEmbedding_toTensorGL : IsClosedEmbedding (toTensorGL K L A) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  set ι := algebraMap A (L ⊗[K] A) with hι
  have hι' : IsClosedEmbedding ι := isClosedEmbedding_algebraMap_tensor K L A

  set mapM : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := fun M => M.map ι with hmapM
  have hM : IsClosedEmbedding mapM := by
    have : mapM = Pi.map (fun _ : Fin 2 => Pi.map (fun _ : Fin 2 => ι)) := by
      funext M i j; rfl
    rw [this]
    exact IsClosedEmbedding.piMap fun _ => IsClosedEmbedding.piMap fun _ => hι'
  have hMop : IsClosedEmbedding (fun z : (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ =>
      MulOpposite.op (mapM (MulOpposite.unop z))) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hM.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  have h1 : IsClosedEmbedding (Units.embedProduct (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) :=
    Units.isClosedEmbedding_embedProduct
  rw [← IsClosedEmbedding.of_comp_iff h1]
  have hcomp : (Units.embedProduct (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) ∘ (toTensorGL K L A) =
      (Prod.map mapM (fun z : (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ => MulOpposite.op (mapM (MulOpposite.unop z)))) ∘
        (Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) := by
    funext g
    simp only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]
    refine Prod.ext ?_ ?_
    · exact Carriers.CentralizerEmbedding.coe_toTensorGL K L A g
    · simp only
      rw [← map_inv]
      exact congrArg MulOpposite.op (Carriers.CentralizerEmbedding.coe_toTensorGL K L A g⁻¹)
  rw [hcomp]
  exact (hM.prodMap hMop).comp Units.isClosedEmbedding_embedProduct

end ClosedEmb
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

section InvAbstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem eq_of_map_eq_of_measurableEmbedding {S X : Type} [MeasurableSpace S] [MeasurableSpace X] {f : S → X}
    (hf : MeasurableEmbedding f) {μ ν : Measure S} (h : Measure.map f μ = Measure.map f ν) : μ = ν := by
  rw [← hf.comap_map μ, ← hf.comap_map ν, h]

theorem measurableEmbedding_conj_subtype [MeasurableSpace H] [BorelSpace H] (T : Subgroup H)
    (hT : IsClosed (T : Set H)) [MeasurableSpace T] [BorelSpace T] (y : H) :
    MeasurableEmbedding (fun t : T => y⁻¹ * (t : H) * y) := by
  have h1 : IsClosedEmbedding (Subtype.val : T → H) := hT.isClosedEmbedding_subtypeVal
  have h2 : IsClosedEmbedding (fun z : H => y⁻¹ * z * y) := by
    have e := ((Homeomorph.mulRight y).trans (Homeomorph.mulLeft y⁻¹)).isClosedEmbedding
    convert e using 1
    funext z
    simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight, mul_assoc]
  exact (h2.comp h1).measurableEmbedding

theorem isInvInvariant_of_map_conj_eq [MeasurableSpace H] [BorelSpace H] (T : Subgroup H)
    (hT : IsClosed (T : Set H)) [MeasurableSpace T] [BorelSpace T] (y : H) (τ' : Measure T) (ν : Measure H)
    (hν : Measure.map (Inv.inv : H → H) ν = ν)
    (h : Measure.map (fun t : T => y⁻¹ * (t : H) * y) τ' = ν) : τ'.IsInvInvariant := by
  have hjm : Measurable (fun t : T => y⁻¹ * (t : H) * y) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  refine ⟨eq_of_map_eq_of_measurableEmbedding (measurableEmbedding_conj_subtype T hT y) ?_⟩
  change Measure.map (fun t : T => y⁻¹ * (t : H) * y) (Measure.map Inv.inv τ') = _
  rw [Measure.map_map hjm measurable_inv]
  have h1 : ((fun t : T => y⁻¹ * (t : H) * y) ∘ Inv.inv) = (Inv.inv : H → H) ∘ (fun t : T => y⁻¹ * (t : H) * y) := by
    funext t
    simp only [Function.comp_apply, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
  rw [h1, ← Measure.map_map measurable_inv hjm, h, hν]

theorem map_inv_map_hom_coe {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [MeasurableSpace H] [BorelSpace H] (S : Subgroup G) [MeasurableSpace S] [BorelSpace S]
    (φ : G →* H) (hφ : Continuous φ) (τ : Measure S) [τ.IsInvInvariant] :
    Measure.map (Inv.inv : H → H) (Measure.map (fun s : S => φ (s : G)) τ) = Measure.map (fun s : S => φ (s : G)) τ := by
  have hm : Measurable (fun s : S => φ (s : G)) := (hφ.comp continuous_subtype_val).measurable
  rw [Measure.map_map measurable_inv hm]
  have : ((Inv.inv : H → H) ∘ fun s : S => φ (s : G)) = (fun s : S => φ (s : G)) ∘ Inv.inv := by
    funext s; simp only [Function.comp_apply, Subgroup.coe_inv, map_inv]
  rw [this, ← Measure.map_map hm measurable_inv, Measure.map_inv_eq_self]

end InvAbstract
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section RightInv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem isInvInvariant_of_isMulRightInvariant (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h3 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h4 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc, h5, one_smul]

theorem isMulRightInvariant_of_exists (μ₀ : Measure G) [μ₀.IsHaarMeasure] [μ₀.IsMulRightInvariant]
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  rw [Measure.isMulLeftInvariant_eq_smul μ μ₀]
  infer_instance

end RightInv
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section CentralTorus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem centralizer_eq_top_of_forall_commute (γ : G) (hγ : ∀ g : G, g * γ = γ * g) :
    Subgroup.centralizer ({γ} : Set G) = ⊤ := by
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_top, iff_true]
  exact hγ g

def centralizerTopEquiv (γ : G) (hγ : ∀ g : G, g * γ = γ * g) : Subgroup.centralizer ({γ} : Set G) ≃ₜ* G :=
  { (MulEquiv.subgroupCongr (centralizer_eq_top_of_forall_commute γ hγ)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      show Continuous fun g : G => (⟨g, _⟩ : Subgroup.centralizer ({γ} : Set G))
      exact continuous_id.subtype_mk _ }

@[scoped simp] theorem centralizerTopEquiv_apply (γ : G) (hγ : ∀ g : G, g * γ = γ * g)
    (s : Subgroup.centralizer ({γ} : Set G)) : centralizerTopEquiv γ hγ s = (s : G) := rfl

variable [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem isInvInvariant_centralizer_of_central (γ : G) (hγ : ∀ g : G, g * γ = γ * g)
    (μ₀ : Measure G) [μ₀.IsHaarMeasure] [μ₀.IsMulRightInvariant]
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))] [BorelSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G))) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  set e := centralizerTopEquiv γ hγ with he
  haveI : (Measure.map e τ).IsHaarMeasure := e.isHaarMeasure_map τ
  haveI : (Measure.map e τ).IsMulRightInvariant := isMulRightInvariant_of_exists μ₀ _
  haveI : (Measure.map e τ).IsInvInvariant := isInvInvariant_of_isMulRightInvariant _
  have hem : Measurable e := e.continuous.measurable
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨eq_of_map_eq_of_measurableEmbedding hemb ?_⟩
  change Measure.map e (Measure.map Inv.inv τ) = Measure.map e τ
  rw [Measure.map_map hem measurable_inv]
  have : (⇑e ∘ Inv.inv) = (Inv.inv : G → G) ∘ ⇑e := by
    funext s; simp only [Function.comp_apply, map_inv]
  rw [this, ← Measure.map_map measurable_inv hem, Measure.map_inv_eq_self]

theorem integral_centralizer_mul_eq (γ : G) (hγ : ∀ g : G, g * γ = γ * g)
    (μ₀ : Measure G) [μ₀.IsHaarMeasure] [μ₀.IsMulRightInvariant]
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))] [BorelSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G))) [τ.IsHaarMeasure] (u : G → ℝ) (x : G) :
    ∫ t : Subgroup.centralizer ({γ} : Set G), u ((t : G) * x) ∂τ =
      ∫ g : G, u g ∂(Measure.map (centralizerTopEquiv γ hγ) τ) := by
  set e := centralizerTopEquiv γ hγ with he
  haveI : (Measure.map e τ).IsHaarMeasure := e.isHaarMeasure_map τ
  haveI : (Measure.map e τ).IsMulRightInvariant := isMulRightInvariant_of_exists μ₀ _
  have hmap : Measure.map e τ = Measure.map e.toHomeomorph.toMeasurableEquiv τ := rfl
  calc ∫ t : Subgroup.centralizer ({γ} : Set G), u ((t : G) * x) ∂τ
      = ∫ g : G, u (g * x) ∂(Measure.map e τ) := by
        rw [hmap, integral_map_equiv]; rfl
    _ = ∫ g : G, u g ∂(Measure.map e τ) := integral_mul_right_eq_self _ x

end CentralTorus
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

namespace GroupOrbital

section TransportC

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

theorem mem_centralizer_map (e : G ≃ₜ* G') {γ s : G} (hs : s ∈ Subgroup.centralizer ({γ} : Set G)) :
    e s ∈ Subgroup.centralizer ({e γ} : Set G') := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ⊢
  rw [← map_mul, ← map_mul, hs]

theorem mem_centralizer_symm (e : G ≃ₜ* G') (γ : G) {s : G'} (hs : s ∈ Subgroup.centralizer ({e γ} : Set G')) :
    e.symm s ∈ Subgroup.centralizer ({γ} : Set G) := by
  have h := mem_centralizer_map e.symm hs
  rwa [e.symm_apply_apply] at h

def centTransportMulEquiv (e : G ≃ₜ* G') (γ : G) :
    Subgroup.centralizer ({γ} : Set G) ≃* Subgroup.centralizer ({e γ} : Set G') :=
  { toFun := fun s => ⟨e s, mem_centralizer_map e s.2⟩
    invFun := fun s => ⟨e.symm s, mem_centralizer_symm e γ s.2⟩
    left_inv := fun _ => Subtype.ext (e.symm_apply_apply _)
    right_inv := fun _ => Subtype.ext (e.apply_symm_apply _)
    map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }

def centTransport (e : G ≃ₜ* G') (γ : G) :
    Subgroup.centralizer ({γ} : Set G) ≃ₜ* Subgroup.centralizer ({e γ} : Set G') :=
  { toMulEquiv := centTransportMulEquiv e γ
    continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

@[scoped simp] theorem centTransport_apply_coe (e : G ≃ₜ* G') (γ : G) (s : Subgroup.centralizer ({γ} : Set G)) :
    ((centTransport e γ s : Subgroup.centralizer ({e γ} : Set G')) : G') = e s := rfl

def IsSectionC (γ : G) (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _)) (f : G → ℂ) (w : G → ℝ) :
    Prop :=
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, f (x⁻¹ * γ * x) ≠ 0 → ∫ t : Subgroup.centralizer ({γ} : Set G), w (t * x) ∂τ = 1

def IsValueC (μ : @Measure G (borel G)) (γ : G) (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _))
    (f : G → ℂ) (I : ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  ∃ w : G → ℝ, IsSectionC γ τ f w ∧ I = ∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂μ

theorem IsSectionC.comp_symm (e : G ≃ₜ* G') (γ : G) (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _))
    (f : G → ℂ) (w : G → ℝ) (h : IsSectionC γ τ f w) :
    IsSectionC (e γ) (@Measure.map _ _ (borel _) (borel _) (centTransport e γ) τ) (f ∘ e.symm) (w ∘ e.symm) := by
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace G' := borel G'
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : BorelSpace G' := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  letI : MeasurableSpace (Subgroup.centralizer ({e γ} : Set G')) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({e γ} : Set G')) := ⟨rfl⟩
  obtain ⟨h0, hm, hc, h1⟩ := h
  refine ⟨fun x => h0 _, hm.comp e.symm.continuous.measurable,
    hc.comp_isClosedEmbedding e.symm.toHomeomorph.isClosedEmbedding, fun x hx => ?_⟩
  have hx' : f ((e.symm x)⁻¹ * γ * (e.symm x)) ≠ 0 := by
    have : e.symm (x⁻¹ * e γ * x) = (e.symm x)⁻¹ * γ * (e.symm x) := by
      rw [map_mul, map_mul, map_inv, e.symm_apply_apply]
    simpa only [Function.comp_apply, this] using hx
  have key := h1 (e.symm x) hx'
  have hmap : (Measure.map (centTransport e γ) τ) =
      Measure.map ((centTransport e γ).toHomeomorph.toMeasurableEquiv) τ := rfl
  rw [hmap, integral_map_equiv]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) key
  show w (e.symm ((e t : G') * x)) = w (t * e.symm x)
  rw [map_mul, e.symm_apply_apply]

theorem IsValueC.map (e : G ≃ₜ* G') (μ : @Measure G (borel G)) (γ : G)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _)) (f : G → ℂ) (I : ℂ) (h : IsValueC μ γ τ f I) :
    IsValueC (@Measure.map _ _ (borel G) (borel G') e μ) (e γ)
      (@Measure.map _ _ (borel _) (borel _) (centTransport e γ) τ) (f ∘ e.symm) I := by
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace G' := borel G'
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : BorelSpace G' := ⟨rfl⟩
  obtain ⟨w, hw, hI⟩ := h
  refine ⟨w ∘ e.symm, hw.comp_symm e γ τ f, ?_⟩
  have hmap : (Measure.map e μ) = Measure.map (e.toHomeomorph.toMeasurableEquiv) μ := rfl
  rw [hI, hmap, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show f (x⁻¹ * γ * x) * (w x : ℂ) = f (e.symm ((e x)⁻¹ * e γ * (e x))) * (w (e.symm (e x)) : ℂ)
  rw [← map_inv, ← map_mul, ← map_mul, e.symm_apply_apply, e.symm_apply_apply]

end TransportC
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section TransportCoupling

variable {G G' H H' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H']

theorem coupling_transport (eG : G ≃ₜ* G') (eH : H ≃ₜ* H') (φ : G →* H) (φ' : G' →* H')
    (hφc : Continuous φ) (hφ'c : Continuous φ')
    (hφ : ∀ g, eH (φ g) = φ' (eG g)) {θ : H →* H} {θ' : H' →* H'} (hθ : ∀ x, eH (θ x) = θ' (eH x))
    (γ : G) (δ y : H)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _))
    (τ' : @Measure (sigmaCentralizer θ δ) (borel _))
    (hcpl : @Measure.map _ _ (borel _) (borel H) (fun t : sigmaCentralizer θ δ => y⁻¹ * (t : H) * y) τ' =
      @Measure.map _ _ (borel _) (borel H) (fun s : Subgroup.centralizer ({γ} : Set G) => φ (s : G)) τ) :
    @Measure.map _ _ (borel _) (borel H')
        (fun t : sigmaCentralizer θ' (eH δ) => (eH y)⁻¹ * (t : H') * eH y)
        (@Measure.map _ _ (borel _) (borel _) (torusEquiv eH hθ δ) τ') =
      @Measure.map _ _ (borel _) (borel H')
        (fun s : Subgroup.centralizer ({eG γ} : Set G') => φ' (s : G'))
        (@Measure.map _ _ (borel _) (borel _) (centTransport eG γ) τ) := by
  letI : MeasurableSpace G := borel G; haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace G' := borel G'; haveI : BorelSpace G' := ⟨rfl⟩
  letI : MeasurableSpace H := borel H; haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace H' := borel H'; haveI : BorelSpace H' := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({eG γ} : Set G')) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({eG γ} : Set G')) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer θ δ) := borel _
  haveI : BorelSpace (sigmaCentralizer θ δ) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer θ' (eH δ)) := borel _
  haveI : BorelSpace (sigmaCentralizer θ' (eH δ)) := ⟨rfl⟩
  have hj' : Measurable (fun t : sigmaCentralizer θ' (eH δ) => (eH y)⁻¹ * (t : H') * eH y) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hj : Measurable (fun t : sigmaCentralizer θ δ => y⁻¹ * (t : H) * y) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hT : Measurable (torusEquiv eH hθ δ : sigmaCentralizer θ δ → sigmaCentralizer θ' (eH δ)) :=
    (torusEquiv eH hθ δ).continuous.measurable
  have hC : Measurable (centTransport eG γ : Subgroup.centralizer ({γ} : Set G) → Subgroup.centralizer ({eG γ} : Set G')) :=
    (centTransport eG γ).continuous.measurable
  have hψ : Measurable (fun s : Subgroup.centralizer ({γ} : Set G) => φ (s : G)) :=
    (hφc.comp continuous_subtype_val).measurable
  have hψ' : Measurable (fun s : Subgroup.centralizer ({eG γ} : Set G') => φ' (s : G')) :=
    (hφ'c.comp continuous_subtype_val).measurable
  have heH : Measurable (eH : H → H') := eH.continuous.measurable
  rw [Measure.map_map hj' hT, Measure.map_map hψ' hC]
  have e1 : ((fun t : sigmaCentralizer θ' (eH δ) => (eH y)⁻¹ * (t : H') * eH y) ∘ (torusEquiv eH hθ δ)) =
      eH ∘ (fun t : sigmaCentralizer θ δ => y⁻¹ * (t : H) * y) := by
    funext t
    simp only [Function.comp_apply, torusEquiv_apply_coe, map_mul, map_inv]
  have e2 : ((fun s : Subgroup.centralizer ({eG γ} : Set G') => φ' (s : G')) ∘ (centTransport eG γ)) =
      eH ∘ (fun s : Subgroup.centralizer ({γ} : Set G) => φ (s : G)) := by
    funext s
    simp only [Function.comp_apply, centTransport_apply_coe, hφ]
  rw [e1, e2, ← Measure.map_map heH hj, ← Measure.map_map heH hψ, hcpl]

end TransportCoupling
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

namespace GroupOrbital

section Algebra

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem mem_centralizer_prod_iff (γ₁ : G₁) (γ₂ : G₂) (t : G₁ × G₂) :
    t ∈ Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) ↔
      t.1 ∈ Subgroup.centralizer ({γ₁} : Set G₁) ∧ t.2 ∈ Subgroup.centralizer ({γ₂} : Set G₂) := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [Subgroup.mem_centralizer_singleton_iff, Prod.mk_mul_mk, Prod.mk.injEq]

theorem mem_sigmaCentralizer_prodMap_iff (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) (t : G₁ × G₂) :
    t ∈ sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) ↔
      t.1 ∈ sigmaCentralizer θ₁ δ₁ ∧ t.2 ∈ sigmaCentralizer θ₂ δ₂ := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [mem_sigmaCentralizer_iff, MonoidHom.coe_prodMap, Prod.map_apply, Prod.inv_mk,
    Prod.mk_mul_mk, Prod.mk.injEq]

def prodCentMulEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) ≃*
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) :=
  { toFun := fun t => ⟨((t.1 : G₁), (t.2 : G₂)), (mem_centralizer_prod_iff γ₁ γ₂ _).mpr ⟨t.1.2, t.2.2⟩⟩
    invFun := fun t =>
      (⟨(t : G₁ × G₂).1, ((mem_centralizer_prod_iff γ₁ γ₂ _).mp t.2).1⟩,
       ⟨(t : G₁ × G₂).2, ((mem_centralizer_prod_iff γ₁ γ₂ _).mp t.2).2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

def prodTorusMulEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ ≃* sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toFun := fun t => ⟨((t.1 : G₁), (t.2 : G₂)), (mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mpr ⟨t.1.2, t.2.2⟩⟩
    invFun := fun t =>
      (⟨(t : G₁ × G₂).1, ((mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mp t.2).1⟩,
       ⟨(t : G₁ × G₂).2, ((mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mp t.2).2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

end Algebra
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Topology

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]

def prodCentEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) ≃ₜ*
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) :=
  { toMulEquiv := prodCentMulEquiv γ₁ γ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

theorem prodCentEquiv_apply_coe (γ₁ : G₁) (γ₂ : G₂)
    (t : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) :
    ((prodCentEquiv γ₁ γ₂ t : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) := rfl

def prodTorusEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ ≃ₜ* sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toMulEquiv := prodTorusMulEquiv θ₁ θ₂ δ₁ δ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

theorem prodTorusEquiv_apply_coe (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (t : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂) :
    ((prodTorusEquiv θ₁ θ₂ δ₁ δ₂ t : sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) := rfl

theorem isClosed_sigmaCentralizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {θ : G →* G} (hθ : Continuous θ) (δ : G) :
    IsClosed (sigmaCentralizer θ δ : Set G) := by
  have h : (sigmaCentralizer θ δ : Set G) = (fun t => t * δ * (θ t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp only [SetLike.mem_coe, mem_sigmaCentralizer_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rw [h]
  exact IsClosed.preimage ((continuous_id.mul continuous_const).mul hθ.inv) isClosed_singleton

private theorem _root_.S30SemilocalCent.GroupOrbital.isClosed_centralizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (γ : G) : IsClosed (Subgroup.centralizer ({γ} : Set G) : Set G) := by
  have h : (Subgroup.centralizer ({γ} : Set G) : Set G) = {x | x * γ = γ * x} := by
    ext x; exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

p2m_export "S30SemilocalCent.GroupOrbital" "isClosed_centralizer"
end Topology
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section ProdCoupling

variable {G₁ G₂ H₁ H₂ : Type}
  [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
  [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁] [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂]
  [SecondCountableTopology G₁] [SecondCountableTopology G₂] [SecondCountableTopology H₁] [SecondCountableTopology H₂]

theorem coupling_prod (φ₁ : G₁ →* H₁) (φ₂ : G₂ →* H₂) (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (η₁ : H₁ →* H₁) (η₂ : H₂ →* H₂) (γ₁ : G₁) (γ₂ : G₂) (δ₁ y₁ : H₁) (δ₂ y₂ : H₂)
    (τ₁ : @Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _))
    (τ₂ : @Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _))
    (τ₁' : @Measure (sigmaCentralizer η₁ δ₁) (borel _)) (τ₂' : @Measure (sigmaCentralizer η₂ δ₂) (borel _))
    (s₁ : @SFinite _ (borel _) τ₁) (s₂ : @SFinite _ (borel _) τ₂)
    (s₁' : @SFinite _ (borel _) τ₁') (s₂' : @SFinite _ (borel _) τ₂')
    (h₁ : @Measure.map _ _ (borel _) (borel H₁) (fun t : sigmaCentralizer η₁ δ₁ => y₁⁻¹ * (t : H₁) * y₁) τ₁' =
      @Measure.map _ _ (borel _) (borel H₁) (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => φ₁ (s : G₁)) τ₁)
    (h₂ : @Measure.map _ _ (borel _) (borel H₂) (fun t : sigmaCentralizer η₂ δ₂ => y₂⁻¹ * (t : H₂) * y₂) τ₂' =
      @Measure.map _ _ (borel _) (borel H₂) (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => φ₂ (s : G₂)) τ₂) :
    @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun t : sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂) => (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂))
        (@Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) (prodTorusEquiv η₁ η₂ δ₁ δ₂)
          (@Measure.prod _ _ (borel _) (borel _) τ₁' τ₂')) =
      @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => (φ₁.prodMap φ₂) (s : G₁ × G₂))
        (@Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) (prodCentEquiv γ₁ γ₂)
          (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)) := by
  letI mG₁ : MeasurableSpace G₁ := borel _; haveI : BorelSpace G₁ := ⟨rfl⟩
  letI mG₂ : MeasurableSpace G₂ := borel _; haveI : BorelSpace G₂ := ⟨rfl⟩
  letI mH₁ : MeasurableSpace H₁ := borel _; haveI : BorelSpace H₁ := ⟨rfl⟩
  letI mH₂ : MeasurableSpace H₂ := borel _; haveI : BorelSpace H₂ := ⟨rfl⟩
  haveI : BorelSpace (H₁ × H₂) := Prod.borelSpace
  have hb : (borel (H₁ × H₂)) = (Prod.instMeasurableSpace : MeasurableSpace (H₁ × H₂)) :=
    (BorelSpace.measurable_eq (α := H₁ × H₂)).symm
  rw [hb]
  letI mC₁ : MeasurableSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := ⟨rfl⟩
  letI mC₂ : MeasurableSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := ⟨rfl⟩
  letI mC : MeasurableSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := ⟨rfl⟩
  letI mT₁ : MeasurableSpace (sigmaCentralizer η₁ δ₁) := borel _; haveI : BorelSpace (sigmaCentralizer η₁ δ₁) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (sigmaCentralizer η₂ δ₂) := borel _; haveI : BorelSpace (sigmaCentralizer η₂ δ₂) := ⟨rfl⟩
  letI mT : MeasurableSpace (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI := s₁; haveI := s₂; haveI := s₁'; haveI := s₂'
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₂} : Set G₂)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer η₂ δ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) := Prod.borelSpace
  haveI : BorelSpace (sigmaCentralizer η₁ δ₁ × sigmaCentralizer η₂ δ₂) := Prod.borelSpace

  have hj : Measurable (fun t : sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂) => (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂)) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hψ : Measurable (fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => (φ₁.prodMap φ₂) (s : G₁ × G₂)) := by
    rw [MonoidHom.coe_prodMap]
    exact ((hφ₁.prodMap hφ₂).comp continuous_subtype_val).measurable
  have heT : Measurable (prodTorusEquiv η₁ η₂ δ₁ δ₂ : sigmaCentralizer η₁ δ₁ × sigmaCentralizer η₂ δ₂ → _) :=
    (prodTorusEquiv η₁ η₂ δ₁ δ₂).continuous.measurable
  have heC : Measurable (prodCentEquiv γ₁ γ₂ : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) → _) :=
    (prodCentEquiv γ₁ γ₂).continuous.measurable
  have hj₁ : Measurable (fun t : sigmaCentralizer η₁ δ₁ => y₁⁻¹ * (t : H₁) * y₁) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hj₂ : Measurable (fun t : sigmaCentralizer η₂ δ₂ => y₂⁻¹ * (t : H₂) * y₂) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hψ₁ : Measurable (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => φ₁ (s : G₁)) :=
    (hφ₁.comp continuous_subtype_val).measurable
  have hψ₂ : Measurable (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => φ₂ (s : G₂)) :=
    (hφ₂.comp continuous_subtype_val).measurable
  rw [Measure.map_map hj heT, Measure.map_map hψ heC]
  have e1 : ((fun t : sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂) => (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂)) ∘
      (prodTorusEquiv η₁ η₂ δ₁ δ₂)) =
      Prod.map (fun t : sigmaCentralizer η₁ δ₁ => y₁⁻¹ * (t : H₁) * y₁) (fun t : sigmaCentralizer η₂ δ₂ => y₂⁻¹ * (t : H₂) * y₂) := by
    funext p; rfl
  have e2 : ((fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => (φ₁.prodMap φ₂) (s : G₁ × G₂)) ∘
      (prodCentEquiv γ₁ γ₂)) =
      Prod.map (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => φ₁ (s : G₁))
        (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => φ₂ (s : G₂)) := by
    funext p; rfl
  rw [e1, e2, ← Measure.map_prod_map _ _ hj₁ hj₂, ← Measure.map_prod_map _ _ hψ₁ hψ₂, h₁, h₂]

end ProdCoupling
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

section CentralSectionK

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem exists_central_sectionK (γ : G) (hγ : ∀ g : G, g * γ = γ * g)
    (μ₀ : Measure G) [μ₀.IsHaarMeasure] [μ₀.IsMulRightInvariant]
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))] [BorelSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G))) [τ.IsHaarMeasure] :
    ∃ ω : G → ℝ, Continuous ω ∧ (∀ x, 0 ≤ ω x) ∧ HasCompactSupport ω ∧
      ∀ x : G, ∫ t : Subgroup.centralizer ({γ} : Set G), ω ((t : G) * x) ∂τ = 1 := by
  obtain ⟨u, huc, hu0, hu1⟩ := exists_continuous_nonneg_pos (1 : G)
  set ν : Measure G := Measure.map (centralizerTopEquiv γ hγ) τ with hν
  haveI : ν.IsHaarMeasure := (centralizerTopEquiv γ hγ).isHaarMeasure_map τ
  have hm : 0 < ∫ g, u g ∂ν :=
    u.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero huc hu0 hu1
  have hcs : HasCompactSupport (fun g : G => u g * (∫ g, u g ∂ν)⁻¹) := by
    have := HasCompactSupport.mul_right (f' := fun _ : G => (∫ g, u g ∂ν)⁻¹) huc
    exact this
  refine ⟨fun g => u g * (∫ g, u g ∂ν)⁻¹, u.continuous.mul continuous_const,
    fun x => mul_nonneg (hu0 x) (inv_nonneg.2 hm.le), hcs, fun x => ?_⟩
  rw [integral_mul_const, integral_centralizer_mul_eq γ hγ μ₀ τ (fun g => u g) x, ← hν,
    mul_inv_cancel₀ hm.ne']

end CentralSectionK
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

section Cutoff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contDiff_one_of_isCompact {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ ∀ x ∈ K, χ x = 1 := by
  classical
  by_cases hKe : K = ∅
  · exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp [hKe]⟩
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E

  set U : Set E := Metric.thickening 1 K with hU
  have hUo : IsOpen U := Metric.isOpen_thickening
  have hKU : K ⊆ U := Metric.self_subset_thickening one_pos K
  have hUb : Bornology.IsBounded U := hK.isBounded.thickening
  obtain ⟨f, hfsupp, hfs, hfr⟩ := hUo.exists_contDiff_support_eq (n := ⊤)
  have hfc : Continuous f := hfs.continuous

  have hfpos : ∀ x ∈ K, 0 < f x := by
    intro x hx
    have hx' : x ∈ Function.support f := hfsupp.symm ▸ hKU hx
    have h0 : 0 ≤ f x := (hfr ⟨x, rfl⟩).1
    exact lt_of_le_of_ne h0 (Ne.symm hx')
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hKne hfc.continuousOn
  set m : ℝ := f x₀ with hm
  have hm0 : 0 < m := hfpos x₀ hx₀K
  refine ⟨fun x => Real.smoothTransition (f x / m), ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (hfs.div_const m)
  · refine HasCompactSupport.intro' (K := closure U) (hUb.isCompact_closure) isClosed_closure ?_
    intro x hx
    have hxU : x ∉ U := fun h => hx (subset_closure h)
    have : f x = 0 := by
      have : x ∉ Function.support f := hfsupp.symm ▸ hxU
      simpa [Function.mem_support] using this
    simp [this, Real.smoothTransition.zero_of_nonpos (le_refl 0)]
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hm0, one_mul]
    exact hx₀ hx

end Cutoff
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section PartialSmooth

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  {M P : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiff_integral_smul_comp' (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (Ψ : M × P → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ) := by
  haveI : CompleteSpace ℂ := inferInstance
  refine contDiff_iff_contDiffAt.2 fun p₀ => ?_

  obtain ⟨χ₁, hχ₁s, hχ₁c, hχ₁1⟩ := exists_contDiff_one_of_isCompact (E := M) (hwc.isCompact.image hc)
  obtain ⟨χ₂, hχ₂s, hχ₂c, hχ₂1⟩ :=
    exists_contDiff_one_of_isCompact (E := P) (isCompact_closedBall p₀ 1)
  set Ψ' : M × P → ℂ := fun q => ((χ₁ q.1 * χ₂ q.2 : ℝ) : ℂ) * Ψ q with hΨ'
  have hΨ's : ContDiff ℝ (⊤ : ℕ∞) Ψ' := by
    refine ContDiff.mul ?_ hΨ
    exact (Complex.ofRealCLM.contDiff.comp ((hχ₁s.comp contDiff_fst).mul (hχ₂s.comp contDiff_snd)))
  have hΨ'c : HasCompactSupport Ψ' := by
    refine HasCompactSupport.mul_right ?_
    refine (HasCompactSupport.intro (hχ₁c.isCompact.prod hχ₂c.isCompact) fun q hq => ?_)
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ' (c x, p) ∂μ) :=
    MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport μ c hc w hw hwc Ψ' hΨ's hΨ'c

  have heq : ∀ p ∈ Metric.ball p₀ 1, (∫ x, w x • Ψ' (c x, p) ∂μ) = ∫ x, w x • Ψ (c x, p) ∂μ := by
    intro p hp
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport w
    · have h1 : χ₁ (c x) = 1 := hχ₁1 _ ⟨x, hx, rfl⟩
      have h2 : χ₂ p = 1 := hχ₂1 _ (Metric.ball_subset_closedBall hp)
      simp only [hΨ', h1, h2, mul_one, Complex.ofReal_one, one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hev : (fun p : P => ∫ x, w x • Ψ' (c x, p) ∂μ) =ᶠ[nhds p₀] fun p => ∫ x, w x • Ψ (c x, p) ∂μ :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)) heq
  exact (hsm.contDiffAt).congr_of_eventuallyEq hev.symm

end PartialSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section StepObjects

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι)

abbrev Gi (i : ι) : Type := GL (Fin 2) (A i)

abbrev Hi (i : ι) : Type := GL (Fin 2) (L ⊗[K] A i)

abbrev θfam (i : ι) : Hi K L A i →* Hi K L A i := sigmaGL K L (A i) σ

abbrev φfam (i : ι) : Gi A i →* Hi K L A i := toTensorGL K L (A i)

theorem locallyCompactSpace_Gi (i : ι) : LocallyCompactSpace (Gi A i) :=
  Carriers.OrbitalCarriers.locallyCompactSpace_gl (A i)
theorem secondCountableTopology_Gi (i : ι) : SecondCountableTopology (Gi A i) :=
  Carriers.OrbitalCarriers.secondCountableTopology_gl (A i)
theorem isTopologicalGroup_Hi (i : ι) : IsTopologicalGroup (Hi K L A i) := isTopologicalGroup_tensorGL K L (A i)
theorem t2Space_Hi (i : ι) : T2Space (Hi K L A i) := t2Space_tensorGL K L (A i)
theorem locallyCompactSpace_Hi (i : ι) : LocallyCompactSpace (Hi K L A i) := locallyCompactSpace_tensorGL K L (A i)
theorem secondCountableTopology_Hi (i : ι) : SecondCountableTopology (Hi K L A i) := by
  haveI := isTopologicalRing_tensor K L (A i)
  haveI := Carriers.TensorFacts.secondCountableTopology_tensor K L (A i)
  exact Carriers.OrbitalCarriers.secondCountableTopology_gl (L ⊗[K] A i)

theorem continuous_θfam (i : ι) : Continuous (θfam K L σ A i) := by
  haveI := isTopologicalRing_tensor K L (A i)
  exact Carriers.TensorFacts.continuous_sigmaGL K L (A i) σ
theorem continuous_φfam (i : ι) : Continuous (φfam K L A i) :=
  Carriers.CentralizerEmbedding.continuous_toTensorGL K L (A i)

noncomputable abbrev eG : (∀ i, Gi A i) ≃ₜ* Gi A i₀ × (∀ j : {j // j ≠ i₀}, Gi A j) :=
  GroupOrbital.piSplitEquiv (Gi A) i₀

noncomputable abbrev eH : (∀ i, Hi K L A i) ≃ₜ* Hi K L A i₀ × (∀ j : {j // j ≠ i₀}, Hi K L A j) :=
  GroupOrbital.piSplitEquiv (Hi K L A) i₀

abbrev etaPi : (∀ i, Hi K L A i) →* (∀ i, Hi K L A i) := GroupOrbital.piTwist (Hi K L A) (θfam K L σ A)
abbrev η' : (∀ j : {j // j ≠ i₀}, Hi K L A j) →* (∀ j : {j // j ≠ i₀}, Hi K L A j) :=
  GroupOrbital.piTwist' (Hi K L A) i₀ (θfam K L σ A)

abbrev PhiPi : (∀ i, Gi A i) →* (∀ i, Hi K L A i) :=
  MonoidHom.pi fun i => (φfam K L A i).comp (Pi.evalMonoidHom (Gi A) i)
abbrev Φ' : (∀ j : {j // j ≠ i₀}, Gi A j) →* (∀ j : {j // j ≠ i₀}, Hi K L A j) :=
  MonoidHom.pi fun j : {j // j ≠ i₀} => (φfam K L A j).comp (Pi.evalMonoidHom (fun j : {j // j ≠ i₀} => Gi A j) j)

theorem eH_etaPi (x : ∀ i, Hi K L A i) :
    eH K L A i₀ (etaPi K L σ A x) = ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ x) := rfl

theorem eH_PhiPi (g : ∀ i, Gi A i) :
    eH K L A i₀ (PhiPi K L A g) = ((φfam K L A i₀).prodMap (Φ' K L A i₀)) (eG A i₀ g) := rfl

theorem isClosedEmbedding_φfam (i : ι) : IsClosedEmbedding (φfam K L A i) := isClosedEmbedding_toTensorGL K L (A i)

theorem isClosedEmbedding_Φ' : IsClosedEmbedding (Φ' K L A i₀) := by
  have : ((Φ' K L A i₀) : (∀ j : {j // j ≠ i₀}, Gi A j) → ∀ j : {j // j ≠ i₀}, Hi K L A j) =
      Pi.map (fun j : {j // j ≠ i₀} => (φfam K L A j : Gi A j → Hi K L A j)) := by
    funext g j; rfl
  rw [this]
  exact IsClosedEmbedding.piMap fun j => isClosedEmbedding_φfam K L A j

theorem continuous_PhiPi : Continuous (PhiPi K L A) :=
  continuous_pi fun i => (continuous_φfam K L A i).comp (continuous_apply i)
theorem continuous_Φ' : Continuous (Φ' K L A i₀) :=
  continuous_pi fun j => (continuous_φfam K L A j).comp (continuous_apply j)
theorem continuous_η' : Continuous (η' K L σ A i₀) := by
  haveI := fun i => isTopologicalGroup_Hi K L A i
  exact continuous_pi fun j => (continuous_θfam K L σ A j).comp (continuous_apply j)
theorem continuous_prodMap_φ :
    Continuous ((φfam K L A i₀).prodMap (Φ' K L A i₀)) := by
  rw [MonoidHom.coe_prodMap]
  exact (continuous_φfam K L A i₀).prodMap (continuous_Φ' K L A i₀)

end StepObjects
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section StepSplit

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι)

set_option maxHeartbeats 3200000 in

theorem step_split (γ : ∀ i, Gi A i) (δ y : ∀ i, Hi K L A i)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) (borel _))
    (τ' : @Measure (sigmaCentralizer (etaPi K L σ A) δ) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hcpl : @Measure.map _ _ (borel _) (borel (∀ i, Hi K L A i))
        (fun t : sigmaCentralizer (etaPi K L σ A) δ => y⁻¹ * (t : ∀ i, Hi K L A i) * y) τ' =
      @Measure.map _ _ (borel _) (borel (∀ i, Hi K L A i))
        (fun s : Subgroup.centralizer ({γ} : Set (∀ i, Gi A i)) => PhiPi K L A (s : ∀ i, Gi A i)) τ) :
    ∃ (τ₁ : @Measure (Subgroup.centralizer ({γ i₀} : Set (Gi A i₀))) (borel _))
      (τ₂ : @Measure (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => γ j)} : Set (∀ j : {j // j ≠ i₀}, Gi A j)))
        (borel _))
      (τ₁' : @Measure (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) (borel _))
      (τ₂' : @Measure (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁ ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂ ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁' ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂' ∧
      @Measure.map _ _ (borel _) (borel _) (GroupOrbital.centTransport (eG A i₀) γ) τ =
        @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _)
          (GroupOrbital.prodCentEquiv (γ i₀) (fun j : {j // j ≠ i₀} => γ j))
          (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂) ∧
      @Measure.map _ _ (borel _) (borel _) (GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ) τ' =
        @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _)
          (GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) (δ i₀) (fun j : {j // j ≠ i₀} => δ j))
          (@Measure.prod _ _ (borel _) (borel _) τ₁' τ₂') ∧
      @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
          (fun t : sigmaCentralizer (θfam K L σ A i₀) (δ i₀) => (y i₀)⁻¹ * (t : Hi K L A i₀) * y i₀) τ₁' =
        @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
          (fun s : Subgroup.centralizer ({γ i₀} : Set (Gi A i₀)) => φfam K L A i₀ (s : Gi A i₀)) τ₁ ∧
      @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
          (fun t : sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j) =>
            (fun j : {j // j ≠ i₀} => y j)⁻¹ * (t : ∀ j : {j // j ≠ i₀}, Hi K L A j) * (fun j : {j // j ≠ i₀} => y j)) τ₂' =
        @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
          (fun s : Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => γ j)} : Set (∀ j : {j // j ≠ i₀}, Gi A j)) =>
            Φ' K L A i₀ (s : ∀ j : {j // j ≠ i₀}, Gi A j)) τ₂ := by
  haveI := fun i => locallyCompactSpace_Gi A i
  haveI := fun i => secondCountableTopology_Gi A i
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i

  have hcplb := GroupOrbital.coupling_transport (eG A i₀) (eH K L A i₀) (PhiPi K L A)
    ((φfam K L A i₀).prodMap (Φ' K L A i₀)) (continuous_PhiPi K L A) (continuous_prodMap_φ K L A i₀)
    (eH_PhiPi K L A i₀) (eH_etaPi K L σ A i₀) γ δ y τ τ' hcpl
  have hτb : @Measure.IsHaarMeasure _ _ _ (borel _)
      (@Measure.map _ _ (borel _) (borel _) (GroupOrbital.centTransport (eG A i₀) γ) τ) := by
    letI m1 : MeasurableSpace (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) := borel _
    haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) := ⟨rfl⟩
    letI m2 : MeasurableSpace (Subgroup.centralizer ({eG A i₀ γ} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) :=
      borel _
    haveI : BorelSpace (Subgroup.centralizer ({eG A i₀ γ} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) := ⟨rfl⟩
    haveI := hτ
    exact (GroupOrbital.centTransport (eG A i₀) γ).isHaarMeasure_map τ
  have hτb' : @Measure.IsHaarMeasure _ _ _ (borel _)
      (@Measure.map _ _ (borel _) (borel _) (GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ) τ') := by
    letI m1 : MeasurableSpace (sigmaCentralizer (etaPi K L σ A) δ) := borel _
    haveI : BorelSpace (sigmaCentralizer (etaPi K L σ A) δ) := ⟨rfl⟩
    letI m2 : MeasurableSpace
        (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ δ)) := borel _
    haveI : BorelSpace (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ δ)) := ⟨rfl⟩
    haveI := hτ'
    exact (GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ).isHaarMeasure_map τ'
  exact AutomorphicForm.exists_prod_eq_and_coupled_of_coupled_prod (φfam K L A i₀) (isClosedEmbedding_φfam K L A i₀)
    (Φ' K L A i₀) (isClosedEmbedding_Φ' K L A i₀) (θfam K L σ A i₀) (continuous_θfam K L σ A i₀)
    (η' K L σ A i₀) (continuous_η' K L σ A i₀) (γ i₀) (fun j : {j // j ≠ i₀} => γ j) (δ i₀) (y i₀)
    (fun j : {j // j ≠ i₀} => δ j) (fun j : {j // j ≠ i₀} => y j)
    (GroupOrbital.prodCentEquiv (γ i₀) (fun j : {j // j ≠ i₀} => γ j)) (fun p => rfl)
    (GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) (δ i₀) (fun j : {j // j ≠ i₀} => δ j))
    (fun p => rfl) _ hτb _ hτb' hcplb

end StepSplit
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section InlineShapes

variable {G : Type} [Group G] [TopologicalSpace G]

theorem GroupOrbital.isValue_iff_inline (θ : G →* G) (μ : @Measure G (borel G)) (δ : G)
    (τ : @Measure (sigmaCentralizer θ δ) (borel _)) (f : G → ℂ) (I : ℂ) :
    GroupOrbital.IsValue θ μ δ τ f I ↔
      ∃ W : G → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel G] W ∧ HasCompactSupport W ∧
        (∀ x : G, f (x⁻¹ * δ * θ x) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ (fun t => W ((t : G) * x)) = 1) ∧
        I = @integral _ ℂ _ _ (borel G) μ (fun x => f (x⁻¹ * δ * θ x) * (W x : ℂ)) := by
  constructor
  · rintro ⟨w, ⟨h0, hm, hc, h1⟩, hI⟩; exact ⟨w, h0, hm, hc, h1, hI⟩
  · rintro ⟨w, h0, hm, hc, h1, hI⟩; exact ⟨w, ⟨h0, hm, hc, h1⟩, hI⟩

theorem GroupOrbital.isValueC_iff_inline (μ : @Measure G (borel G)) (γ : G)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _)) (f : G → ℂ) (I : ℂ) :
    GroupOrbital.IsValueC μ γ τ f I ↔
      ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel G] w ∧ HasCompactSupport w ∧
        (∀ x : G, f (x⁻¹ * γ * x) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : G) * x)) = 1) ∧
        I = @integral _ ℂ _ _ (borel G) μ (fun x => f (x⁻¹ * γ * x) * (w x : ℂ)) := by
  constructor
  · rintro ⟨w, ⟨h0, hm, hc, h1⟩, hI⟩; exact ⟨w, h0, hm, hc, h1, hI⟩
  · rintro ⟨w, h0, hm, hc, h1, hI⟩; exact ⟨w, ⟨h0, hm, hc, h1⟩, hI⟩

end InlineShapes
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section StepInv

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)]

theorem scalar_central {R : Type} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) c = Matrix.GeneralLinearGroup.scalar (Fin 2) c * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hv : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  rw [hv]
  exact ((Matrix.scalar_commute (c : R) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) R)).eq).symm

theorem scalar_family_central {κ : Type} (B : κ → Type) [∀ k, CommRing (B k)] (c : ∀ k, (B k)ˣ)
    (g : ∀ k, GL (Fin 2) (B k)) :
    g * (fun k => Matrix.GeneralLinearGroup.scalar (Fin 2) (c k)) =
      (fun k => Matrix.GeneralLinearGroup.scalar (Fin 2) (c k)) * g := by
  funext k
  exact scalar_central (c k) (g k)

theorem isInvInvariant_centralizer_scalar_family {κ : Type} [Fintype κ] (B : κ → Type) [∀ k, CommRing (B k)]
    [∀ k, TopologicalSpace (B k)] [∀ k, IsTopologicalRing (B k)] [∀ k, T2Space (B k)]
    [∀ k, LocallyCompactSpace (B k)] [∀ k, SecondCountableTopology (B k)]
    (μ : ∀ k, @Measure (GL (Fin 2) (B k)) (glBorelOf (B k)))
    (hμ : ∀ k, @Measure.IsHaarMeasure _ _ _ (glBorelOf (B k)) (μ k))
    (hμr : ∀ k, @Measure.IsMulRightInvariant _ (glBorelOf (B k)) _ (μ k))
    (c : ∀ k, (B k)ˣ)
    (τ : @Measure (Subgroup.centralizer
      ({(fun k => Matrix.GeneralLinearGroup.scalar (Fin 2) (c k) : ∀ k, GL (Fin 2) (B k))} :
        Set (∀ k, GL (Fin 2) (B k)))) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) :
    @Measure.IsInvInvariant _ (borel _) _ τ := by
  letI mB : ∀ k, MeasurableSpace (GL (Fin 2) (B k)) := fun k => glBorelOf (B k)
  haveI : ∀ k, BorelSpace (GL (Fin 2) (B k)) := fun k => borelSpace_glBorelOf (B k)
  haveI := fun k => Carriers.OrbitalCarriers.locallyCompactSpace_gl (B k)
  haveI := fun k => Carriers.OrbitalCarriers.secondCountableTopology_gl (B k)
  haveI := hμ; haveI := hμr
  haveI : ∀ k, SigmaFinite (μ k) := fun k => inferInstance
  letI mC : MeasurableSpace (Subgroup.centralizer
      ({(fun k => Matrix.GeneralLinearGroup.scalar (Fin 2) (c k) : ∀ k, GL (Fin 2) (B k))} :
        Set (∀ k, GL (Fin 2) (B k)))) := borel _
  haveI : BorelSpace (Subgroup.centralizer
      ({(fun k => Matrix.GeneralLinearGroup.scalar (Fin 2) (c k) : ∀ k, GL (Fin 2) (B k))} :
        Set (∀ k, GL (Fin 2) (B k)))) := ⟨rfl⟩
  haveI := hτ

  haveI : (Measure.pi μ).IsHaarMeasure := inferInstance
  haveI : (Measure.pi μ).IsMulRightInvariant := inferInstance
  exact isInvInvariant_centralizer_of_central _ (fun g => scalar_family_central B c g) (Measure.pi μ) τ

end StepInv
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section StepInv2

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι)
  (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
  (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
  (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))

include μ hμ hμr

theorem step_inv_head (c₀ : (A i₀)ˣ) (δ₀ y₀ : Hi K L A i₀)
    (τ₁ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c₀} : Set (Gi A i₀))) (borel _))
    (τ₁' : @Measure (sigmaCentralizer (θfam K L σ A i₀) δ₀) (borel _))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁)
    (hc₁ : @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
        (fun t : sigmaCentralizer (θfam K L σ A i₀) δ₀ => y₀⁻¹ * (t : Hi K L A i₀) * y₀) τ₁' =
      @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
        (fun s : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c₀} : Set (Gi A i₀)) =>
          φfam K L A i₀ (s : Gi A i₀)) τ₁) :
    @Measure.IsInvInvariant _ (borel _) _ τ₁ ∧ @Measure.IsInvInvariant _ (borel _) _ τ₁' := by
  letI m0 : MeasurableSpace (Gi A i₀) := glBorelOf (A i₀)
  haveI : BorelSpace (Gi A i₀) := borelSpace_glBorelOf (A i₀)
  haveI := locallyCompactSpace_Gi A i₀
  haveI := secondCountableTopology_Gi A i₀
  letI m1 : MeasurableSpace
      (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c₀} : Set (Gi A i₀))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c₀} : Set (Gi A i₀))) := ⟨rfl⟩
  haveI := hμ i₀; haveI := hμr i₀; haveI := hτ₁
  have h1 : @Measure.IsInvInvariant _ (borel _) _ τ₁ :=
    isInvInvariant_centralizer_of_central _ (fun g => scalar_central c₀ g) (μ i₀) τ₁
  exact ⟨h1, AutomorphicForm.isInvInvariant_of_coupled_of_isInvInvariant K L σ (A i₀)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c₀) δ₀ y₀ τ₁ τ₁' hc₁ h1⟩

theorem step_inv_tail (c : ∀ i, (A i)ˣ) (δ' y' : ∀ j : {j // j ≠ i₀}, Hi K L A j)
    (τ₂ : @Measure (Subgroup.centralizer
      ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : ∀ j : {j // j ≠ i₀}, Gi A j)} :
        Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _))
    (τ₂' : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _))
    (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂)
    (hc₂ : @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
        (fun t : sigmaCentralizer (η' K L σ A i₀) δ' => y'⁻¹ * (t : ∀ j : {j // j ≠ i₀}, Hi K L A j) * y') τ₂' =
      @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
        (fun s : Subgroup.centralizer
            ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : ∀ j : {j // j ≠ i₀}, Gi A j)} :
              Set (∀ j : {j // j ≠ i₀}, Gi A j)) => Φ' K L A i₀ (s : ∀ j : {j // j ≠ i₀}, Gi A j)) τ₂) :
    @Measure.IsInvInvariant _ (borel _) _ τ₂ ∧ @Measure.IsInvInvariant _ (borel _) _ τ₂' := by
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  have h2 : @Measure.IsInvInvariant _ (borel _) _ τ₂ :=
    isInvInvariant_centralizer_scalar_family (fun j : {j // j ≠ i₀} => A j) (fun j => μ j) (fun j => hμ j)
      (fun j => hμr j) (fun j => c j) τ₂ hτ₂
  refine ⟨h2, ?_⟩
  letI mG : MeasurableSpace (∀ j : {j // j ≠ i₀}, Gi A j) := borel _
  haveI : BorelSpace (∀ j : {j // j ≠ i₀}, Gi A j) := ⟨rfl⟩
  letI mH : MeasurableSpace (∀ j : {j // j ≠ i₀}, Hi K L A j) := borel _
  haveI : BorelSpace (∀ j : {j // j ≠ i₀}, Hi K L A j) := ⟨rfl⟩
  letI mC : MeasurableSpace (Subgroup.centralizer
      ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : ∀ j : {j // j ≠ i₀}, Gi A j)} :
        Set (∀ j : {j // j ≠ i₀}, Gi A j))) := borel _
  haveI : BorelSpace (Subgroup.centralizer
      ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : ∀ j : {j // j ≠ i₀}, Gi A j)} :
        Set (∀ j : {j // j ≠ i₀}, Gi A j))) := ⟨rfl⟩
  letI mT : MeasurableSpace (sigmaCentralizer (η' K L σ A i₀) δ') := borel _
  haveI : BorelSpace (sigmaCentralizer (η' K L σ A i₀) δ') := ⟨rfl⟩
  haveI := h2
  have hT : IsClosed ((sigmaCentralizer (η' K L σ A i₀) δ' : Subgroup _) : Set (∀ j : {j // j ≠ i₀}, Hi K L A j)) :=
    GroupOrbital.isClosed_sigmaCentralizer (continuous_η' K L σ A i₀) δ'
  exact isInvInvariant_of_map_conj_eq _ hT y' τ₂' _
    (map_inv_map_hom_coe _ (Φ' K L A i₀) (continuous_Φ' K L A i₀) τ₂) hc₂

end StepInv2
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped NNReal

namespace GroupOrbital

section FubiniK

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [T2Space G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
  [SecondCountableTopology G₂] [T2Space G₂]

omit [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
  [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] in
theorem sigmaCentralizer_prodMap_id (δ : G₁ × G₂) :
    sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) δ = Subgroup.centralizer ({δ} : Set (G₁ × G₂)) := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  rfl

def centProdEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) ≃ₜ*
      sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂) :=
  { MulEquiv.subgroupCongr (sigmaCentralizer_prodMap_id (γ₁, γ₂)).symm with
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }

omit [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
  [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] in
theorem integral_map_centProdEquiv (γ₁ : G₁) (γ₂ : G₂)
    (τ : @Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) (borel _)) (g : G₁ × G₂ → ℝ) :
    @integral _ ℝ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (centProdEquiv γ₁ γ₂) τ)
        (fun t : sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂) => g (t : G₁ × G₂)) =
      @integral _ ℝ _ _ (borel _) τ (fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => g (s : G₁ × G₂)) := by
  letI : MeasurableSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂)) := borel _
  haveI : BorelSpace (sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂)) := ⟨rfl⟩
  have hmap : @Measure.map _ _ (borel _) (borel _) (centProdEquiv γ₁ γ₂) τ =
      Measure.map ((centProdEquiv γ₁ γ₂).toHomeomorph.toMeasurableEquiv) τ := rfl
  rw [hmap, integral_map_equiv]
  rfl

set_option maxHeartbeats 3200000 in

theorem fubini_centralizer (γ₁ : G₁) (γ₂ : G₂)
    (μ : @Measure (G₁ × G₂) (borel (G₁ × G₂))) (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel G₁)) (hμ₁ : @Measure.IsHaarMeasure G₁ _ _ (borel G₁) μ₁)
    (μ₂ : @Measure G₂ (borel G₂)) (hμ₂ : @Measure.IsHaarMeasure G₂ _ _ (borel G₂) μ₂)
    (τ₁ : @Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁) (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁)
    (τ₂ : @Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _))
    (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂) (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (f : G₁ × G₂ → ℂ), Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      ∀ (W₁ : G₁ → ℝ) (W₂ : G₂ → ℝ), Continuous W₁ → (∀ x, 0 ≤ W₁ x) → HasCompactSupport W₁ →
        Continuous W₂ → (∀ x, 0 ≤ W₂ x) → HasCompactSupport W₂ →
        (∀ (x₁ : G₁) (x₂ : G₂), f (x₁⁻¹ * γ₁ * x₁, x₂⁻¹ * γ₂ * x₂) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : G₁) * x₁)) = 1 ∧
          @integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : G₂) * x₂)) = 1) →
        letI τ : @Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) (borel _) :=
          @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) (prodCentEquiv γ₁ γ₂)
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)
        (∀ x : G₁ × G₂, f (x⁻¹ * (γ₁, γ₂) * x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ
              (fun t => W₁ (((t : G₁ × G₂) * x).1) * W₂ (((t : G₁ × G₂) * x).2)) = 1) ∧
        (∀ w : G₁ × G₂ → ℝ, (∀ x, 0 ≤ w x) → Measurable[borel (G₁ × G₂)] w → HasCompactSupport w →
          (∀ x : G₁ × G₂, f (x⁻¹ * (γ₁, γ₂) * x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ (fun t => w ((t : G₁ × G₂) * x)) = 1) →
          @integral _ ℂ _ _ (borel (G₁ × G₂)) μ (fun x => f (x⁻¹ * (γ₁, γ₂) * x) * (w x : ℂ)) =
            ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ =>
              f (x₁⁻¹ * γ₁ * x₁, x₂⁻¹ * γ₂ * x₂) * ((W₁ x₁ * W₂ x₂ : ℝ) : ℂ)))) := by

  letI mC₁ : MeasurableSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := ⟨rfl⟩
  letI mC₂ : MeasurableSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := ⟨rfl⟩
  letI mC : MeasurableSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := ⟨rfl⟩
  letI mT₁ : MeasurableSpace (sigmaCentralizer (MonoidHom.id G₁) γ₁) := borel _
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G₁) γ₁) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (sigmaCentralizer (MonoidHom.id G₂) γ₂) := borel _
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G₂) γ₂) := ⟨rfl⟩
  letI mT : MeasurableSpace (sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂)) := borel _
  haveI : BorelSpace (sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂)) := ⟨rfl⟩
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₂} : Set G₂)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer (MonoidHom.id G₂) γ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) := Prod.borelSpace
  haveI : BorelSpace (sigmaCentralizer (MonoidHom.id G₁) γ₁ × sigmaCentralizer (MonoidHom.id G₂) γ₂) := Prod.borelSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := (isClosed_centralizer γ₁).locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := (isClosed_centralizer γ₂).locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₁} : Set G₁)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI := hτ₁; haveI := hτ₂
  haveI : SFinite τ₁ := inferInstance
  haveI : SFinite τ₂ := inferInstance
  set σ₁ := Measure.map (centEquiv γ₁) τ₁ with hσ₁
  set σ₂ := Measure.map (centEquiv γ₂) τ₂ with hσ₂
  have hσ₁H := isHaarMeasure_map_centEquiv γ₁ τ₁ hτ₁
  have hσ₂H := isHaarMeasure_map_centEquiv γ₂ τ₂ hτ₂
  have hσ₁i := isInvInvariant_map_centEquiv γ₁ τ₁ hτ₁i
  have hσ₂i := isInvInvariant_map_centEquiv γ₂ τ₂ hτ₂i

  let e' : sigmaCentralizer (MonoidHom.id G₁) γ₁ × sigmaCentralizer (MonoidHom.id G₂) γ₂ →
      sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂) :=
    fun p => centProdEquiv γ₁ γ₂ (prodCentEquiv γ₁ γ₂ ((centEquiv γ₁).symm p.1, (centEquiv γ₂).symm p.2))
  have he' : ∀ p, ((e' p : sigmaCentralizer ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) (γ₁, γ₂)) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂)) := fun p => rfl
  obtain ⟨c, hc0, hc⟩ :=
    AutomorphicForm.integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
      (MonoidHom.id G₁) continuous_id (MonoidHom.id G₂) continuous_id γ₁ γ₂ μ hμ μ₁ hμ₁ μ₂ hμ₂
      σ₁ hσ₁H hσ₁i σ₂ hσ₂H hσ₂i e' he'
  refine ⟨c, hc0, fun f hf hfb W₁ W₂ hW₁c hW₁0 hW₁s hW₂c hW₂0 hW₂s hn => ?_⟩

  have hn' : ∀ (x₁ : G₁) (x₂ : G₂), f (x₁⁻¹ * γ₁ * (MonoidHom.id G₁) x₁, x₂⁻¹ * γ₂ * (MonoidHom.id G₂) x₂) ≠ 0 →
      ∫ t : sigmaCentralizer (MonoidHom.id G₁) γ₁, W₁ ((t : G₁) * x₁) ∂σ₁ = 1 ∧
      ∫ t : sigmaCentralizer (MonoidHom.id G₂) γ₂, W₂ ((t : G₂) * x₂) ∂σ₂ = 1 := by
    intro x₁ x₂ hx
    obtain ⟨h1, h2⟩ := hn x₁ x₂ hx
    refine ⟨?_, ?_⟩
    · rw [hσ₁, integral_map_centEquiv γ₁ τ₁ (fun g => W₁ (g * x₁))]; exact h1
    · rw [hσ₂, integral_map_centEquiv γ₂ τ₂ (fun g => W₂ (g * x₂))]; exact h2
  obtain ⟨hsec, hval⟩ := hc f hf hfb W₁ W₂ hW₁c hW₁0 hW₁s hW₂c hW₂0 hW₂s hn'

  have hmeas : @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) e' (σ₁.prod σ₂) =
      Measure.map (centProdEquiv γ₁ γ₂)
        (Measure.map (prodCentEquiv γ₁ γ₂) (τ₁.prod τ₂)) := by
    have h1 : Measurable (centEquiv γ₁ : Subgroup.centralizer ({γ₁} : Set G₁) → _) := (centEquiv γ₁).continuous.measurable
    have h2 : Measurable (centEquiv γ₂ : Subgroup.centralizer ({γ₂} : Set G₂) → _) := (centEquiv γ₂).continuous.measurable
    have h3 : Measurable (prodCentEquiv γ₁ γ₂ : _ → Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) :=
      (prodCentEquiv γ₁ γ₂).continuous.measurable
    have h4 : Measurable (centProdEquiv γ₁ γ₂ : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) → _) :=
      (centProdEquiv γ₁ γ₂).continuous.measurable
    have hs1 : Measurable ((centEquiv γ₁).symm : sigmaCentralizer (MonoidHom.id G₁) γ₁ → Subgroup.centralizer ({γ₁} : Set G₁)) :=
      (centEquiv γ₁).symm.continuous.measurable
    have hs2 : Measurable ((centEquiv γ₂).symm : sigmaCentralizer (MonoidHom.id G₂) γ₂ → Subgroup.centralizer ({γ₂} : Set G₂)) :=
      (centEquiv γ₂).symm.continuous.measurable
    have he'm2 : Measurable e' := h4.comp (h3.comp (hs1.prodMap hs2))
    rw [hσ₁, hσ₂, Measure.map_prod_map _ _ h1 h2, Measure.map_map he'm2 (h1.prodMap h2), Measure.map_map h4 h3]
    rfl
  refine ⟨fun x hx => ?_, fun w hw0 hwm hws hw1 => ?_⟩
  · have := hsec x hx
    rw [hmeas, integral_map_centProdEquiv γ₁ γ₂ _ (fun g => W₁ ((g * x).1) * W₂ ((g * x).2))] at this
    exact this
  · have hw1' : ∀ x : G₁ × G₂, f (x⁻¹ * (γ₁, γ₂) * ((MonoidHom.id G₁).prodMap (MonoidHom.id G₂)) x) ≠ 0 →
        ∫ t, w ((t : G₁ × G₂) * x) ∂(@Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) e'
          (σ₁.prod σ₂)) = 1 := by
      intro x hx
      rw [hmeas, integral_map_centProdEquiv γ₁ γ₂ _ (fun g => w (g * x))]
      exact hw1 x hx
    exact hval w hw0 hwm hws hw1'

end FubiniK
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent
namespace Partial

open MeasureTheory Topology

section Cutoff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contDiff_one_of_isCompact {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ ∀ x ∈ K, χ x = 1 := by
  classical
  by_cases hKe : K = ∅
  · exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp [hKe]⟩
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E

  set U : Set E := Metric.thickening 1 K with hU
  have hUo : IsOpen U := Metric.isOpen_thickening
  have hKU : K ⊆ U := Metric.self_subset_thickening one_pos K
  have hUb : Bornology.IsBounded U := hK.isBounded.thickening
  obtain ⟨f, hfsupp, hfs, hfr⟩ := hUo.exists_contDiff_support_eq (n := ⊤)
  have hfc : Continuous f := hfs.continuous

  have hfpos : ∀ x ∈ K, 0 < f x := by
    intro x hx
    have hx' : x ∈ Function.support f := hfsupp.symm ▸ hKU hx
    have h0 : 0 ≤ f x := (hfr ⟨x, rfl⟩).1
    exact lt_of_le_of_ne h0 (Ne.symm hx')
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hKne hfc.continuousOn
  set m : ℝ := f x₀ with hm
  have hm0 : 0 < m := hfpos x₀ hx₀K
  refine ⟨fun x => Real.smoothTransition (f x / m), ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (hfs.div_const m)
  · refine HasCompactSupport.intro' (K := closure U) (hUb.isCompact_closure) isClosed_closure ?_
    intro x hx
    have hxU : x ∉ U := fun h => hx (subset_closure h)
    have : f x = 0 := by
      have : x ∉ Function.support f := hfsupp.symm ▸ hxU
      simpa [Function.mem_support] using this
    simp [this, Real.smoothTransition.zero_of_nonpos (le_refl 0)]
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hm0, one_mul]
    exact hx₀ hx

end Cutoff
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section PartialSmooth

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  {M P : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiff_integral_smul_comp' (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (Ψ : M × P → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ) := by
  haveI : CompleteSpace ℂ := inferInstance
  refine contDiff_iff_contDiffAt.2 fun p₀ => ?_

  obtain ⟨χ₁, hχ₁s, hχ₁c, hχ₁1⟩ := exists_contDiff_one_of_isCompact (E := M) (hwc.isCompact.image hc)
  obtain ⟨χ₂, hχ₂s, hχ₂c, hχ₂1⟩ :=
    exists_contDiff_one_of_isCompact (E := P) (isCompact_closedBall p₀ 1)
  set Ψ' : M × P → ℂ := fun q => ((χ₁ q.1 * χ₂ q.2 : ℝ) : ℂ) * Ψ q with hΨ'
  have hΨ's : ContDiff ℝ (⊤ : ℕ∞) Ψ' := by
    refine ContDiff.mul ?_ hΨ
    exact (Complex.ofRealCLM.contDiff.comp ((hχ₁s.comp contDiff_fst).mul (hχ₂s.comp contDiff_snd)))
  have hΨ'c : HasCompactSupport Ψ' := by
    refine HasCompactSupport.mul_right ?_
    refine (HasCompactSupport.intro (hχ₁c.isCompact.prod hχ₂c.isCompact) fun q hq => ?_)
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ' (c x, p) ∂μ) :=
    MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport μ c hc w hw hwc Ψ' hΨ's hΨ'c

  have heq : ∀ p ∈ Metric.ball p₀ 1, (∫ x, w x • Ψ' (c x, p) ∂μ) = ∫ x, w x • Ψ (c x, p) ∂μ := by
    intro p hp
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport w
    · have h1 : χ₁ (c x) = 1 := hχ₁1 _ ⟨x, hx, rfl⟩
      have h2 : χ₂ p = 1 := hχ₂1 _ (Metric.ball_subset_closedBall hp)
      simp only [hΨ', h1, h2, mul_one, Complex.ofReal_one, one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hev : (fun p : P => ∫ x, w x • Ψ' (c x, p) ∂μ) =ᶠ[nhds p₀] fun p => ∫ x, w x • Ψ (c x, p) ∂μ :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)) heq
  exact (hsm.contDiffAt).congr_of_eventuallyEq hev.symm

end PartialSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Main

theorem partial_fst
    {H₁ H₂ : Type} [TopologicalSpace H₁] [MeasurableSpace H₁] [BorelSpace H₁] [T2Space H₁]
    [LocallyCompactSpace H₁] [SecondCountableTopology H₁] [TopologicalSpace H₂] [T2Space H₂]
    {Y₁ Y₂ : Type} [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁] [FiniteDimensional ℝ Y₁]
    [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [FiniteDimensional ℝ Y₂]
    (ε₁ : H₁ → Y₁) (hε₁ : Continuous ε₁) (ε₂ : H₂ → Y₂) (hε₂ : Continuous ε₂)
    (μ₁ : MeasureTheory.Measure H₁) [MeasureTheory.IsFiniteMeasureOnCompacts μ₁]
    (Φ : H₁ × H₂ → ℂ)
    (hΦ : ∃ Φ₁ : Y₁ × Y₂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ p : H₁ × H₂, Φ p = Φ₁ (ε₁ p.1, ε₂ p.2))
    (hΦc : HasCompactSupport Φ)
    (κ : H₁ → H₁) (hκ : Continuous κ) (W : H₁ → ℝ) (hW : Continuous W) (hWc : HasCompactSupport W) :
    (∃ Φ₂ : Y₂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₂ ∧
        ∀ h₂ : H₂, (∫ y, Φ (κ y, h₂) * (W y : ℂ) ∂μ₁) = Φ₂ (ε₂ h₂)) ∧
      HasCompactSupport (fun h₂ : H₂ => ∫ y, Φ (κ y, h₂) * (W y : ℂ) ∂μ₁) ∧
      Continuous (fun h₂ : H₂ => ∫ y, Φ (κ y, h₂) * (W y : ℂ) ∂μ₁) := by
  obtain ⟨Φ₁, hΦ₁, hΦeq⟩ := hΦ

  set Φ₂ : Y₂ → ℂ := fun q => ∫ y, W y • Φ₁ (ε₁ (κ y), q) ∂μ₁ with hΦ₂
  have hΦ₂s : ContDiff ℝ (⊤ : ℕ∞) Φ₂ :=
    contDiff_integral_smul_comp' μ₁ (ε₁ ∘ κ) (hε₁.comp hκ) W hW hWc Φ₁ hΦ₁
  have heq : ∀ h₂ : H₂, (∫ y, Φ (κ y, h₂) * (W y : ℂ) ∂μ₁) = Φ₂ (ε₂ h₂) := by
    intro h₂
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Φ (κ y, h₂) * (W y : ℂ) = W y • Φ₁ (ε₁ (κ y), ε₂ h₂)
    rw [hΦeq, Complex.real_smul, mul_comm]
  have hfun : (fun h₂ : H₂ => ∫ y, Φ (κ y, h₂) * (W y : ℂ) ∂μ₁) = Φ₂ ∘ ε₂ := funext heq
  refine ⟨⟨Φ₂, hΦ₂s, heq⟩, ?_, ?_⟩
  ·
    refine HasCompactSupport.intro' (hΦc.image continuous_snd) ((hΦc.image continuous_snd).isClosed) ?_
    intro h₂ hh₂
    have hzero : ∀ y, Φ (κ y, h₂) = 0 := by
      intro y
      by_contra hne
      exact hh₂ ⟨(κ y, h₂), subset_tsupport Φ hne, rfl⟩
    simp [hzero]
  · rw [hfun]
    exact hΦ₂s.continuous.comp hε₂

theorem partial_snd
    {H₁ H₂ : Type} [TopologicalSpace H₁] [T2Space H₁] [TopologicalSpace H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [T2Space H₂] [LocallyCompactSpace H₂] [SecondCountableTopology H₂]
    {Y₁ Y₂ : Type} [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁] [FiniteDimensional ℝ Y₁]
    [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] [FiniteDimensional ℝ Y₂]
    (ε₁ : H₁ → Y₁) (hε₁ : Continuous ε₁) (ε₂ : H₂ → Y₂) (hε₂ : Continuous ε₂)
    (μ₂ : MeasureTheory.Measure H₂) [MeasureTheory.IsFiniteMeasureOnCompacts μ₂]
    (Φ : H₁ × H₂ → ℂ)
    (hΦ : ∃ Φ₁ : Y₁ × Y₂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ p : H₁ × H₂, Φ p = Φ₁ (ε₁ p.1, ε₂ p.2))
    (hΦc : HasCompactSupport Φ)
    (κ : H₂ → H₂) (hκ : Continuous κ) (W : H₂ → ℝ) (hW : Continuous W) (hWc : HasCompactSupport W) :
    (∃ Φ₂ : Y₁ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₂ ∧
        ∀ h₁ : H₁, (∫ y, Φ (h₁, κ y) * (W y : ℂ) ∂μ₂) = Φ₂ (ε₁ h₁)) ∧
      HasCompactSupport (fun h₁ : H₁ => ∫ y, Φ (h₁, κ y) * (W y : ℂ) ∂μ₂) ∧
      Continuous (fun h₁ : H₁ => ∫ y, Φ (h₁, κ y) * (W y : ℂ) ∂μ₂) := by
  obtain ⟨Φ₁, hΦ₁, hΦeq⟩ := hΦ
  have hΦ' : ∃ Φ₁' : Y₂ × Y₁ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁' ∧
      ∀ p : H₂ × H₁, (fun p : H₂ × H₁ => Φ (p.2, p.1)) p = Φ₁' (ε₂ p.1, ε₁ p.2) :=
    ⟨fun q => Φ₁ (q.2, q.1), hΦ₁.comp (contDiff_snd.prodMk contDiff_fst), fun p => hΦeq (p.2, p.1)⟩
  have hΦc' : HasCompactSupport (fun p : H₂ × H₁ => Φ (p.2, p.1)) :=
    hΦc.comp_homeomorph (Homeomorph.prodComm H₂ H₁)
  exact partial_fst ε₂ hε₂ ε₁ hε₁ μ₂ (fun p : H₂ × H₁ => Φ (p.2, p.1)) hΦ' hΦc' κ hκ W hW hWc

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent.Partial
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology

namespace GroupOrbital

section SectionSwap

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H]

theorem twistedConj_mul_mem (θ : H →* H) (δ : H) (t : sigmaCentralizer θ δ) (x : H) :
    ((t : H) * x)⁻¹ * δ * θ ((t : H) * x) = x⁻¹ * δ * θ x := by
  have ht : (t : H)⁻¹ * δ * θ (t : H) = δ := by
    have h : (t : H) * δ * (θ (t : H))⁻¹ = δ := mem_sigmaCentralizer_iff.1 t.2
    calc (t : H)⁻¹ * δ * θ (t : H) = (t : H)⁻¹ * ((t : H) * δ * (θ (t : H))⁻¹) * θ (t : H) := by rw [h]
      _ = δ := by group
  rw [mul_inv_rev, map_mul]
  calc x⁻¹ * (t : H)⁻¹ * δ * (θ (t : H) * θ x) = x⁻¹ * ((t : H)⁻¹ * δ * θ (t : H)) * θ x := by group
    _ = x⁻¹ * δ * θ x := by rw [ht]

theorem integral_twistedConj_mul_eq_of_sections (θ : H →* H) (hθ : Continuous θ)
    (μ : @Measure H (borel H)) (hμ : @Measure.IsHaarMeasure H _ _ (borel H) μ) (δ : H)
    (τ' : @Measure (sigmaCentralizer θ δ) (borel _)) (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'i : @Measure.IsInvInvariant _ (borel _) _ τ')
    (f : H → ℂ) (hf : Continuous f) (W W' : H → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hW'0 : ∀ x, 0 ≤ W' x)
    (hWm : Measurable[borel H] W) (hW'm : Measurable[borel H] W')
    (h1 : ∀ x, f (x⁻¹ * δ * θ x) ≠ 0 → @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : H) * x)) = 1)
    (h1' : ∀ x, f (x⁻¹ * δ * θ x) ≠ 0 → @integral _ ℝ _ _ (borel _) τ' (fun t => W' ((t : H) * x)) = 1) :
    @integral _ ℂ _ _ (borel H) μ (fun x => f (x⁻¹ * δ * θ x) * (W x : ℂ)) =
      @integral _ ℂ _ _ (borel H) μ (fun x => f (x⁻¹ * δ * θ x) * (W' x : ℂ)) := by
  letI : MeasurableSpace H := borel H; haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer θ δ) := borel _; haveI : BorelSpace (sigmaCentralizer θ δ) := ⟨rfl⟩
  haveI := hμ; haveI := hτ'; haveI := hτ'i
  have hT : IsClosed ((sigmaCentralizer θ δ : Subgroup H) : Set H) := isClosed_sigmaCentralizer hθ δ
  haveI : LocallyCompactSpace (sigmaCentralizer θ δ) := hT.locallyCompactSpace
  haveI : SecondCountableTopology (sigmaCentralizer θ δ) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SFinite τ' := inferInstance
  have hF : Measurable (fun x : H => f (x⁻¹ * δ * θ x)) :=
    (hf.comp ((continuous_inv.mul continuous_const).mul hθ)).measurable
  exact AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one μ (sigmaCentralizer θ δ)
    continuous_subtype_val.measurable τ' (fun x => f (x⁻¹ * δ * θ x)) hF
    (fun t x => congrArg f (twistedConj_mul_mem θ δ t x)) W W' hW0 hW'0 hWm hW'm h1 h1'

theorem integral_conj_mul_eq_of_sections (μ : @Measure H (borel H)) (hμ : @Measure.IsHaarMeasure H _ _ (borel H) μ)
    (γ : H) (τ : @Measure (Subgroup.centralizer ({γ} : Set H)) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) (hτi : @Measure.IsInvInvariant _ (borel _) _ τ)
    (f : H → ℂ) (hf : Continuous f) (w w' : H → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw'0 : ∀ x, 0 ≤ w' x)
    (hwm : Measurable[borel H] w) (hw'm : Measurable[borel H] w')
    (h1 : ∀ x, f (x⁻¹ * γ * x) ≠ 0 → @integral _ ℝ _ _ (borel _) τ (fun t => w ((t : H) * x)) = 1)
    (h1' : ∀ x, f (x⁻¹ * γ * x) ≠ 0 → @integral _ ℝ _ _ (borel _) τ (fun t => w' ((t : H) * x)) = 1) :
    @integral _ ℂ _ _ (borel H) μ (fun x => f (x⁻¹ * γ * x) * (w x : ℂ)) =
      @integral _ ℂ _ _ (borel H) μ (fun x => f (x⁻¹ * γ * x) * (w' x : ℂ)) := by
  letI : MeasurableSpace H := borel H; haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set H)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set H)) := ⟨rfl⟩
  haveI := hμ; haveI := hτ; haveI := hτi
  have hT : IsClosed ((Subgroup.centralizer ({γ} : Set H)) : Set H) := isClosed_centralizer γ
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ} : Set H)) := hT.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ} : Set H)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SFinite τ := inferInstance
  have hF : Measurable (fun x : H => f (x⁻¹ * γ * x)) :=
    (hf.comp ((continuous_inv.mul continuous_const).mul continuous_id)).measurable
  have hinv : ∀ (t : Subgroup.centralizer ({γ} : Set H)) (x : H), f (((t : H) * x)⁻¹ * γ * ((t : H) * x)) = f (x⁻¹ * γ * x) := by
    intro t x
    have ht : (t : H) * γ = γ * (t : H) := Subgroup.mem_centralizer_singleton_iff.1 t.2
    congr 1
    rw [mul_inv_rev]
    calc x⁻¹ * (t : H)⁻¹ * γ * ((t : H) * x) = x⁻¹ * ((t : H)⁻¹ * (γ * (t : H))) * x := by group
      _ = x⁻¹ * γ * x := by rw [← ht]; group
  exact AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one μ
    (Subgroup.centralizer ({γ} : Set H)) continuous_subtype_val.measurable τ (fun x => f (x⁻¹ * γ * x)) hF
    hinv w w' hw0 hw'0 hwm hw'm h1 h1'

end SectionSwap
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory Topology

namespace GroupOrbital

theorem isInvInvariant_map_prod {T₁ T₂ T : Type}
    [Group T₁] [TopologicalSpace T₁] [IsTopologicalGroup T₁] [MeasurableSpace T₁] [BorelSpace T₁]
    [SecondCountableTopology T₁]
    [Group T₂] [TopologicalSpace T₂] [IsTopologicalGroup T₂] [MeasurableSpace T₂] [BorelSpace T₂]
    [SecondCountableTopology T₂]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T]
    (e : T₁ × T₂ ≃ₜ* T) (τ₁ : Measure T₁) (τ₂ : Measure T₂) [SFinite τ₁] [SFinite τ₂]
    [τ₁.IsInvInvariant] [τ₂.IsInvInvariant] :
    (Measure.map e (τ₁.prod τ₂)).IsInvInvariant := by
  haveI : BorelSpace (T₁ × T₂) := Prod.borelSpace
  have hem : Measurable e := e.continuous.measurable
  refine ⟨?_⟩
  change Measure.map Inv.inv (Measure.map e (τ₁.prod τ₂)) = Measure.map e (τ₁.prod τ₂)
  rw [Measure.map_map measurable_inv hem]
  have h1 : (Inv.inv ∘ e) = e ∘ (Inv.inv : T₁ × T₂ → T₁ × T₂) := by
    funext p; simp only [Function.comp_apply, map_inv]
  rw [h1, ← Measure.map_map hem measurable_inv]
  congr 1
  have h2 : (Inv.inv : T₁ × T₂ → T₁ × T₂) = Prod.map Inv.inv Inv.inv := by
    funext p; rfl
  rw [h2, ← Measure.map_prod_map _ _ measurable_inv measurable_inv, Measure.map_inv_eq_self, Measure.map_inv_eq_self]

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace GroupOrbital

section HaarRatio

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [T2Space G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
  [SecondCountableTopology G₂] [T2Space G₂]

theorem exists_haarRatio (μ : @Measure (G₁ × G₂) (borel (G₁ × G₂))) (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel G₁)) (hμ₁ : @Measure.IsHaarMeasure G₁ _ _ (borel G₁) μ₁)
    (μ₂ : @Measure G₂ (borel G₂)) (hμ₂ : @Measure.IsHaarMeasure G₂ _ _ (borel G₂) μ₂) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ g : G₁ × G₂ → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel (G₁ × G₂)) μ g =
        ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ => g (x₁, x₂))) := by
  letI m1 : MeasurableSpace G₁ := borel G₁; haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m2 : MeasurableSpace G₂ := borel G₂; haveI : BorelSpace G₂ := ⟨rfl⟩
  haveI : BorelSpace (G₁ × G₂) := Prod.borelSpace
  have hb : (borel (G₁ × G₂)) = (Prod.instMeasurableSpace : MeasurableSpace (G₁ × G₂)) :=
    (BorelSpace.measurable_eq (α := G₁ × G₂)).symm
  revert μ
  rw [hb]
  intro μ hμ
  haveI := hμ; haveI := hμ₁; haveI := hμ₂
  haveI : (μ₁.prod μ₂).IsHaarMeasure := inferInstance
  set c : ℝ≥0 := μ.haarScalarFactor (μ₁.prod μ₂) with hc
  have hμeq : μ = c • μ₁.prod μ₂ := Measure.isMulLeftInvariant_eq_smul μ (μ₁.prod μ₂)
  refine ⟨c, Measure.haarScalarFactor_pos_of_isHaarMeasure μ (μ₁.prod μ₂), fun g hg hgc => ?_⟩
  rw [hμeq, integral_smul_nnreal_measure, integral_prod _ (hg.integrable_of_hasCompactSupport hgc)]
  simp only [NNReal.smul_def, Complex.real_smul, smul_eq_mul]

end HaarRatio
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent
namespace Env

open MeasureTheory AutomorphicForm Topology
open scoped NNReal ENNReal

section Algebra

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem mem_centralizer_prod_iff (γ₁ : G₁) (γ₂ : G₂) (t : G₁ × G₂) :
    t ∈ Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) ↔
      t.1 ∈ Subgroup.centralizer ({γ₁} : Set G₁) ∧ t.2 ∈ Subgroup.centralizer ({γ₂} : Set G₂) := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [Subgroup.mem_centralizer_singleton_iff, Prod.mk_mul_mk, Prod.mk.injEq]

theorem mem_sigmaCentralizer_prodMap_iff (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) (t : G₁ × G₂) :
    t ∈ sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) ↔
      t.1 ∈ sigmaCentralizer θ₁ δ₁ ∧ t.2 ∈ sigmaCentralizer θ₂ δ₂ := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [mem_sigmaCentralizer_iff, MonoidHom.coe_prodMap, Prod.map_apply, Prod.inv_mk,
    Prod.mk_mul_mk, Prod.mk.injEq]

def prodCentMulEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) ≃*
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) :=
  { toFun := fun t => ⟨((t.1 : G₁), (t.2 : G₂)), (mem_centralizer_prod_iff γ₁ γ₂ _).mpr ⟨t.1.2, t.2.2⟩⟩
    invFun := fun t =>
      (⟨(t : G₁ × G₂).1, ((mem_centralizer_prod_iff γ₁ γ₂ _).mp t.2).1⟩,
       ⟨(t : G₁ × G₂).2, ((mem_centralizer_prod_iff γ₁ γ₂ _).mp t.2).2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

def prodTorusMulEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ ≃* sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toFun := fun t => ⟨((t.1 : G₁), (t.2 : G₂)), (mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mpr ⟨t.1.2, t.2.2⟩⟩
    invFun := fun t =>
      (⟨(t : G₁ × G₂).1, ((mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mp t.2).1⟩,
       ⟨(t : G₁ × G₂).2, ((mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mp t.2).2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

end Algebra
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Topology

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]

private def _root_.S30SemilocalCent.Env.prodCentEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) ≃ₜ*
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) :=
  { toMulEquiv := prodCentMulEquiv γ₁ γ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

p2m_export "S30SemilocalCent.Env" "prodCentEquiv"
theorem prodCentEquiv_apply_coe (γ₁ : G₁) (γ₂ : G₂)
    (t : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) :
    ((prodCentEquiv γ₁ γ₂ t : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) := rfl

private def _root_.S30SemilocalCent.Env.prodTorusEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ ≃ₜ* sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toMulEquiv := prodTorusMulEquiv θ₁ θ₂ δ₁ δ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

p2m_export "S30SemilocalCent.Env" "prodTorusEquiv"
theorem prodTorusEquiv_apply_coe (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (t : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂) :
    ((prodTorusEquiv θ₁ θ₂ δ₁ δ₂ t : sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) := rfl

private theorem _root_.S30SemilocalCent.Env.isClosed_sigmaCentralizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {θ : G →* G} (hθ : Continuous θ) (δ : G) :
    IsClosed (sigmaCentralizer θ δ : Set G) := by
  have h : (sigmaCentralizer θ δ : Set G) = (fun t => t * δ * (θ t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp only [SetLike.mem_coe, mem_sigmaCentralizer_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rw [h]
  exact IsClosed.preimage ((continuous_id.mul continuous_const).mul hθ.inv) isClosed_singleton

p2m_export "S30SemilocalCent.Env" "isClosed_sigmaCentralizer"
private theorem _root_.S30SemilocalCent.Env.isClosed_centralizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (γ : G) : IsClosed (Subgroup.centralizer ({γ} : Set G) : Set G) := by
  have h : (Subgroup.centralizer ({γ} : Set G) : Set G) = {x | x * γ = γ * x} := by
    ext x; exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

p2m_export "S30SemilocalCent.Env" "isClosed_centralizer"
end Topology
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section HaarProd

variable {C₁ C₂ C : Type} [Group C₁] [TopologicalSpace C₁] [IsTopologicalGroup C₁] [LocallyCompactSpace C₁]
  [SecondCountableTopology C₁] [MeasurableSpace C₁] [BorelSpace C₁]
  [Group C₂] [TopologicalSpace C₂] [IsTopologicalGroup C₂] [LocallyCompactSpace C₂]
  [SecondCountableTopology C₂] [MeasurableSpace C₂] [BorelSpace C₂]
  [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [LocallyCompactSpace C]
  [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]

theorem exists_isHaarMeasure_prod_eq (e : C₁ × C₂ ≃ₜ* C) (τ : Measure C) [τ.IsHaarMeasure] :
    ∃ (τ₁ : Measure C₁) (τ₂ : Measure C₂), τ₁.IsHaarMeasure ∧ τ₂.IsHaarMeasure ∧
      τ = Measure.map e (τ₁.prod τ₂) := by
  haveI : BorelSpace (C₁ × C₂) := Prod.borelSpace
  set ν : Measure C := Measure.map e ((Measure.haar : Measure C₁).prod (Measure.haar : Measure C₂)) with hν
  haveI : ((Measure.haar : Measure C₁).prod (Measure.haar : Measure C₂)).IsHaarMeasure := inferInstance
  haveI hνH : ν.IsHaarMeasure := by rw [hν]; exact e.isHaarMeasure_map _
  set s : ℝ≥0 := τ.haarScalarFactor ν with hs
  have hs0 : s ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure τ ν).ne'
  have hτ : τ = s • ν := Measure.isMulLeftInvariant_eq_smul τ ν
  refine ⟨(s : ℝ≥0∞) • Measure.haar, Measure.haar, ?_, inferInstance, ?_⟩
  · exact Measure.IsHaarMeasure.smul _ (by exact_mod_cast hs0) ENNReal.coe_ne_top
  · rw [Measure.prod_smul_left, Measure.map_smul, ← hν, hτ]
    rfl

end HaarProd
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Weights

variable {G₁ G₂ : Type} [TopologicalSpace G₁] [T2Space G₁] [TopologicalSpace G₂] [T2Space G₂]

theorem hasCompactSupport_prodWeights {W₁ : G₁ → ℝ} {W₂ : G₂ → ℝ} (hW₁s : HasCompactSupport W₁)
    (hW₂s : HasCompactSupport W₂) : HasCompactSupport fun x : G₁ × G₂ => W₁ x.1 * W₂ x.2 := by
  refine HasCompactSupport.intro (hW₁s.isCompact.prod hW₂s.isCompact) fun x hx => ?_
  simp only [Set.mem_prod, not_and_or] at hx
  rcases hx with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

omit [T2Space G₁] [T2Space G₂] in

theorem exists_bump_eq_one [LocallyCompactSpace G₁] [RegularSpace G₁] {K : Set G₁} (hK : IsCompact K) :
    ∃ ψ : G₁ → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ ∀ x ∈ K, ψ x = 1 := by
  obtain ⟨f, hf1, -, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  refine ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous,
    hfc.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero, fun x hx => ?_⟩
  show ((f x : ℝ) : ℂ) = 1
  rw [hf1 hx]; simp

end Weights
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

section Main

theorem envelope_section_prod
    {H₁ H₂ : Type}
    [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁] [LocallyCompactSpace H₁] [SecondCountableTopology H₁] [T2Space H₁]
    [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂] [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [T2Space H₂]
    (θ₁ : H₁ →* H₁) (hθ₁ : Continuous θ₁) (θ₂ : H₂ →* H₂) (hθ₂ : Continuous θ₂) (δ₁ : H₁) (δ₂ : H₂)
    (τ : @MeasureTheory.Measure (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) (borel _))
    (hτ : @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ)
    (hinv₁ : ∀ τ₁ : @MeasureTheory.Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _),
      @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ₁ → @MeasureTheory.Measure.IsInvInvariant _ (borel _) _ τ₁)
    (hinv₂ : ∀ τ₂ : @MeasureTheory.Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _),
      @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ₂ → @MeasureTheory.Measure.IsInvInvariant _ (borel _) _ τ₂)
    (hsec₁ : ∀ τ₁ : @MeasureTheory.Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _),
      @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ₁ → @MeasureTheory.Measure.IsInvInvariant _ (borel _) _ τ₁ →
      ∀ ψ : H₁ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ W₁ : H₁ → ℝ, Continuous W₁ ∧ (∀ x, 0 ≤ W₁ x) ∧ HasCompactSupport W₁ ∧
          ∀ x₁ : H₁, ψ (x₁⁻¹ * δ₁ * θ₁ x₁) ≠ 0 →
            @MeasureTheory.integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : H₁) * x₁)) = 1)
    (hsec₂ : ∀ τ₂ : @MeasureTheory.Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _),
      @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ₂ → @MeasureTheory.Measure.IsInvInvariant _ (borel _) _ τ₂ →
      ∀ ψ : H₂ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ W₂ : H₂ → ℝ, Continuous W₂ ∧ (∀ x, 0 ≤ W₂ x) ∧ HasCompactSupport W₂ ∧
          ∀ x₂ : H₂, ψ (x₂⁻¹ * δ₂ * θ₂ x₂) ≠ 0 →
            @MeasureTheory.integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : H₂) * x₂)) = 1)
    (Ψ : H₁ × H₂ → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ W : H₁ × H₂ → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : H₁ × H₂, Ψ (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
        @MeasureTheory.integral _ ℝ _ _ (borel _) τ (fun t => W ((t : H₁ × H₂) * x)) = 1 := by

  letI m1 : MeasurableSpace (sigmaCentralizer θ₁ δ₁) := borel _
  haveI : BorelSpace (sigmaCentralizer θ₁ δ₁) := ⟨rfl⟩
  letI m2 : MeasurableSpace (sigmaCentralizer θ₂ δ₂) := borel _
  haveI : BorelSpace (sigmaCentralizer θ₂ δ₂) := ⟨rfl⟩
  letI m12 : MeasurableSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ := hτ

  haveI : LocallyCompactSpace (sigmaCentralizer θ₁ δ₁) :=
    (isClosed_sigmaCentralizer hθ₁ δ₁).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer θ₂ δ₂) :=
    (isClosed_sigmaCentralizer hθ₂ δ₂).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) :=
    (isClosed_sigmaCentralizer (θ := θ₁.prodMap θ₂) (hθ₁.prodMap hθ₂) (δ₁, δ₂)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (sigmaCentralizer θ₁ δ₁) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer θ₂ δ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂) := Prod.borelSpace

  set e := prodTorusEquiv θ₁ θ₂ δ₁ δ₂ with he
  obtain ⟨τ₁, τ₂, h₁, h₂, hτeq⟩ := exists_isHaarMeasure_prod_eq e τ
  haveI := h₁
  haveI := h₂

  obtain ⟨ψ₁, hψ₁, hψ₁c, hψ₁1⟩ := exists_bump_eq_one (hΨc.image continuous_fst)
  obtain ⟨ψ₂, hψ₂, hψ₂c, hψ₂1⟩ := exists_bump_eq_one (hΨc.image continuous_snd)
  obtain ⟨W₁, hW₁, hW₁0, hW₁c, hW₁1⟩ := hsec₁ τ₁ h₁ (hinv₁ τ₁ h₁) ψ₁ hψ₁ hψ₁c
  obtain ⟨W₂, hW₂, hW₂0, hW₂c, hW₂1⟩ := hsec₂ τ₂ h₂ (hinv₂ τ₂ h₂) ψ₂ hψ₂ hψ₂c
  refine ⟨fun x => W₁ x.1 * W₂ x.2, (hW₁.comp continuous_fst).mul (hW₂.comp continuous_snd),
    fun x => mul_nonneg (hW₁0 _) (hW₂0 _), hasCompactSupport_prodWeights hW₁c hW₂c, fun x hx => ?_⟩

  have hmem : x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x ∈ tsupport Ψ := subset_tsupport Ψ hx
  have hp1 : (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x).1 = x.1⁻¹ * δ₁ * θ₁ x.1 := rfl
  have hp2 : (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x).2 = x.2⁻¹ * δ₂ * θ₂ x.2 := rfl
  have hne₁ : ψ₁ (x.1⁻¹ * δ₁ * θ₁ x.1) ≠ 0 := by
    rw [hψ₁1 _ ⟨_, hmem, hp1⟩]; exact one_ne_zero
  have hne₂ : ψ₂ (x.2⁻¹ * δ₂ * θ₂ x.2) ≠ 0 := by
    rw [hψ₂1 _ ⟨_, hmem, hp2⟩]; exact one_ne_zero
  have hI₁ := hW₁1 x.1 hne₁
  have hI₂ := hW₂1 x.2 hne₂

  rw [hτeq]
  rw [show (⇑e : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ → _) = ⇑(e.toHomeomorph.toMeasurableEquiv) from rfl,
    MeasureTheory.integral_map_equiv]
  show ∫ s : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂,
      W₁ ((s.1 : H₁) * x.1) * W₂ ((s.2 : H₂) * x.2) ∂(τ₁.prod τ₂) = 1
  rw [MeasureTheory.integral_prod_mul (fun s : sigmaCentralizer θ₁ δ₁ => W₁ ((s : H₁) * x.1))
    (fun s : sigmaCentralizer θ₂ δ₂ => W₂ ((s : H₂) * x.2)), hI₁, hI₂, one_mul]

theorem envelope_section_prod_centralizer
    {G₁ G₂ : Type}
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]
    (γ₁ : G₁) (γ₂ : G₂)
    (τ : @MeasureTheory.Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) (borel _))
    (hτ : @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ)
    (hsec₁ : ∀ τ₁ : @MeasureTheory.Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _),
      @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ₁ →
      ∀ ψ : G₁ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ w₁ : G₁ → ℝ, Continuous w₁ ∧ (∀ x, 0 ≤ w₁ x) ∧ HasCompactSupport w₁ ∧
          ∀ x₁ : G₁, ψ (x₁⁻¹ * γ₁ * x₁) ≠ 0 →
            @MeasureTheory.integral _ ℝ _ _ (borel _) τ₁ (fun t => w₁ ((t : G₁) * x₁)) = 1)
    (hsec₂ : ∀ τ₂ : @MeasureTheory.Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _),
      @MeasureTheory.Measure.IsHaarMeasure _ _ _ (borel _) τ₂ →
      ∀ ψ : G₂ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ w₂ : G₂ → ℝ, Continuous w₂ ∧ (∀ x, 0 ≤ w₂ x) ∧ HasCompactSupport w₂ ∧
          ∀ x₂ : G₂, ψ (x₂⁻¹ * γ₂ * x₂) ≠ 0 →
            @MeasureTheory.integral _ ℝ _ _ (borel _) τ₂ (fun t => w₂ ((t : G₂) * x₂)) = 1)
    (Ψ : G₁ × G₂ → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ w : G₁ × G₂ → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : G₁ × G₂, Ψ (x⁻¹ * (γ₁, γ₂) * x) ≠ 0 →
        @MeasureTheory.integral _ ℝ _ _ (borel _) τ (fun t => w ((t : G₁ × G₂) * x)) = 1 := by
  letI m1 : MeasurableSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := ⟨rfl⟩
  letI m2 : MeasurableSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := ⟨rfl⟩
  letI m12 : MeasurableSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ := hτ
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₁} : Set G₁)) :=
    (isClosed_centralizer γ₁).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₂} : Set G₂)) :=
    (isClosed_centralizer γ₂).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) :=
    (isClosed_centralizer (γ₁, γ₂)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₁} : Set G₁)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₂} : Set G₂)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) := Prod.borelSpace
  set e := prodCentEquiv γ₁ γ₂ with he
  obtain ⟨τ₁, τ₂, h₁, h₂, hτeq⟩ := exists_isHaarMeasure_prod_eq e τ
  haveI := h₁
  haveI := h₂
  obtain ⟨ψ₁, hψ₁, hψ₁c, hψ₁1⟩ := exists_bump_eq_one (hΨc.image continuous_fst)
  obtain ⟨ψ₂, hψ₂, hψ₂c, hψ₂1⟩ := exists_bump_eq_one (hΨc.image continuous_snd)
  obtain ⟨W₁, hW₁, hW₁0, hW₁c, hW₁1⟩ := hsec₁ τ₁ h₁ ψ₁ hψ₁ hψ₁c
  obtain ⟨W₂, hW₂, hW₂0, hW₂c, hW₂1⟩ := hsec₂ τ₂ h₂ ψ₂ hψ₂ hψ₂c
  refine ⟨fun x => W₁ x.1 * W₂ x.2, (hW₁.comp continuous_fst).mul (hW₂.comp continuous_snd),
    fun x => mul_nonneg (hW₁0 _) (hW₂0 _), hasCompactSupport_prodWeights hW₁c hW₂c, fun x hx => ?_⟩
  have hmem : x⁻¹ * (γ₁, γ₂) * x ∈ tsupport Ψ := subset_tsupport Ψ hx
  have hp1 : (x⁻¹ * (γ₁, γ₂) * x).1 = x.1⁻¹ * γ₁ * x.1 := rfl
  have hp2 : (x⁻¹ * (γ₁, γ₂) * x).2 = x.2⁻¹ * γ₂ * x.2 := rfl
  have hne₁ : ψ₁ (x.1⁻¹ * γ₁ * x.1) ≠ 0 := by
    rw [hψ₁1 _ ⟨_, hmem, hp1⟩]; exact one_ne_zero
  have hne₂ : ψ₂ (x.2⁻¹ * γ₂ * x.2) ≠ 0 := by
    rw [hψ₂1 _ ⟨_, hmem, hp2⟩]; exact one_ne_zero
  have hI₁ := hW₁1 x.1 hne₁
  have hI₂ := hW₂1 x.2 hne₂
  rw [hτeq]
  rw [show (⇑e : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) → _) =
      ⇑(e.toHomeomorph.toMeasurableEquiv) from rfl, MeasureTheory.integral_map_equiv]
  show ∫ s : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂),
      W₁ ((s.1 : G₁) * x.1) * W₂ ((s.2 : G₂) * x.2) ∂(τ₁.prod τ₂) = 1
  rw [MeasureTheory.integral_prod_mul (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => W₁ ((s : G₁) * x.1))
    (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => W₂ ((s : G₂) * x.2)), hI₁, hI₂, one_mul]

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent.Env
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped NNReal

namespace GroupOrbital

section ValueIterate

variable {H₁ H₂ : Type} [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁] [LocallyCompactSpace H₁]
  [SecondCountableTopology H₁] [T2Space H₁]
  [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂] [LocallyCompactSpace H₂]
  [SecondCountableTopology H₂] [T2Space H₂]

set_option maxHeartbeats 3200000 in
theorem value_eq_mul_iterated (θ₁ : H₁ →* H₁) (hθ₁ : Continuous θ₁) (θ₂ : H₂ →* H₂) (hθ₂ : Continuous θ₂)
    (δ₁ : H₁) (δ₂ : H₂)
    (μ : @Measure (H₁ × H₂) (borel (H₁ × H₂))) (hμ : @Measure.IsHaarMeasure (H₁ × H₂) _ _ (borel _) μ)
    (μ₁ : @Measure H₁ (borel H₁)) (hμ₁ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) μ₁)
    (μ₂ : @Measure H₂ (borel H₂)) (hμ₂ : @Measure.IsHaarMeasure H₂ _ _ (borel H₂) μ₂)
    (c : ℝ≥0)
    (hc : ∀ g : H₁ × H₂ → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel (H₁ × H₂)) μ g =
        ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel H₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel H₂) μ₂ (fun x₂ => g (x₁, x₂))))
    (τ₁ : @Measure (sigmaCentralizer θ₁ δ₁) (borel _)) (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁)
    (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁)
    (τ₂ : @Measure (sigmaCentralizer θ₂ δ₂) (borel _)) (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂)
    (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂)
    (f : H₁ × H₂ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (W₁ : H₁ → ℝ) (W₂ : H₂ → ℝ) (hW₁c : Continuous W₁) (hW₁0 : ∀ x, 0 ≤ W₁ x) (hW₁s : HasCompactSupport W₁)
    (hW₂c : Continuous W₂) (hW₂0 : ∀ x, 0 ≤ W₂ x) (hW₂s : HasCompactSupport W₂)
    (hn : ∀ (x₁ : H₁) (x₂ : H₂), f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : H₁) * x₁)) = 1 ∧
      @integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : H₂) * x₂)) = 1)
    (I : ℂ)
    (hI : IsValue (θ₁.prodMap θ₂) μ (δ₁, δ₂)
      (@Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) (prodTorusEquiv θ₁ θ₂ δ₁ δ₂)
        (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)) f I) :
    I = ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel H₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel H₂) μ₂ (fun x₂ =>
          f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) * ((W₁ x₁ * W₂ x₂ : ℝ) : ℂ))) := by
  letI mH₁ : MeasurableSpace H₁ := borel _; haveI : BorelSpace H₁ := ⟨rfl⟩
  letI mH₂ : MeasurableSpace H₂ := borel _; haveI : BorelSpace H₂ := ⟨rfl⟩
  letI mH : MeasurableSpace (H₁ × H₂) := borel _; haveI : BorelSpace (H₁ × H₂) := ⟨rfl⟩
  letI mT₁ : MeasurableSpace (sigmaCentralizer θ₁ δ₁) := borel _; haveI : BorelSpace (sigmaCentralizer θ₁ δ₁) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (sigmaCentralizer θ₂ δ₂) := borel _; haveI : BorelSpace (sigmaCentralizer θ₂ δ₂) := ⟨rfl⟩
  letI mT : MeasurableSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI := hμ; haveI := hτ₁; haveI := hτ₂; haveI := hτ₁i; haveI := hτ₂i
  have hT₁c := isClosed_sigmaCentralizer hθ₁ δ₁
  have hT₂c := isClosed_sigmaCentralizer hθ₂ δ₂
  haveI : LocallyCompactSpace (sigmaCentralizer θ₁ δ₁) := hT₁c.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer θ₂ δ₂) := hT₂c.locallyCompactSpace
  haveI : SecondCountableTopology (sigmaCentralizer θ₁ δ₁) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer θ₂ δ₂) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SFinite τ₁ := inferInstance
  haveI : SFinite τ₂ := inferInstance
  haveI : BorelSpace (sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂) := Prod.borelSpace

  set τ : Measure (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) :=
    Measure.map (prodTorusEquiv θ₁ θ₂ δ₁ δ₂) (τ₁.prod τ₂) with hτdef
  haveI : (τ₁.prod τ₂).IsHaarMeasure := inferInstance
  haveI hτH : τ.IsHaarMeasure := (prodTorusEquiv θ₁ θ₂ δ₁ δ₂).isHaarMeasure_map _
  haveI hτi : τ.IsInvInvariant := isInvInvariant_map_prod (prodTorusEquiv θ₁ θ₂ δ₁ δ₂) τ₁ τ₂
  have hθ : Continuous (θ₁.prodMap θ₂) := by rw [MonoidHom.coe_prodMap]; exact hθ₁.prodMap hθ₂

  have hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := hf.bounded_above_of_compact_support hfc
  obtain ⟨c', -, hTF⟩ :=
    AutomorphicForm.integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer θ₁ hθ₁ θ₂ hθ₂ δ₁ δ₂
      μ hμ μ₁ hμ₁ μ₂ hμ₂ τ₁ hτ₁ hτ₁i τ₂ hτ₂ hτ₂i (prodTorusEquiv θ₁ θ₂ δ₁ δ₂) (fun p => rfl)
  have hsec := (hTF f hf hfb W₁ W₂ hW₁c hW₁0 hW₁s hW₂c hW₂0 hW₂s hn).1

  obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, rfl⟩ := hI
  have hWm : Measurable (fun x : H₁ × H₂ => W₁ x.1 * W₂ x.2) :=
    ((hW₁c.comp continuous_fst).mul (hW₂c.comp continuous_snd)).measurable
  have hswap := integral_twistedConj_mul_eq_of_sections (θ₁.prodMap θ₂) hθ μ hμ (δ₁, δ₂) τ hτH hτi f hf
    w (fun x => W₁ x.1 * W₂ x.2) hw0 (fun x => mul_nonneg (hW₁0 _) (hW₂0 _)) hwm hWm hw1
    (fun x hx => hsec x hx)
  rw [hswap]

  have hgc : Continuous (fun x : H₁ × H₂ => f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) * ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ)) :=
    (hf.comp ((continuous_inv.mul continuous_const).mul hθ)).mul
      (Complex.continuous_ofReal.comp ((hW₁c.comp continuous_fst).mul (hW₂c.comp continuous_snd)))
  have hgs : HasCompactSupport (fun x : H₁ × H₂ => f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) * ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ)) := by
    refine HasCompactSupport.mul_left ?_
    have h12 : HasCompactSupport (fun x : H₁ × H₂ => W₁ x.1 * W₂ x.2) := by
      refine HasCompactSupport.intro' (hW₁s.prod hW₂s) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
      intro x hx
      rw [Set.mem_prod, not_and_or] at hx
      rcases hx with h | h
      · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
    exact h12.comp_left Complex.ofReal_zero
  rw [hc _ hgc hgs]
  rfl

end ValueIterate
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section RegularInv

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι)

theorem isMulCommutative_twistedCentralizer_of_regular (i : ι) (δ : Hi K L A i)
    (hδ : IsRegularSemisimple (normString K L (A i) σ δ)) :
    IsMulCommutative (sigmaCentralizer (θfam K L σ A i) δ) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hle := Carriers.RegularCentralizer.twistedCentralizer_le_centralizer_normString K L (A i) σ δ
  exact (Carriers.RegularCentralizer.commute_of_mem_centralizer_of_isRegularSemisimple hδ (hle x.2) (hle y.2)).eq

theorem mem_sigmaCentralizer_η'_iff (δ' : ∀ j : {j // j ≠ i₀}, Hi K L A j) (t : ∀ j : {j // j ≠ i₀}, Hi K L A j) :
    t ∈ sigmaCentralizer (η' K L σ A i₀) δ' ↔
      ∀ j : {j // j ≠ i₀}, t j ∈ sigmaCentralizer (θfam K L σ A j) (δ' j) := by
  simp only [mem_sigmaCentralizer_iff]
  constructor
  · intro h j
    have := congrFun h j
    exact this
  · intro h
    funext j
    exact h j

theorem isMulCommutative_sigmaCentralizer_η'_of_regular (δ' : ∀ j : {j // j ≠ i₀}, Hi K L A j)
    (hδ' : ∀ j : {j // j ≠ i₀}, IsRegularSemisimple (normString K L (A j) σ (δ' j))) :
    IsMulCommutative (sigmaCentralizer (η' K L σ A i₀) δ') := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  funext j
  have hx := (mem_sigmaCentralizer_η'_iff K L σ A i₀ δ' x).1 x.2 j
  have hy := (mem_sigmaCentralizer_η'_iff K L σ A i₀ δ' y).1 y.2 j
  have hc := (isMulCommutative_twistedCentralizer_of_regular K L σ A j (δ' j) (hδ' j)).is_comm.comm
    (⟨x.1 j, hx⟩ : sigmaCentralizer (θfam K L σ A (j : ι)) (δ' j)) ⟨y.1 j, hy⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem isInvInvariant_of_regular_head (δ₀ : Hi K L A i₀) (hδ₀ : IsRegularSemisimple (normString K L (A i₀) σ δ₀))
    (τ : @Measure (sigmaCentralizer (θfam K L σ A i₀) δ₀) (borel _)) (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) :
    @Measure.IsInvInvariant _ (borel _) _ τ := by
  haveI := isTopologicalGroup_Hi K L A i₀
  haveI := t2Space_Hi K L A i₀
  haveI := secondCountableTopology_Hi K L A i₀
  haveI := locallyCompactSpace_Hi K L A i₀
  exact Carriers.OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _
    (GroupOrbital.isClosed_sigmaCentralizer (continuous_θfam K L σ A i₀) δ₀)
    (isMulCommutative_twistedCentralizer_of_regular K L σ A i₀ δ₀ hδ₀) τ hτ

theorem isInvInvariant_of_regular_tail (δ' : ∀ j : {j // j ≠ i₀}, Hi K L A j)
    (hδ' : ∀ j : {j // j ≠ i₀}, IsRegularSemisimple (normString K L (A j) σ (δ' j)))
    (τ : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _)) (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) :
    @Measure.IsInvInvariant _ (borel _) _ τ := by
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  exact Carriers.OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _
    (GroupOrbital.isClosed_sigmaCentralizer (continuous_η' K L σ A i₀) δ')
    (isMulCommutative_sigmaCentralizer_η'_of_regular K L σ A i₀ δ' hδ') τ hτ

end RegularInv
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

theorem isInvInvariant_of_exists {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (τ₀ : Measure T) [τ₀.IsHaarMeasure] [τ₀.IsInvInvariant] (τ : Measure T) [τ.IsHaarMeasure] :
    τ.IsInvInvariant := by
  have h : τ = τ.haarScalarFactor τ₀ • τ₀ := Measure.isMulLeftInvariant_eq_smul τ τ₀
  refine ⟨?_⟩
  change Measure.map Inv.inv τ = τ
  conv_lhs => rw [h]
  rw [Measure.map_smul, Measure.map_inv_eq_self, ← h]

namespace GroupOrbital

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem section_pullback (e : G ≃ₜ* H) {θ : G →* G} {θ' : H →* H} (he : ∀ x, e (θ x) = θ' (e x)) (δ : G)
    (τ : @Measure (sigmaCentralizer θ δ) (borel _)) (Ψ : G → ℂ) (W : H → ℝ)
    (hW : ∀ z : H, Ψ (e.symm (z⁻¹ * e δ * θ' z)) ≠ 0 →
      @integral _ ℝ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (torusEquiv e he δ) τ)
        (fun t => W ((t : H) * z)) = 1)
    (x : G) (hx : Ψ (x⁻¹ * δ * θ x) ≠ 0) :
    @integral _ ℝ _ _ (borel _) τ (fun t => W (e ((t : G) * x))) = 1 := by
  letI : MeasurableSpace G := borel G; haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace H := borel H; haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer θ δ) := borel _; haveI : BorelSpace (sigmaCentralizer θ δ) := ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer θ' (e δ)) := borel _
  haveI : BorelSpace (sigmaCentralizer θ' (e δ)) := ⟨rfl⟩
  have hx' : Ψ (e.symm ((e x)⁻¹ * e δ * θ' (e x))) ≠ 0 := by
    have : e.symm ((e x)⁻¹ * e δ * θ' (e x)) = x⁻¹ * δ * θ x := by
      rw [← he, ← map_inv, ← map_mul, ← map_mul, e.symm_apply_apply]
    rwa [this]
  have key := hW (e x) hx'
  have hmap : @Measure.map _ _ (borel _) (borel _) (torusEquiv e he δ) τ =
      Measure.map ((torusEquiv e he δ).toHomeomorph.toMeasurableEquiv) τ := rfl
  rw [hmap, integral_map_equiv] at key
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) key
  show W (e ((t : G) * x)) = W ((e t : H) * e x)
  rw [map_mul]

theorem sectionC_pullback (e : G ≃ₜ* H) (γ : G)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set G)) (borel _)) (Ψ : G → ℂ) (w : H → ℝ)
    (hw : ∀ z : H, Ψ (e.symm (z⁻¹ * e γ * z)) ≠ 0 →
      @integral _ ℝ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (centTransport e γ) τ)
        (fun t => w ((t : H) * z)) = 1)
    (x : G) (hx : Ψ (x⁻¹ * γ * x) ≠ 0) :
    @integral _ ℝ _ _ (borel _) τ (fun t => w (e ((t : G) * x))) = 1 := by
  letI : MeasurableSpace G := borel G; haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace H := borel H; haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set G)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set G)) := ⟨rfl⟩
  letI : MeasurableSpace (Subgroup.centralizer ({e γ} : Set H)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({e γ} : Set H)) := ⟨rfl⟩
  have hx' : Ψ (e.symm ((e x)⁻¹ * e γ * (e x))) ≠ 0 := by
    have : e.symm ((e x)⁻¹ * e γ * (e x)) = x⁻¹ * γ * x := by
      rw [← map_inv, ← map_mul, ← map_mul, e.symm_apply_apply]
    rwa [this]
  have key := hw (e x) hx'
  have hmap : @Measure.map _ _ (borel _) (borel _) (centTransport e γ) τ =
      Measure.map ((centTransport e γ).toHomeomorph.toMeasurableEquiv) τ := rfl
  rw [hmap, integral_map_equiv] at key
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) key
  show w (e ((t : G) * x)) = w ((e t : H) * e x)
  rw [map_mul]

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

section StepB

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι) (c : ∀ i, (A i)ˣ)
  (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
  (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
  (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))

include μ hμ hμr

set_option maxHeartbeats 6400000 in
theorem step_B
    (hsecL₀ : ∀ δ₀ : Hi K L A i₀,
      (IsRegularSemisimple (normString K L (A i₀) σ δ₀) ∨
        ∃ d : (L ⊗[K] A i₀)ˣ, IsSigmaConjugate K L (A i₀) σ δ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i₀) σ δ₀) (twistedCentralizerBorel K L (A i₀) σ δ₀),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i₀) σ δ₀) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i₀) σ δ₀) _ τ' →
      ∀ φ : Hi K L A i₀ → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : Hi K L A i₀ → ℝ, IsTwistedSectionFnOn K L (A i₀) σ δ₀ τ' φ W ∧ Continuous W)
    (ihB : ∀ (δ' y' : (∀ j : {j // j ≠ i₀}, Hi K L A j)),
      (∀ j : {j // j ≠ i₀}, IsNormConjugator K L (A j) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c j)) (δ' j) (y' j)) →
      ∀ (τ₂ : @Measure (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _))
        (τ₂' : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ₂ → @Measure.IsHaarMeasure _ _ _ (borel _) τ₂' →
        @Measure.IsInvInvariant _ (borel _) _ τ₂' →
        @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
            (fun t : sigmaCentralizer (η' K L σ A i₀) δ' => y'⁻¹ * (t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * y') τ₂' =
          @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
            (fun s : Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j)) => Φ' K L A i₀ (s : (∀ j : {j // j ≠ i₀}, Gi A j))) τ₂ →
        ∀ Ψ : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : (∀ j : {j // j ≠ i₀}, Hi K L A j), Ψ (x⁻¹ * δ' * (η' K L σ A i₀) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ₂' (fun t => W ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x)) = 1)
    (δ y : (∀ i, Hi K L A i))
    (hnc : ∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i))
    (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : (∀ i, Gi A i))} : Set (∀ i, Gi A i))) (borel _))
    (τ' : @Measure (sigmaCentralizer (etaPi K L σ A) δ) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ) (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'i : @Measure.IsInvInvariant _ (borel _) _ τ')
    (hcpl : @Measure.map _ _ (borel _) (borel (∀ i, Hi K L A i))
        (fun t : sigmaCentralizer (etaPi K L σ A) δ => y⁻¹ * (t : (∀ i, Hi K L A i)) * y) τ' =
      @Measure.map _ _ (borel _) (borel (∀ i, Hi K L A i))
        (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : (∀ i, Gi A i))} : Set (∀ i, Gi A i)) => PhiPi K L A (s : (∀ i, Gi A i))) τ)
    (Ψ : (∀ i, Hi K L A i) → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ W : (∀ i, Hi K L A i) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : (∀ i, Hi K L A i), Ψ (x⁻¹ * δ * (etaPi K L σ A) x) ≠ 0 →
        @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : (∀ i, Hi K L A i)) * x)) = 1 := by
  haveI := fun i => locallyCompactSpace_Gi A i
  haveI := fun i => secondCountableTopology_Gi A i
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i

  obtain ⟨τ₁, τ₂, τ₁', τ₂', hτ₁, hτ₂, hτ₁', hτ₂', hτbeq, hτb'eq, hc₁, hc₂⟩ :=
    step_split K L σ A i₀ _ δ y τ τ' hτ hτ' hcpl

  have hinv1 := (step_inv_head K L σ A i₀ μ hμ hμr (c i₀) (δ i₀) (y i₀) τ₁ τ₁' hτ₁ hc₁).2
  have hinv2 := (step_inv_tail K L σ A i₀ μ hμ hμr c (fun j => δ j) (fun j => y j) τ₂ τ₂' hτ₂ hc₂).2

  letI mT₁ : MeasurableSpace (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) := borel _
  haveI : BorelSpace (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) := borel _
  haveI : BorelSpace (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) := ⟨rfl⟩
  letI mC₂ : MeasurableSpace (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := ⟨rfl⟩
  have hT₁c := GroupOrbital.isClosed_sigmaCentralizer (continuous_θfam K L σ A i₀) (δ i₀)
  have hT₂c := GroupOrbital.isClosed_sigmaCentralizer (continuous_η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)
  haveI : LocallyCompactSpace (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) := hT₁c.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) := hT₂c.locallyCompactSpace
  haveI : SecondCountableTopology (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI := hτ₁'; haveI := hτ₂'; haveI := hinv1; haveI := hinv2; haveI := hτ₂
  have hinv₁ : ∀ τ₁'' : @Measure (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁'' → @Measure.IsInvInvariant _ (borel _) _ τ₁'' := by
    intro τ₁'' h; haveI := h; exact isInvInvariant_of_exists τ₁' τ₁''
  have hinv₂ : ∀ τ₂'' : @Measure (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₂'' → @Measure.IsInvInvariant _ (borel _) _ τ₂'' := by
    intro τ₂'' h; haveI := h; exact isInvInvariant_of_exists τ₂' τ₂''

  have hsc : ∃ d : (L ⊗[K] A i₀)ˣ, IsSigmaConjugate K L (A i₀) σ (δ i₀) (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by
    letI mC₁ : MeasurableSpace
        (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)} : Set (Gi A i₀))) := borel _
    haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)} : Set (Gi A i₀))) := ⟨rfl⟩
    haveI := hτ₁
    exact AutomorphicForm.exists_isSigmaConjugate_scalar_of_coupled K L σ (A i₀)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)) ⟨c i₀, rfl⟩ (δ i₀) (y i₀) τ₁ τ₁' inferInstance hc₁

  have hsec₁ : ∀ τ₁'' : @Measure (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁'' → @Measure.IsInvInvariant _ (borel _) _ τ₁'' →
      ∀ ψ : Hi K L A i₀ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ W₁ : Hi K L A i₀ → ℝ, Continuous W₁ ∧ (∀ x, 0 ≤ W₁ x) ∧ HasCompactSupport W₁ ∧
          ∀ x₁ : Hi K L A i₀, ψ (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ₁'' (fun t => W₁ ((t : Hi K L A i₀) * x₁)) = 1 := by
    intro τ₁'' h1 h2 ψ hψ hψc
    obtain ⟨W₁, ⟨h0, -, hcs, hn⟩, hW₁c⟩ := hsecL₀ (δ i₀) (Or.inr hsc) τ₁'' h1 h2 ψ hψ hψc
    exact ⟨W₁, hW₁c, h0, hcs, hn⟩

  have hsec₂ : ∀ τ₂'' : @Measure (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₂'' → @Measure.IsInvInvariant _ (borel _) _ τ₂'' →
      ∀ ψ : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ W₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℝ, Continuous W₂ ∧ (∀ x, 0 ≤ W₂ x) ∧ HasCompactSupport W₂ ∧
          ∀ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), ψ (x₂⁻¹ * (fun j : {j // j ≠ i₀} => δ j) * (η' K L σ A i₀) x₂) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ₂'' (fun t => W₂ ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x₂)) = 1 := by
    intro τ₂'' h1 h2 ψ hψ hψc
    haveI := h1
    set s : ℝ≥0 := Measure.haarScalarFactor τ₂'' τ₂' with hs
    have hs0 : s ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure τ₂'' τ₂').ne'
    have heq : τ₂'' = s • τ₂' := Measure.isMulLeftInvariant_eq_smul τ₂'' τ₂'
    have hτ₂s : @Measure.IsHaarMeasure _ _ _ (borel _) ((s : ℝ≥0∞) • τ₂) :=
      Measure.IsHaarMeasure.smul τ₂ (by exact_mod_cast hs0) ENNReal.coe_ne_top
    have hc₂s : @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
        (fun t : sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j) =>
          (fun j : {j // j ≠ i₀} => y j)⁻¹ * (t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * (fun j : {j // j ≠ i₀} => y j)) τ₂'' =
      @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
        (fun s' : Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j)) => Φ' K L A i₀ (s' : (∀ j : {j // j ≠ i₀}, Gi A j)))
          ((s : ℝ≥0∞) • τ₂) := by
      rw [heq, Measure.map_smul, Measure.map_smul, hc₂]
      rfl
    exact ihB (fun j => δ j) (fun j => y j) (fun j => hnc j) ((s : ℝ≥0∞) • τ₂) τ₂'' hτ₂s h1 h2 hc₂s ψ hψ hψc

  have hτb' : @Measure.IsHaarMeasure _ _ _ (borel _)
      (@Measure.map _ _ (borel _) (borel _) (GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ) τ') := by
    letI m1 : MeasurableSpace (sigmaCentralizer (etaPi K L σ A) δ) := borel _
    haveI : BorelSpace (sigmaCentralizer (etaPi K L σ A) δ) := ⟨rfl⟩
    letI m2 : MeasurableSpace
        (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ δ)) := borel _
    haveI : BorelSpace (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ δ)) := ⟨rfl⟩
    haveI := hτ'
    exact (GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ).isHaarMeasure_map τ'
  have hΨb : Continuous (Ψ ∘ (eH K L A i₀).symm) := hΨ.comp (eH K L A i₀).symm.continuous
  have hΨbc : HasCompactSupport (Ψ ∘ (eH K L A i₀).symm) :=
    hΨc.comp_isClosedEmbedding (eH K L A i₀).symm.toHomeomorph.isClosedEmbedding
  obtain ⟨Wb, hWbc, hWb0, hWbs, hWb1⟩ := S30SemilocalCent.Env.envelope_section_prod (θfam K L σ A i₀)
    (continuous_θfam K L σ A i₀) (η' K L σ A i₀) (continuous_η' K L σ A i₀) (δ i₀) (fun j : {j // j ≠ i₀} => δ j)
    _ hτb' hinv₁ hinv₂ hsec₁ hsec₂ (Ψ ∘ (eH K L A i₀).symm) hΨb hΨbc
  refine ⟨Wb ∘ eH K L A i₀, hWbc.comp (eH K L A i₀).continuous, fun x => hWb0 _,
    hWbs.comp_isClosedEmbedding (eH K L A i₀).toHomeomorph.isClosedEmbedding, fun x hx => ?_⟩
  exact GroupOrbital.section_pullback (eH K L A i₀) (eH_etaPi K L σ A i₀) δ τ' Ψ Wb hWb1 x hx

end StepB
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped NNReal

namespace GroupOrbital

section ValueIterateC

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [T2Space G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
  [SecondCountableTopology G₂] [T2Space G₂]

set_option maxHeartbeats 3200000 in
theorem valueC_eq_mul_iterated (γ₁ : G₁) (γ₂ : G₂)
    (μ : @Measure (G₁ × G₂) (borel (G₁ × G₂))) (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel G₁)) (hμ₁ : @Measure.IsHaarMeasure G₁ _ _ (borel G₁) μ₁)
    (μ₂ : @Measure G₂ (borel G₂)) (hμ₂ : @Measure.IsHaarMeasure G₂ _ _ (borel G₂) μ₂)
    (c : ℝ≥0)
    (hc : ∀ g : G₁ × G₂ → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel (G₁ × G₂)) μ g =
        ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ => g (x₁, x₂))))
    (τ₁ : @Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _)) (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁)
    (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁)
    (τ₂ : @Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _)) (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂)
    (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂)
    (f : G₁ × G₂ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (W₁ : G₁ → ℝ) (W₂ : G₂ → ℝ) (hW₁c : Continuous W₁) (hW₁0 : ∀ x, 0 ≤ W₁ x) (hW₁s : HasCompactSupport W₁)
    (hW₂c : Continuous W₂) (hW₂0 : ∀ x, 0 ≤ W₂ x) (hW₂s : HasCompactSupport W₂)
    (hn : ∀ (x₁ : G₁) (x₂ : G₂), f (x₁⁻¹ * γ₁ * x₁, x₂⁻¹ * γ₂ * x₂) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : G₁) * x₁)) = 1 ∧
      @integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : G₂) * x₂)) = 1)
    (I : ℂ)
    (hI : IsValueC μ (γ₁, γ₂)
      (@Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) (prodCentEquiv γ₁ γ₂)
        (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)) f I) :
    I = ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ =>
          f (x₁⁻¹ * γ₁ * x₁, x₂⁻¹ * γ₂ * x₂) * ((W₁ x₁ * W₂ x₂ : ℝ) : ℂ))) := by
  letI mG₁ : MeasurableSpace G₁ := borel _; haveI : BorelSpace G₁ := ⟨rfl⟩
  letI mG₂ : MeasurableSpace G₂ := borel _; haveI : BorelSpace G₂ := ⟨rfl⟩
  letI mG : MeasurableSpace (G₁ × G₂) := borel _; haveI : BorelSpace (G₁ × G₂) := ⟨rfl⟩
  letI mT₁ : MeasurableSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := ⟨rfl⟩
  letI mT : MeasurableSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := ⟨rfl⟩
  haveI := hμ; haveI := hτ₁; haveI := hτ₂; haveI := hτ₁i; haveI := hτ₂i
  have hT₁c := isClosed_centralizer γ₁
  have hT₂c := isClosed_centralizer γ₂
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := hT₁c.locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := hT₂c.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₁} : Set G₁)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₂} : Set G₂)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SFinite τ₁ := inferInstance
  haveI : SFinite τ₂ := inferInstance
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) := Prod.borelSpace
  set τ : Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) :=
    Measure.map (prodCentEquiv γ₁ γ₂) (τ₁.prod τ₂) with hτdef
  haveI : (τ₁.prod τ₂).IsHaarMeasure := inferInstance
  haveI hτH : τ.IsHaarMeasure := (prodCentEquiv γ₁ γ₂).isHaarMeasure_map _
  haveI hτi : τ.IsInvInvariant := isInvInvariant_map_prod (prodCentEquiv γ₁ γ₂) τ₁ τ₂

  have hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := hf.bounded_above_of_compact_support hfc
  obtain ⟨c', -, hTF⟩ := fubini_centralizer γ₁ γ₂ μ hμ μ₁ hμ₁ μ₂ hμ₂ τ₁ hτ₁ hτ₁i τ₂ hτ₂ hτ₂i
  have hsec := (hTF f hf hfb W₁ W₂ hW₁c hW₁0 hW₁s hW₂c hW₂0 hW₂s hn).1
  obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, rfl⟩ := hI
  have hWm : Measurable (fun x : G₁ × G₂ => W₁ x.1 * W₂ x.2) :=
    ((hW₁c.comp continuous_fst).mul (hW₂c.comp continuous_snd)).measurable
  have hswap := integral_conj_mul_eq_of_sections μ hμ (γ₁, γ₂) τ hτH hτi f hf
    w (fun x => W₁ x.1 * W₂ x.2) hw0 (fun x => mul_nonneg (hW₁0 _) (hW₂0 _)) hwm hWm hw1
    (fun x hx => hsec x hx)
  rw [hswap]
  have hgc : Continuous (fun x : G₁ × G₂ => f (x⁻¹ * (γ₁, γ₂) * x) * ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ)) :=
    (hf.comp ((continuous_inv.mul continuous_const).mul continuous_id)).mul
      (Complex.continuous_ofReal.comp ((hW₁c.comp continuous_fst).mul (hW₂c.comp continuous_snd)))
  have hgs : HasCompactSupport (fun x : G₁ × G₂ => f (x⁻¹ * (γ₁, γ₂) * x) * ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ)) := by
    refine HasCompactSupport.mul_left ?_
    have h12 : HasCompactSupport (fun x : G₁ × G₂ => W₁ x.1 * W₂ x.2) := by
      refine HasCompactSupport.intro' (hW₁s.prod hW₂s) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
      intro x hx
      rw [Set.mem_prod, not_and_or] at hx
      rcases hx with h | h
      · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
    exact h12.comp_left Complex.ofReal_zero
  rw [hc _ hgc hgs]
  rfl

end ValueIterateC
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end GroupOrbital
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

section StepSections

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι)

theorem step_CK
    (hsecK₀ : ∀ γ₀ : Gi A i₀, IsRegularSemisimple γ₀ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) (centralizerBorel (A i₀) γ₀),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i₀) γ₀) τ →
      ∀ f : Gi A i₀ → ℂ, Continuous f → HasCompactSupport f →
        ∃ w : Gi A i₀ → ℝ, IsSectionFnOn (A i₀) γ₀ τ f w ∧ Continuous w)
    (ihCK : ∀ (γ' : (∀ j : {j // j ≠ i₀}, Gi A j)), (∀ j : {j // j ≠ i₀}, IsRegularSemisimple (γ' j)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ →
        ∀ Ψ : (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ w : (∀ j : {j // j ≠ i₀}, Gi A j) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
        ∀ x : (∀ j : {j // j ≠ i₀}, Gi A j), Ψ (x⁻¹ * γ' * x) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : (∀ j : {j // j ≠ i₀}, Gi A j)) * x)) = 1)
    (γ : (∀ i, Gi A i)) (hγ : ∀ i, IsRegularSemisimple (γ i))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) (borel _)) (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ)
    (Ψ : (∀ i, Gi A i) → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ w : (∀ i, Gi A i) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
        ∀ x : (∀ i, Gi A i), Ψ (x⁻¹ * γ * x) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : (∀ i, Gi A i)) * x)) = 1 := by
  classical
  haveI := fun i => locallyCompactSpace_Gi A i
  haveI := fun i => secondCountableTopology_Gi A i

  letI m0 : MeasurableSpace (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) := ⟨rfl⟩
  letI mb' : MeasurableSpace
      (Subgroup.centralizer ({(γ i₀, fun j : {j // j ≠ i₀} => γ j)} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) :=
    borel _
  haveI : BorelSpace
      (Subgroup.centralizer ({(γ i₀, fun j : {j // j ≠ i₀} => γ j)} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) :=
    ⟨rfl⟩
  haveI := hτ

  set eb : Subgroup.centralizer ({γ} : Set (∀ i, Gi A i)) ≃ₜ*
      Subgroup.centralizer ({(γ i₀, fun j : {j // j ≠ i₀} => γ j)} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j)) :=
    GroupOrbital.centTransport (eG A i₀) γ with heb
  set τb : @Measure (Subgroup.centralizer ({(γ i₀, fun j : {j // j ≠ i₀} => γ j)} :
      Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) (borel _) := Measure.map eb τ with hτb_def
  have hτb : Measure.IsHaarMeasure τb := eb.isHaarMeasure_map τ

  have hsec₁ : ∀ τ₁ : @Measure (Subgroup.centralizer ({γ i₀} : Set (Gi A i₀))) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁ →
      ∀ ψ : Gi A i₀ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ w₁ : Gi A i₀ → ℝ, Continuous w₁ ∧ (∀ x, 0 ≤ w₁ x) ∧ HasCompactSupport w₁ ∧
          ∀ x₁ : Gi A i₀, ψ (x₁⁻¹ * γ i₀ * x₁) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ₁ (fun t => w₁ ((t : Gi A i₀) * x₁)) = 1 := by
    intro τ₁ hτ₁ ψ hψ hψc
    obtain ⟨w, ⟨h0, -, hc, h1⟩, hw⟩ := hsecK₀ (γ i₀) (hγ i₀) τ₁ hτ₁ ψ hψ hψc
    exact ⟨w, hw, h0, hc, h1⟩
  obtain ⟨wb, hwb, hwb0, hwbc, hwb1⟩ :=
    Env.envelope_section_prod_centralizer (γ i₀) (fun j : {j // j ≠ i₀} => γ j) τb hτb
      hsec₁ (ihCK (fun j : {j // j ≠ i₀} => γ j) (fun j => hγ j))
      (Ψ ∘ (eG A i₀).symm) (hΨ.comp (eG A i₀).symm.continuous)
      (hΨc.comp_homeomorph (eG A i₀).symm.toHomeomorph)
  refine ⟨wb ∘ eG A i₀, hwb.comp (eG A i₀).continuous, fun x => hwb0 _,
    hwbc.comp_isClosedEmbedding (eG A i₀).toHomeomorph.isClosedEmbedding, fun x hx => ?_⟩

  have hx' : (Ψ ∘ (eG A i₀).symm) ((eG A i₀ x)⁻¹ * (γ i₀, fun j : {j // j ≠ i₀} => γ j) * eG A i₀ x) ≠ 0 := by
    have : (eG A i₀).symm ((eG A i₀ x)⁻¹ * (γ i₀, fun j : {j // j ≠ i₀} => γ j) * eG A i₀ x) = x⁻¹ * γ * x := by
      rw [show ((γ i₀, fun j : {j // j ≠ i₀} => γ j) : Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j) = eG A i₀ γ from rfl,
        ← map_inv, ← map_mul, ← map_mul, (eG A i₀).symm_apply_apply]
    simpa only [Function.comp_apply, this] using hx
  have key := hwb1 (eG A i₀ x) hx'
  rw [show τb = Measure.map (eb.toHomeomorph.toMeasurableEquiv) τ from rfl,
    integral_map_equiv] at key
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)) key
  show wb (eG A i₀ ((s : ∀ i, Gi A i) * x)) = wb ((eb s : Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j) * eG A i₀ x)
  rw [map_mul]
  rfl

theorem step_CL
    (hsecL₀ : ∀ δ₀ : Hi K L A i₀,
      (IsRegularSemisimple (normString K L (A i₀) σ δ₀) ∨
        ∃ d : (L ⊗[K] A i₀)ˣ, IsSigmaConjugate K L (A i₀) σ δ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i₀) σ δ₀) (twistedCentralizerBorel K L (A i₀) σ δ₀),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i₀) σ δ₀) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i₀) σ δ₀) _ τ' →
      ∀ φ : Hi K L A i₀ → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : Hi K L A i₀ → ℝ, IsTwistedSectionFnOn K L (A i₀) σ δ₀ τ' φ W ∧ Continuous W)
    (ihCL : ∀ (δ' : (∀ j : {j // j ≠ i₀}, Hi K L A j)), (∀ j : {j // j ≠ i₀}, IsRegularSemisimple (normString K L (A j) σ (δ' j))) →
      ∀ (τ' : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
        ∀ Ψ : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : (∀ j : {j // j ≠ i₀}, Hi K L A j), Ψ (x⁻¹ * δ' * (η' K L σ A i₀) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x)) = 1)
    (δ : (∀ i, Hi K L A i)) (hδ : ∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i)))
    (τ' : @Measure (sigmaCentralizer (etaPi K L σ A) δ) (borel _)) (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'i : @Measure.IsInvInvariant _ (borel _) _ τ')
    (Ψ : (∀ i, Hi K L A i) → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ W : (∀ i, Hi K L A i) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : (∀ i, Hi K L A i), Ψ (x⁻¹ * δ * (etaPi K L σ A) x) ≠ 0 →
        @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : (∀ i, Hi K L A i)) * x)) = 1 := by
  classical
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i

  letI m0 : MeasurableSpace (sigmaCentralizer (etaPi K L σ A) δ) := borel _
  haveI : BorelSpace (sigmaCentralizer (etaPi K L σ A) δ) := ⟨rfl⟩
  letI mb' : MeasurableSpace
      (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (δ i₀, fun j : {j // j ≠ i₀} => δ j)) := borel _
  haveI : BorelSpace
      (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (δ i₀, fun j : {j // j ≠ i₀} => δ j)) := ⟨rfl⟩
  haveI := hτ'

  set eb : sigmaCentralizer (etaPi K L σ A) δ ≃ₜ*
      sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (δ i₀, fun j : {j // j ≠ i₀} => δ j) :=
    GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ with heb
  set τb : @Measure (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀))
      (δ i₀, fun j : {j // j ≠ i₀} => δ j)) (borel _) := Measure.map eb τ' with hτb_def
  have hτb : Measure.IsHaarMeasure τb := eb.isHaarMeasure_map τ'

  have hsec₁ : ∀ τ₁ : @Measure (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁ → @Measure.IsInvInvariant _ (borel _) _ τ₁ →
      ∀ ψ : Hi K L A i₀ → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∃ W₁ : Hi K L A i₀ → ℝ, Continuous W₁ ∧ (∀ x, 0 ≤ W₁ x) ∧ HasCompactSupport W₁ ∧
          ∀ x₁ : Hi K L A i₀, ψ (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : Hi K L A i₀) * x₁)) = 1 := by
    intro τ₁ hτ₁ hi₁ ψ hψ hψc
    obtain ⟨W, ⟨h0, -, hc, h1⟩, hW⟩ := hsecL₀ (δ i₀) (Or.inl (hδ i₀)) τ₁ hτ₁ hi₁ ψ hψ hψc
    exact ⟨W, hW, h0, hc, h1⟩
  obtain ⟨Wb, hWb, hWb0, hWbc, hWb1⟩ :=
    Env.envelope_section_prod (θfam K L σ A i₀) (continuous_θfam K L σ A i₀) (η' K L σ A i₀)
      (continuous_η' K L σ A i₀) (δ i₀) (fun j : {j // j ≠ i₀} => δ j) τb hτb
      (fun τ₁ hτ₁ => isInvInvariant_of_regular_head K L σ A i₀ (δ i₀) (hδ i₀) τ₁ hτ₁)
      (fun τ₂ hτ₂ => isInvInvariant_of_regular_tail K L σ A i₀ (fun j : {j // j ≠ i₀} => δ j) (fun j => hδ j) τ₂ hτ₂)
      hsec₁ (ihCL (fun j : {j // j ≠ i₀} => δ j) (fun j => hδ j))
      (Ψ ∘ (eH K L A i₀).symm) (hΨ.comp (eH K L A i₀).symm.continuous)
      (hΨc.comp_homeomorph (eH K L A i₀).symm.toHomeomorph)
  refine ⟨Wb ∘ eH K L A i₀, hWb.comp (eH K L A i₀).continuous, fun x => hWb0 _,
    hWbc.comp_isClosedEmbedding (eH K L A i₀).toHomeomorph.isClosedEmbedding, fun x hx => ?_⟩

  have hx' : (Ψ ∘ (eH K L A i₀).symm)
      ((eH K L A i₀ x)⁻¹ * (δ i₀, fun j : {j // j ≠ i₀} => δ j) *
        ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ x)) ≠ 0 := by
    have : (eH K L A i₀).symm ((eH K L A i₀ x)⁻¹ * (δ i₀, fun j : {j // j ≠ i₀} => δ j) *
        ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (eH K L A i₀ x)) = x⁻¹ * δ * etaPi K L σ A x := by
      rw [show ((δ i₀, fun j : {j // j ≠ i₀} => δ j) : Hi K L A i₀ × ∀ j : {j // j ≠ i₀}, Hi K L A j) =
          eH K L A i₀ δ from rfl, ← eH_etaPi K L σ A i₀, ← map_inv, ← map_mul, ← map_mul,
        (eH K L A i₀).symm_apply_apply]
    simpa only [Function.comp_apply, this] using hx
  have key := hWb1 (eH K L A i₀ x) hx'
  rw [show τb = Measure.map (eb.toHomeomorph.toMeasurableEquiv) τ' from rfl,
    integral_map_equiv] at key
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)) key
  show Wb (eH K L A i₀ ((s : ∀ i, Hi K L A i) * x)) =
    Wb ((eb s : Hi K L A i₀ × ∀ j : {j // j ≠ i₀}, Hi K L A j) * eH K L A i₀ x)
  rw [map_mul]
  rfl

end StepSections
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open Topology

section PeelSmooth

variable {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
  (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  (Y : ι → Type) [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
  (ε : ∀ i, H i → Y i)

theorem contDiff_piSplitAt_symm :
    ContDiff ℝ (⊤ : ℕ∞) (fun pq : Y i₀ × (∀ j : {j // j ≠ i₀}, Y j) => (Equiv.piSplitAt i₀ Y).symm pq) := by
  rw [contDiff_pi]
  intro j
  by_cases h : j = i₀
  · subst h
    have : (fun pq : Y j × (∀ k : {k // k ≠ j}, Y k) => (Equiv.piSplitAt j Y).symm pq j) = Prod.fst := by
      funext pq
      rw [Equiv.piSplitAt_symm_apply, dif_pos rfl]
    rw [this]
    exact contDiff_fst
  · have : (fun pq : Y i₀ × (∀ k : {k // k ≠ i₀}, Y k) => (Equiv.piSplitAt i₀ Y).symm pq j) =
        fun pq => pq.2 ⟨j, h⟩ := by
      funext pq
      rw [Equiv.piSplitAt_symm_apply, dif_neg h]
    rw [this]
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (∀ k : {k // k ≠ i₀}, Y k) => q ⟨j, h⟩) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun k : {k // k ≠ i₀} => Y k) ⟨j, h⟩).contDiff
    exact h1.comp contDiff_snd

theorem smooth_through_peel (Φ : (∀ i, H i) → ℂ)
    (hΦ : ∃ Φ₁ : (∀ i, Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => ε i (g i))) :
    ∃ Φ₂ : Y i₀ × (∀ j : {j // j ≠ i₀}, Y j) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₂ ∧
      ∀ p : H i₀ × (∀ j : {j // j ≠ i₀}, H j),
        Φ ((GroupOrbital.piSplitEquiv H i₀).symm p) = Φ₂ (ε i₀ p.1, fun j => ε j (p.2 j)) := by
  obtain ⟨Φ₁, hΦ₁, hrep⟩ := hΦ
  refine ⟨fun pq => Φ₁ ((Equiv.piSplitAt i₀ Y).symm pq), hΦ₁.comp (contDiff_piSplitAt_symm i₀ Y), fun p => ?_⟩
  rw [hrep]
  congr 1
  funext j
  show ε j ((Equiv.piSplitAt i₀ H).symm p j) = (Equiv.piSplitAt i₀ Y).symm (ε i₀ p.1, fun j => ε j (p.2 j)) j
  rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply]
  by_cases h : j = i₀
  · subst h
    rw [dif_pos rfl, dif_pos rfl]
  · rw [dif_neg h, dif_neg h]

end PeelSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem integral_ne_zero_exists {X : Type} [MeasurableSpace X] (m : Measure X) (g : X → ℂ)
    (h : ∫ x, g x ∂m ≠ 0) : ∃ x, g x ≠ 0 := by
  by_contra hx
  push_neg at hx
  apply h
  have : g = fun _ => 0 := funext hx
  rw [this, integral_zero]

section StepASM

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι) (c : ∀ i, (A i)ˣ)
  (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
  (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
  (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
  (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))

include hμ hμ'

set_option maxHeartbeats 6400000 in

theorem step_ASM
    (ν : @Measure (∀ i, Gi A i) (borel _)) (hν : @Measure.IsHaarMeasure (∀ i, Gi A i) _ _ (borel _) ν)
    (ν' : @Measure (∀ i, Hi K L A i) (borel _)) (hν' : @Measure.IsHaarMeasure (∀ i, Hi K L A i) _ _ (borel _) ν')
    (ν₂ : @Measure (∀ j : {j // j ≠ i₀}, Gi A j) (borel _)) (hν₂ : @Measure.IsHaarMeasure (∀ j : {j // j ≠ i₀}, Gi A j) _ _ (borel _) ν₂)
    (ν₂' : @Measure (∀ j : {j // j ≠ i₀}, Hi K L A j) (borel _)) (hν₂' : @Measure.IsHaarMeasure (∀ j : {j // j ≠ i₀}, Hi K L A j) _ _ (borel _) ν₂')
    (cK cL : ℝ≥0) (hcK0 : 0 < cK) (hcL0 : 0 < cL)
    (hcK : ∀ g : (Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eG A i₀) ν) g =
        ((cK : ℝ) : ℂ) * @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
          @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ => g (x₁, x₂))))
    (hcL : ∀ g : (Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eH K L A i₀) ν') g =
        ((cL : ℝ) : ℂ) * @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
          @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ => g (x₁, x₂))))
    (F : (∀ i, Gi A i) → ℂ) (hF : Continuous F) (hFc : HasCompactSupport F)
    (Φ : (∀ i, Hi K L A i) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (δ : (∀ i, Hi K L A i))
    (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : (∀ i, Gi A i))} : Set (∀ i, Gi A i))) (borel _))
    (τ' : @Measure (sigmaCentralizer (etaPi K L σ A) δ) (borel _))
    (τ₁ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)} : Set (Gi A i₀))) (borel _))
    (τ₂ : @Measure (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _))
    (τ₁' : @Measure (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) (borel _))
    (τ₂' : @Measure (sigmaCentralizer (η' K L σ A i₀) (fun j : {j // j ≠ i₀} => δ j)) (borel _))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁) (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂)
    (hτ₁' : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁') (hτ₂' : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂')
    (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁) (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂)
    (hτ₁'i : @Measure.IsInvInvariant _ (borel _) _ τ₁') (hτ₂'i : @Measure.IsInvInvariant _ (borel _) _ τ₂')
    (hτbeq : @Measure.map _ _ (borel _) (borel _) (GroupOrbital.centTransport (eG A i₀) (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : (∀ i, Gi A i))) τ =
      @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _)
        (GroupOrbital.prodCentEquiv (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)) (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)))
        (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂))
    (hτb'eq : @Measure.map _ _ (borel _) (borel _) (GroupOrbital.torusEquiv (eH K L A i₀) (eH_etaPi K L σ A i₀) δ) τ' =
      @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _)
        (GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) (δ i₀) (fun j : {j // j ≠ i₀} => δ j))
        (@Measure.prod _ _ (borel _) (borel _) τ₁' τ₂'))

    (ω₀ : (Gi A i₀) → ℝ) (hω₀c : Continuous ω₀) (hω₀0 : ∀ x, 0 ≤ ω₀ x) (hω₀s : HasCompactSupport ω₀)
    (hω₀1 : ∀ x₁ : (Gi A i₀), @integral _ ℝ _ _ (borel _) τ₁ (fun t => ω₀ ((t : (Gi A i₀)) * x₁)) = 1)
    (ω' : (∀ j : {j // j ≠ i₀}, Gi A j) → ℝ) (hω'c : Continuous ω') (hω'0 : ∀ x, 0 ≤ ω' x) (hω's : HasCompactSupport ω')
    (hω'1 : ∀ x₂ : (∀ j : {j // j ≠ i₀}, Gi A j), @integral _ ℝ _ _ (borel _) τ₂ (fun t => ω' ((t : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) = 1)
    (W₀ : (Hi K L A i₀) → ℝ) (hW₀c : Continuous W₀) (hW₀0 : ∀ x, 0 ≤ W₀ x) (hW₀s : HasCompactSupport W₀)
    (hW₀1 : ∀ x₁ : (Hi K L A i₀), (∃ z : (∀ j : {j // j ≠ i₀}, Hi K L A j), Φ ((eH K L A i₀).symm (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁, z)) ≠ 0) →
      @integral _ ℝ _ _ (borel _) τ₁' (fun t => W₀ ((t : (Hi K L A i₀)) * x₁)) = 1)
    (W' : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℝ) (hW'c : Continuous W') (hW'0 : ∀ x, 0 ≤ W' x) (hW's : HasCompactSupport W')
    (hW'1 : ∀ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), (∃ z : (Hi K L A i₀),
        Φ ((eH K L A i₀).symm (z, x₂⁻¹ * (fun j : {j // j ≠ i₀} => δ j) * (η' K L σ A i₀) x₂)) ≠ 0) →
      @integral _ ℝ _ _ (borel _) τ₂' (fun t => W' ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x₂)) = 1)

    (hone : ∀ J J' : ℂ,
      IsTwistedOrbitalIntegralOn K L (A i₀) σ (μ' i₀) (δ i₀) τ₁'
        (fun h : (Hi K L A i₀) => @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
          Φ ((eH K L A i₀).symm (h, x₂⁻¹ * (fun j : {j // j ≠ i₀} => δ j) * (η' K L σ A i₀) x₂)) * (W' x₂ : ℂ))) J' →
      IsOrbitalIntegralOn (A i₀) (μ i₀) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)) τ₁
        (fun g : (Gi A i₀) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ : (∀ j : {j // j ≠ i₀}, Gi A j) =>
          F ((eG A i₀).symm (g, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω' x₂ : ℂ))) J →
      J' = J)
    (I I' : ℂ) (hI' : GroupOrbital.IsValue (etaPi K L σ A) ν' δ τ' Φ I')
    (hI : GroupOrbital.IsValueC ν (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : (∀ i, Gi A i)) τ F I) :
    I' = I := by
  haveI := fun i => locallyCompactSpace_Gi A i
  haveI := fun i => secondCountableTopology_Gi A i
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i
  have hcL0' : ((cL : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcL0.ne'
  have hcK0' : ((cK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcK0.ne'

  have hI'b := GroupOrbital.IsValue.map (eH K L A i₀) (eH_etaPi K L σ A i₀) ν' δ τ' Φ I' hI'
  rw [hτb'eq] at hI'b
  have hνb' : @Measure.IsHaarMeasure _ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eH K L A i₀) ν') := by
    letI : MeasurableSpace (∀ i, Hi K L A i) := borel _; haveI : BorelSpace (∀ i, Hi K L A i) := ⟨rfl⟩
    letI : MeasurableSpace ((Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j)) := borel _; haveI : BorelSpace ((Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j)) := ⟨rfl⟩
    haveI := hν'
    exact (eH K L A i₀).isHaarMeasure_map ν'
  have hΦb : Continuous (Φ ∘ (eH K L A i₀).symm) := hΦ.comp (eH K L A i₀).symm.continuous
  have hΦbc : HasCompactSupport (Φ ∘ (eH K L A i₀).symm) :=
    hΦc.comp_isClosedEmbedding (eH K L A i₀).symm.toHomeomorph.isClosedEmbedding
  have hnL : ∀ (x₁ : (Hi K L A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j)),
      (Φ ∘ (eH K L A i₀).symm) (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁,
        x₂⁻¹ * (fun j : {j // j ≠ i₀} => δ j) * (η' K L σ A i₀) x₂) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₁' (fun t => W₀ ((t : (Hi K L A i₀)) * x₁)) = 1 ∧
      @integral _ ℝ _ _ (borel _) τ₂' (fun t => W' ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x₂)) = 1 :=
    fun x₁ x₂ h => ⟨hW₀1 x₁ ⟨_, h⟩, hW'1 x₂ ⟨_, h⟩⟩
  have eqL := GroupOrbital.value_eq_mul_iterated (θfam K L σ A i₀) (continuous_θfam K L σ A i₀)
    (η' K L σ A i₀) (continuous_η' K L σ A i₀) (δ i₀) (fun j : {j // j ≠ i₀} => δ j) _ hνb'
    (μ' i₀) (hμ' i₀) ν₂' hν₂' cL hcL τ₁' hτ₁' hτ₁'i τ₂' hτ₂' hτ₂'i (Φ ∘ (eH K L A i₀).symm) hΦb hΦbc
    W₀ W' hW₀c hW₀0 hW₀s hW'c hW'0 hW's hnL I' hI'b

  have hIb := GroupOrbital.IsValueC.map (eG A i₀) ν (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : (∀ i, Gi A i)) τ F I hI
  rw [hτbeq] at hIb
  have hνb : @Measure.IsHaarMeasure _ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eG A i₀) ν) := by
    letI : MeasurableSpace (∀ i, Gi A i) := borel _; haveI : BorelSpace (∀ i, Gi A i) := ⟨rfl⟩
    letI : MeasurableSpace ((Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j)) := borel _; haveI : BorelSpace ((Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j)) := ⟨rfl⟩
    haveI := hν
    exact (eG A i₀).isHaarMeasure_map ν
  have hFb : Continuous (F ∘ (eG A i₀).symm) := hF.comp (eG A i₀).symm.continuous
  have hFbc : HasCompactSupport (F ∘ (eG A i₀).symm) :=
    hFc.comp_isClosedEmbedding (eG A i₀).symm.toHomeomorph.isClosedEmbedding
  have hnK : ∀ (x₁ : (Gi A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Gi A j)),
      (F ∘ (eG A i₀).symm) (x₁⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀) * x₁, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₁ (fun t => ω₀ ((t : (Gi A i₀)) * x₁)) = 1 ∧
      @integral _ ℝ _ _ (borel _) τ₂ (fun t => ω' ((t : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) = 1 :=
    fun x₁ x₂ _ => ⟨hω₀1 x₁, hω'1 x₂⟩
  have eqK := GroupOrbital.valueC_eq_mul_iterated (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)) (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) _ hνb
    (μ i₀) (hμ i₀) ν₂ hν₂ cK hcK τ₁ hτ₁ hτ₁i τ₂ hτ₂ hτ₂i (F ∘ (eG A i₀).symm) hFb hFbc
    ω₀ ω' hω₀c hω₀0 hω₀s hω'c hω'0 hω's hnK I hIb

  set Φ₀ : (Hi K L A i₀) → ℂ := fun h => @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
      Φ ((eH K L A i₀).symm (h, x₂⁻¹ * (fun j : {j // j ≠ i₀} => δ j) * (η' K L σ A i₀) x₂)) * (W' x₂ : ℂ)) with hΦ₀
  set F₀ : (Gi A i₀) → ℂ := fun g => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ : (∀ j : {j // j ≠ i₀}, Gi A j) =>
      F ((eG A i₀).symm (g, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω' x₂ : ℂ)) with hF₀
  set J' : ℂ := @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀)
      (fun x₁ => Φ₀ (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁) * (W₀ x₁ : ℂ)) with hJ'
  set J : ℂ := @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀)
      (fun x₁ => F₀ (x₁⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀) * x₁) * (ω₀ x₁ : ℂ)) with hJ

  have hI'J : I' = ((cL : ℝ) : ℂ) * J' := by
    rw [eqL, hJ']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₁ => ?_)
    show (∫ x₂, (Φ ∘ (eH K L A i₀).symm) (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁,
        x₂⁻¹ * (fun j : {j // j ≠ i₀} => δ j) * (η' K L σ A i₀) x₂) * ((W₀ x₁ * W' x₂ : ℝ) : ℂ) ∂ν₂') =
      Φ₀ (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁) * (W₀ x₁ : ℂ)
    rw [hΦ₀, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₂ => ?_)
    simp only [Function.comp_apply, Complex.ofReal_mul]
    ring

  have hIJ : I = ((cL : ℝ) : ℂ) * J := by
    rw [eqK, hJ, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₁ => ?_)
    have hin : (∫ x₂, (F ∘ (eG A i₀).symm) (x₁⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀) * x₁,
          x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂) * ((ω₀ x₁ * ω' x₂ : ℝ) : ℂ) ∂ν₂) =
        (ω₀ x₁ : ℂ) * ∫ x₂, F ((eG A i₀).symm (x₁⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀) * x₁,
          x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω' x₂ : ℂ) ∂ν₂ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      simp only [Function.comp_apply, Complex.ofReal_mul]
      ring
    show ((cK : ℝ) : ℂ) * _ = ((cL : ℝ) : ℂ) * (F₀ _ * _)
    rw [hin, hF₀]
    field_simp

  have hW₀m : Measurable[borel (Hi K L A i₀)] W₀ := by
    letI : MeasurableSpace (Hi K L A i₀) := borel _; haveI : BorelSpace (Hi K L A i₀) := ⟨rfl⟩
    exact hW₀c.measurable
  have hω₀m : Measurable[borel (Gi A i₀)] ω₀ := by
    letI : MeasurableSpace (Gi A i₀) := borel _; haveI : BorelSpace (Gi A i₀) := ⟨rfl⟩
    exact hω₀c.measurable
  have hJ'val : IsTwistedOrbitalIntegralOn K L (A i₀) σ (μ' i₀) (δ i₀) τ₁' Φ₀ J' := by
    refine ⟨W₀, ⟨hW₀0, hW₀m, hW₀s, fun x₁ hx => hW₀1 x₁ ?_⟩, rfl⟩
    obtain ⟨x₂, hx₂⟩ := @integral_ne_zero_exists _ (borel _) ν₂' _ hx
    exact ⟨_, fun h0 => hx₂ (by rw [h0, zero_mul])⟩
  have hJval : IsOrbitalIntegralOn (A i₀) (μ i₀) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)) τ₁ F₀ J :=
    ⟨ω₀, ⟨hω₀0, hω₀m, hω₀s, fun x₁ _ => hω₀1 x₁⟩, rfl⟩
  rw [hI'J, hIJ, hone J J' hJ'val hJval]

end StepASM
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal

section StepONE

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι) (c : ∀ i, (A i)ˣ)
  (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
  (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
  (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
  (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))

include hμ hμ'

set_option maxHeartbeats 6400000 in

theorem step_ONE
    (ν₂ : @Measure (∀ j : {j // j ≠ i₀}, Gi A j) (borel _)) (hν₂ : @Measure.IsHaarMeasure (∀ j : {j // j ≠ i₀}, Gi A j) _ _ (borel _) ν₂)
    (ν₂' : @Measure (∀ j : {j // j ≠ i₀}, Hi K L A j) (borel _)) (hν₂' : @Measure.IsHaarMeasure (∀ j : {j // j ≠ i₀}, Hi K L A j) _ _ (borel _) ν₂')
    (cK cL : ℝ≥0)
    (F : (∀ i, Gi A i) → ℂ) (hF : Continuous F) (hFc : HasCompactSupport F)
    (Φ : (∀ i, Hi K L A i) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hsecK₀ : ∀ γ₀ : Gi A i₀, IsRegularSemisimple γ₀ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) (centralizerBorel (A i₀) γ₀),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i₀) γ₀) τ →
      ∀ f : Gi A i₀ → ℂ, Continuous f → HasCompactSupport f →
        ∃ w : Gi A i₀ → ℝ, IsSectionFnOn (A i₀) γ₀ τ f w ∧ Continuous w)
    (hsecL₀ : ∀ δ₀ : Hi K L A i₀,
      (IsRegularSemisimple (normString K L (A i₀) σ δ₀) ∨
        ∃ d : (L ⊗[K] A i₀)ˣ, IsSigmaConjugate K L (A i₀) σ δ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i₀) σ δ₀) (twistedCentralizerBorel K L (A i₀) σ δ₀),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i₀) σ δ₀) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i₀) σ δ₀) _ τ' →
      ∀ φ : Hi K L A i₀ → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : Hi K L A i₀ → ℝ, IsTwistedSectionFnOn K L (A i₀) σ δ₀ τ' φ W ∧ Continuous W)

    (δ' : (∀ j : {j // j ≠ i₀}, Hi K L A j))
    (τ₂ : @Measure (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _))
    (τ₂' : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _))
    (ω' : (∀ j : {j // j ≠ i₀}, Gi A j) → ℝ) (hω'c : Continuous ω') (hω'0 : ∀ x, 0 ≤ ω' x) (hω's : HasCompactSupport ω')
    (hω'm : Measurable[borel (∀ j : {j // j ≠ i₀}, Gi A j)] ω')
    (hω'1 : ∀ x₂ : (∀ j : {j // j ≠ i₀}, Gi A j), @integral _ ℝ _ _ (borel _) τ₂ (fun t => ω' ((t : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) = 1)
    (W' : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℝ) (hW'c : Continuous W') (hW'0 : ∀ x, 0 ≤ W' x) (hW's : HasCompactSupport W')
    (hW'm : Measurable[borel (∀ j : {j // j ≠ i₀}, Hi K L A j)] W')
    (hW'1 : ∀ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), (∃ z : (Hi K L A i₀),
        Φ ((eH K L A i₀).symm (z, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) ≠ 0) →
      @integral _ ℝ _ _ (borel _) τ₂' (fun t => W' ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x₂)) = 1)

    (hcent : ∀ (γ₀ : (Gi A i₀)) (δ₀ y₀ : (Hi K L A i₀)), IsRegularSemisimple γ₀ →
      IsRegularSemisimple (normString K L (A i₀) σ δ₀) → IsNormConjugator K L (A i₀) σ γ₀ δ₀ y₀ →
      ∀ (τ₀ : @Measure (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) (borel _))
        (τ₀' : @Measure (sigmaCentralizer (θfam K L σ A i₀) δ₀) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ₀ → @Measure.IsHaarMeasure _ _ _ (borel _) τ₀' →
        @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
            (fun t : sigmaCentralizer (θfam K L σ A i₀) δ₀ => y₀⁻¹ * (t : (Hi K L A i₀)) * y₀) τ₀' =
          @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
            (fun s : Subgroup.centralizer ({γ₀} : Set (Gi A i₀)) => φfam K L A i₀ (s : (Gi A i₀))) τ₀ →
      ∀ (ω₀ : (Gi A i₀) → ℝ) (W₀ : (Hi K L A i₀) → ℝ),
      Continuous ω₀ → (∀ x, 0 ≤ ω₀ x) → HasCompactSupport ω₀ →
      (∀ (x₁ : (Gi A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Gi A j)), F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x₂)) ≠ 0 →
        @integral _ ℝ _ _ (borel _) τ₀ (fun t => ω₀ ((t : (Gi A i₀)) * x₁)) = 1) →
      Continuous W₀ → (∀ x, 0 ≤ W₀ x) → HasCompactSupport W₀ →
      (∀ (x₁ : (Hi K L A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j)), Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂)) ≠ 0 →
        @integral _ ℝ _ _ (borel _) τ₀' (fun t => W₀ ((t : (Hi K L A i₀)) * x₁)) = 1) →
      ∀ J J' : ℂ,
        GroupOrbital.IsValue (η' K L σ A i₀) ν₂' δ' τ₂'
          (fun h' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
            Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, h')) * (W₀ x₁ : ℂ))) J' →
        GroupOrbital.IsValueC ν₂ (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) τ₂
          (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
            @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
              F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, g')) * (ω₀ x₁ : ℂ))) J →
        J' = J)

    (hΦ₀c : Continuous (fun h : (Hi K L A i₀) => @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
          Φ ((eH K L A i₀).symm (h, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) * (W' x₂ : ℂ))))
    (hF₀c : Continuous (fun g : (Gi A i₀) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ : (∀ j : {j // j ≠ i₀}, Gi A j) =>
          F ((eG A i₀).symm (g, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω' x₂ : ℂ)))) :
    ∀ δ₀ : (Hi K L A i₀), IsRegularSemisimple (normString K L (A i₀) σ δ₀) →
    ∀ γ₀ ∈ (Set.univ : Set (Gi A i₀)), IsRegularSemisimple γ₀ →
    ∀ y₀ : (Hi K L A i₀), IsNormConjugator K L (A i₀) σ γ₀ δ₀ y₀ →
    ∀ (τ₀ : @Measure (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) (centralizerBorel (A i₀) γ₀))
      (τ₀' : @Measure (twistedCentralizer K L (A i₀) σ δ₀) (twistedCentralizerBorel K L (A i₀) σ δ₀)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i₀) γ₀) τ₀ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i₀) σ δ₀) τ₀' →
      Coupled K L (A i₀) σ γ₀ δ₀ y₀ τ₀ τ₀' →
      ∀ I₀ I₀' : ℂ,
        IsTwistedOrbitalIntegralOn K L (A i₀) σ (μ' i₀) δ₀ τ₀'
          (fun h : (Hi K L A i₀) => @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
            Φ ((eH K L A i₀).symm (h, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) * (W' x₂ : ℂ))) I₀' →
        IsOrbitalIntegralOn (A i₀) (μ i₀) γ₀ τ₀
          (fun g : (Gi A i₀) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ : (∀ j : {j // j ≠ i₀}, Gi A j) =>
            F ((eG A i₀).symm (g, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω' x₂ : ℂ))) I₀ →
        I₀' = I₀ := by
  intro δ₀ hδ₀ γ₀ _ hγ₀ y₀ hy₀ τ₀ τ₀' hτ₀ hτ₀' hcpl₀ I₀ I₀' hI₀' hI₀
  haveI := fun i => locallyCompactSpace_Gi A i
  haveI := fun i => secondCountableTopology_Gi A i
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i
  letI mG₀ : MeasurableSpace (Gi A i₀) := glBorelOf (A i₀); haveI : BorelSpace (Gi A i₀) := borelSpace_glBorelOf _
  letI mH₀ : MeasurableSpace (Hi K L A i₀) := glBorelOf (L ⊗[K] A i₀); haveI : BorelSpace (Hi K L A i₀) := borelSpace_glBorelOf _
  letI mG' : MeasurableSpace (∀ j : {j // j ≠ i₀}, Gi A j) := borel _; haveI : BorelSpace (∀ j : {j // j ≠ i₀}, Gi A j) := ⟨rfl⟩
  letI mH' : MeasurableSpace (∀ j : {j // j ≠ i₀}, Hi K L A j) := borel _; haveI : BorelSpace (∀ j : {j // j ≠ i₀}, Hi K L A j) := ⟨rfl⟩
  haveI := hμ i₀; haveI := hμ' i₀; haveI := hν₂; haveI := hν₂'

  obtain ⟨W₀, ⟨hW₀0, hW₀m, hW₀s, hW₀1⟩, rfl⟩ := hI₀'
  obtain ⟨ω₀, ⟨hω₀0, hω₀m, hω₀s, hω₀1⟩, rfl⟩ := hI₀

  have hτ₀'i := isInvInvariant_of_regular_head K L σ A i₀ δ₀ hδ₀ τ₀' hτ₀'
  have hτ₀i : @Measure.IsInvInvariant _ (borel _) _ τ₀ :=
    Carriers.OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _
      (Carriers.OrbitalCarriers.isClosed_centralizer (A i₀) γ₀)
      (Carriers.RegularCentralizer.isMulCommutative_centralizer_of_isRegularSemisimple hγ₀) τ₀ hτ₀

  set kL : (Hi K L A i₀) → (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ := fun h x₂ =>
    Φ ((eH K L A i₀).symm (h, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) * (W' x₂ : ℂ) with hkL
  set kK : (Gi A i₀) → (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ := fun g x₂ =>
    F ((eG A i₀).symm (g, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω' x₂ : ℂ) with hkK

  have hΦb : Continuous (Φ ∘ (eH K L A i₀).symm) := hΦ.comp (eH K L A i₀).symm.continuous
  have hΦbc : HasCompactSupport (Φ ∘ (eH K L A i₀).symm) :=
    hΦc.comp_isClosedEmbedding (eH K L A i₀).symm.toHomeomorph.isClosedEmbedding
  have hFb : Continuous (F ∘ (eG A i₀).symm) := hF.comp (eG A i₀).symm.continuous
  have hFbc : HasCompactSupport (F ∘ (eG A i₀).symm) :=
    hFc.comp_isClosedEmbedding (eG A i₀).symm.toHomeomorph.isClosedEmbedding
  obtain ⟨ψL, hψLc, hψLs, hψL1⟩ := S30SemilocalCent.Env.exists_bump_eq_one (hΦbc.isCompact.image continuous_fst)
  obtain ⟨ψK, hψKc, hψKs, hψK1⟩ := S30SemilocalCent.Env.exists_bump_eq_one (hFbc.isCompact.image continuous_fst)
  obtain ⟨W₀ₑ, ⟨hW₀ₑ0, hW₀ₑm, hW₀ₑs, hW₀ₑ1⟩, hW₀ₑc⟩ := hsecL₀ δ₀ (Or.inl hδ₀) τ₀' hτ₀' hτ₀'i ψL hψLc hψLs
  obtain ⟨ω₀ₑ, ⟨hω₀ₑ0, hω₀ₑm, hω₀ₑs, hω₀ₑ1⟩, hω₀ₑc⟩ := hsecK₀ γ₀ hγ₀ τ₀ hτ₀ ψK hψKc hψKs
  have hW₀ₑE : ∀ (x₁ : (Hi K L A i₀)) (z : (∀ j : {j // j ≠ i₀}, Hi K L A j)),
      Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, z)) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₀' (fun t => W₀ₑ ((t : (Hi K L A i₀)) * x₁)) = 1 := by
    intro x₁ z hz
    apply hW₀ₑ1 x₁
    rw [hψL1 _ ⟨(x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, z), subset_tsupport _ hz, rfl⟩]
    exact one_ne_zero
  have hω₀ₑE : ∀ (x₁ : (Gi A i₀)) (z : (∀ j : {j // j ≠ i₀}, Gi A j)),
      F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, z)) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₀ (fun t => ω₀ₑ ((t : (Gi A i₀)) * x₁)) = 1 := by
    intro x₁ z hz
    apply hω₀ₑ1 x₁
    rw [hψK1 _ ⟨(x₁⁻¹ * γ₀ * x₁, z), subset_tsupport _ hz, rfl⟩]
    exact one_ne_zero

  have hswL := GroupOrbital.integral_twistedConj_mul_eq_of_sections (θfam K L σ A i₀) (continuous_θfam K L σ A i₀)
    (μ' i₀) (hμ' i₀) δ₀ τ₀' hτ₀' hτ₀'i (fun h => ∫ x₂, kL h x₂ ∂ν₂') hΦ₀c W₀ W₀ₑ hW₀0 hW₀ₑ0 hW₀m hW₀ₑm hW₀1
    (fun x₁ hx => by
      beta_reduce at hx
      obtain ⟨x₂, hx₂⟩ := @integral_ne_zero_exists _ (borel _) ν₂' _ hx
      exact hW₀ₑE x₁ _ (fun h0 => hx₂ (by simp only [hkL]; rw [h0, zero_mul])))
  have hswK := GroupOrbital.integral_conj_mul_eq_of_sections (μ i₀) (hμ i₀) γ₀ τ₀ hτ₀ hτ₀i
    (fun g => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * ∫ x₂, kK g x₂ ∂ν₂) hF₀c ω₀ ω₀ₑ hω₀0 hω₀ₑ0 hω₀m hω₀ₑm hω₀1
    (fun x₁ hx => by
      beta_reduce at hx
      have hx' : (∫ x₂, kK (x₁⁻¹ * γ₀ * x₁) x₂ ∂ν₂) ≠ 0 := fun h0 => hx (by rw [h0, mul_zero])
      obtain ⟨x₂, hx₂⟩ := @integral_ne_zero_exists _ (borel _) ν₂ _ hx'
      exact hω₀ₑE x₁ _ (fun h0 => hx₂ (by simp only [hkK]; rw [h0, zero_mul])))
  rw [hswL, hswK]

  set J' : ℂ := @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
      (@integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
        Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) * (W₀ₑ x₁ : ℂ))) *
      (W' x₂ : ℂ)) with hJ'
  set J : ℂ := @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ : (∀ j : {j // j ≠ i₀}, Gi A j) =>
      ((((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
        F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂)) * (ω₀ₑ x₁ : ℂ))) *
      (ω' x₂ : ℂ)) with hJ

  haveI : BorelSpace ((Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j)) := Prod.borelSpace
  haveI : BorelSpace ((Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j)) := Prod.borelSpace
  have hθc := continuous_θfam K L σ A i₀
  have hη'c := continuous_η' K L σ A i₀
  have hgL : Continuous (fun p : (Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
      Φ ((eH K L A i₀).symm (p.1⁻¹ * δ₀ * (θfam K L σ A i₀) p.1, p.2⁻¹ * δ' * (η' K L σ A i₀) p.2)) *
        (W' p.2 : ℂ) * (W₀ₑ p.1 : ℂ)) := by
    refine ((hΦ.comp ((eH K L A i₀).symm.continuous.comp ?_)).mul
      (Complex.continuous_ofReal.comp (hW'c.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hW₀ₑc.comp continuous_fst))
    exact (((continuous_fst.inv).mul continuous_const).mul (hθc.comp continuous_fst)).prodMk
      (((continuous_snd.inv).mul continuous_const).mul (hη'c.comp continuous_snd))
  have hprodcs : ∀ {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (u : P → ℝ) (v : Q → ℝ)
      (hu : HasCompactSupport u) (hv : HasCompactSupport v) (g : P × Q → ℂ),
      HasCompactSupport (fun p : P × Q => g p * (v p.2 : ℂ) * (u p.1 : ℂ)) := by
    intro P Q _ _ u v hu hv g
    refine HasCompactSupport.intro' (hu.prod hv) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, Complex.ofReal_zero, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h, Complex.ofReal_zero, mul_zero, zero_mul]
  have hgLs := hprodcs W₀ₑ W' hW₀ₑs hW's (fun p : (Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j) =>
      Φ ((eH K L A i₀).symm (p.1⁻¹ * δ₀ * (θfam K L σ A i₀) p.1, p.2⁻¹ * δ' * (η' K L σ A i₀) p.2)))
  have hgK : Continuous (fun p : (Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j) =>
      F ((eG A i₀).symm (p.1⁻¹ * γ₀ * p.1, p.2⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * p.2)) * (ω' p.2 : ℂ) * (ω₀ₑ p.1 : ℂ)) := by
    refine ((hF.comp ((eG A i₀).symm.continuous.comp ?_)).mul
      (Complex.continuous_ofReal.comp (hω'c.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hω₀ₑc.comp continuous_fst))
    exact (((continuous_fst.inv).mul continuous_const).mul continuous_fst).prodMk
      (((continuous_snd.inv).mul continuous_const).mul continuous_snd)
  have hgKs := hprodcs ω₀ₑ ω' hω₀ₑs hω's (fun p : (Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j) =>
      F ((eG A i₀).symm (p.1⁻¹ * γ₀ * p.1, p.2⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * p.2)))

  have hL : (∫ x₁, (∫ x₂, kL (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁) x₂ ∂ν₂') * (W₀ₑ x₁ : ℂ) ∂(μ' i₀)) = J' := by
    have h1 : ∀ x₁, (∫ x₂, kL (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁) x₂ ∂ν₂') * (W₀ₑ x₁ : ℂ) =
        ∫ x₂, kL (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁) x₂ * (W₀ₑ x₁ : ℂ) ∂ν₂' := fun x₁ => by
      rw [← integral_mul_const]
    simp_rw [h1]
    rw [integral_integral_swap ((hgL.integrable_of_hasCompactSupport hgLs).congr ?_)]
    · rw [hJ']
      refine integral_congr_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      beta_reduce
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x₁ => ?_)
      simp only [hkL]
      ring
    · exact Filter.Eventually.of_forall fun p => by
        obtain ⟨a, b⟩ := p
        simp only [hkL, Function.uncurry_apply_pair]
  have hK : (∫ x₁, ((((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * ∫ x₂, kK (x₁⁻¹ * γ₀ * x₁) x₂ ∂ν₂) * (ω₀ₑ x₁ : ℂ) ∂(μ i₀)) = J := by
    have h1 : ∀ x₁, ((((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * ∫ x₂, kK (x₁⁻¹ * γ₀ * x₁) x₂ ∂ν₂) * (ω₀ₑ x₁ : ℂ) =
        (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * ∫ x₂, kK (x₁⁻¹ * γ₀ * x₁) x₂ * (ω₀ₑ x₁ : ℂ) ∂ν₂ := fun x₁ => by
      rw [mul_assoc, ← integral_mul_const]
    simp_rw [h1]
    rw [integral_const_mul, integral_integral_swap ((hgK.integrable_of_hasCompactSupport hgKs).congr ?_)]
    · rw [hJ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      beta_reduce
      rw [mul_assoc, ← integral_mul_const]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x₁ => ?_)
      simp only [hkK]
      ring
    · exact Filter.Eventually.of_forall fun p => by
        obtain ⟨a, b⟩ := p
        simp only [hkK, Function.uncurry_apply_pair]
  rw [hL, hK]

  refine hcent γ₀ δ₀ y₀ hγ₀ hδ₀ hy₀ τ₀ τ₀' hτ₀ hτ₀' hcpl₀ ω₀ₑ W₀ₑ hω₀ₑc hω₀ₑ0 hω₀ₑs hω₀ₑE hW₀ₑc hW₀ₑ0 hW₀ₑs hW₀ₑE
    J J' ?_ ?_
  · refine ⟨W', ⟨hW'0, hW'm, hW's, fun x₂ hx => hW'1 x₂ ?_⟩, by rw [hJ']⟩
    obtain ⟨x₁, hx₁⟩ := @integral_ne_zero_exists _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) _ hx
    exact ⟨_, fun h0 => hx₁ (by rw [h0, zero_mul])⟩
  · refine ⟨ω', ⟨hω'0, hω'm, hω's, fun x₂ _ => hω'1 x₂⟩, by rw [hJ]⟩

end StepONE
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal

section RegFurniture

theorem GroupOrbital.isInvInvariant_map_mulEquiv {T T' : Type}
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (e : T ≃ₜ* T') (τ : Measure T) [τ.IsInvInvariant] : (Measure.map e τ).IsInvInvariant := by
  have hem : Measurable e := e.continuous.measurable
  refine ⟨?_⟩
  change Measure.map Inv.inv (Measure.map e τ) = Measure.map e τ
  rw [Measure.map_map measurable_inv hem]
  have h1 : (Inv.inv ∘ e) = e ∘ (Inv.inv : T → T) := by
    funext p; simp only [Function.comp_apply, map_inv]
  rw [h1, ← Measure.map_map hem measurable_inv]
  congr 1
  exact Measure.map_inv_eq_self τ

theorem Carriers.isMulCommutative_centralizer_pi_of_isRegularSemisimple {κ : Type} (B : κ → Type)
    [∀ k, CommRing (B k)] (γ : ∀ k, GL (Fin 2) (B k)) (hγ : ∀ k, IsRegularSemisimple (γ k)) :
    IsMulCommutative (Subgroup.centralizer ({γ} : Set (∀ k, GL (Fin 2) (B k)))) := by
  refine ⟨⟨fun a b => Subtype.ext (funext fun k => ?_)⟩⟩
  have ha := Subgroup.mem_centralizer_singleton_iff.1 a.2
  have hb := Subgroup.mem_centralizer_singleton_iff.1 b.2
  have hak : a.1 k ∈ Subgroup.centralizer ({γ k} : Set (GL (Fin 2) (B k))) :=
    Subgroup.mem_centralizer_singleton_iff.2 (congrFun ha k)
  have hbk : b.1 k ∈ Subgroup.centralizer ({γ k} : Set (GL (Fin 2) (B k))) :=
    Subgroup.mem_centralizer_singleton_iff.2 (congrFun hb k)
  exact (Carriers.RegularCentralizer.commute_of_mem_centralizer_of_isRegularSemisimple (hγ k) hak hbk).eq

end RegFurniture
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"
namespace S30SemilocalCent

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions NNReal

section StepREG

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
  [∀ i, SecondCountableTopology (A i)] (i₀ : ι)
  (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
  (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
  (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
  (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))

include μ hμ μ' hμ'

set_option maxHeartbeats 3200000 in

theorem step_REG
    (ν : @Measure (∀ i, Gi A i) (borel _)) (hν : @Measure.IsHaarMeasure (∀ i, Gi A i) _ _ (borel _) ν)
    (ν' : @Measure (∀ i, Hi K L A i) (borel _)) (hν' : @Measure.IsHaarMeasure (∀ i, Hi K L A i) _ _ (borel _) ν')
    (ν₂ : @Measure (∀ j : {j // j ≠ i₀}, Gi A j) (borel _)) (hν₂ : @Measure.IsHaarMeasure (∀ j : {j // j ≠ i₀}, Gi A j) _ _ (borel _) ν₂)
    (ν₂' : @Measure (∀ j : {j // j ≠ i₀}, Hi K L A j) (borel _)) (hν₂' : @Measure.IsHaarMeasure (∀ j : {j // j ≠ i₀}, Hi K L A j) _ _ (borel _) ν₂')
    (cK cL : ℝ≥0) (hcK0 : 0 < cK) (hcL0 : 0 < cL)
    (hcK : ∀ g : (Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eG A i₀) ν) g =
        ((cK : ℝ) : ℂ) * @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
          @integral _ ℂ _ _ (borel _) ν₂ (fun x₂ => g (x₁, x₂))))
    (hcL : ∀ g : (Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ, Continuous g → HasCompactSupport g →
      @integral _ ℂ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eH K L A i₀) ν') g =
        ((cL : ℝ) : ℂ) * @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
          @integral _ ℂ _ _ (borel _) ν₂' (fun x₂ => g (x₁, x₂))))
    (F : (∀ i, Gi A i) → ℂ) (hF : Continuous F) (hFc : HasCompactSupport F)
    (Φ : (∀ i, Hi K L A i) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hreg : (∀ (γ : (∀ i, Gi A i)) (δ y : (∀ i, Hi K L A i)),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (∀ i, Gi A i))) (borel _))
        (τ' : @Measure (sigmaCentralizer (etaPi K L σ A) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel (∀ i, Hi K L A i))
            (fun t : sigmaCentralizer (etaPi K L σ A) δ => y⁻¹ * (t : (∀ i, Hi K L A i)) * y) τ' =
          @Measure.map _ _ (borel _) (borel (∀ i, Hi K L A i))
            (fun s : Subgroup.centralizer ({γ} : Set (∀ i, Gi A i)) => PhiPi K L A (s : (∀ i, Gi A i))) τ →
        ∀ I I' : ℂ, GroupOrbital.IsValue (etaPi K L σ A) ν' δ τ' Φ I' → GroupOrbital.IsValueC ν γ τ F I → I' = I))
    (ihCL : (∀ (δ' : (∀ j : {j // j ≠ i₀}, Hi K L A j)), (∀ j : {j // j ≠ i₀}, IsRegularSemisimple (normString K L (A j) σ (δ' j))) →
      ∀ (τ' : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
        ∀ Ψ : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : (∀ j : {j // j ≠ i₀}, Hi K L A j), Ψ (x⁻¹ * δ' * (η' K L σ A i₀) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x)) = 1))
    (ihCK : (∀ (γ' : (∀ j : {j // j ≠ i₀}, Gi A j)), (∀ j : {j // j ≠ i₀}, IsRegularSemisimple (γ' j)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ →
        ∀ Ψ : (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ w : (∀ j : {j // j ≠ i₀}, Gi A j) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
            ∀ x : (∀ j : {j // j ≠ i₀}, Gi A j), Ψ (x⁻¹ * γ' * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : (∀ j : {j // j ≠ i₀}, Gi A j)) * x)) = 1))

    (γ₀ : (Gi A i₀)) (hγ₀ : IsRegularSemisimple γ₀) (δ₀ y₀ : (Hi K L A i₀))
    (hδ₀ : IsRegularSemisimple (normString K L (A i₀) σ δ₀)) (hy₀ : IsNormConjugator K L (A i₀) σ γ₀ δ₀ y₀)
    (τ₀ : @Measure (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) (borel _))
    (τ₀' : @Measure (sigmaCentralizer (θfam K L σ A i₀) δ₀) (borel _))
    (hτ₀ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₀) (hτ₀' : @Measure.IsHaarMeasure _ _ _ (borel _) τ₀')
    (hc₀ : @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
        (fun t : sigmaCentralizer (θfam K L σ A i₀) δ₀ => y₀⁻¹ * (t : (Hi K L A i₀)) * y₀) τ₀' =
      @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
        (fun s : Subgroup.centralizer ({γ₀} : Set (Gi A i₀)) => φfam K L A i₀ (s : (Gi A i₀))) τ₀)
    (ω₀ : (Gi A i₀) → ℝ) (hω₀c : Continuous ω₀) (hω₀0 : ∀ x, 0 ≤ ω₀ x) (hω₀s : HasCompactSupport ω₀)
    (hω₀1 : ∀ (x₁ : (Gi A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Gi A j)), F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x₂)) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₀ (fun t => ω₀ ((t : (Gi A i₀)) * x₁)) = 1)
    (W₀ : (Hi K L A i₀) → ℝ) (hW₀c : Continuous W₀) (hW₀0 : ∀ x, 0 ≤ W₀ x) (hW₀s : HasCompactSupport W₀)
    (hW₀1 : ∀ (x₁ : (Hi K L A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j)), Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂)) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ₀' (fun t => W₀ ((t : (Hi K L A i₀)) * x₁)) = 1) :

    ∀ (γ' : (∀ j : {j // j ≠ i₀}, Gi A j)) (δ' y' : (∀ j : {j // j ≠ i₀}, Hi K L A j)),
      (∀ j : {j // j ≠ i₀}, IsRegularSemisimple (γ' j)) →
      (∀ j : {j // j ≠ i₀}, IsRegularSemisimple (normString K L (A j) σ (δ' j))) →
      (∀ j : {j // j ≠ i₀}, IsNormConjugator K L (A j) σ (γ' j) (δ' j) (y' j)) →
      ∀ (τ₂ : @Measure (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) (borel _))
        (τ₂' : @Measure (sigmaCentralizer (η' K L σ A i₀) δ') (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ₂ → @Measure.IsHaarMeasure _ _ _ (borel _) τ₂' →
        @Measure.IsInvInvariant _ (borel _) _ τ₂' →
        @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
            (fun t : sigmaCentralizer (η' K L σ A i₀) δ' => y'⁻¹ * (t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * y') τ₂' =
          @Measure.map _ _ (borel _) (borel (∀ j : {j // j ≠ i₀}, Hi K L A j))
            (fun s : Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j)) => Φ' K L A i₀ (s : (∀ j : {j // j ≠ i₀}, Gi A j))) τ₂ →
        ∀ J J' : ℂ,
          GroupOrbital.IsValue (η' K L σ A i₀) ν₂' δ' τ₂'
            (fun h' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
              Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, h')) * (W₀ x₁ : ℂ))) J' →
          GroupOrbital.IsValueC ν₂ γ' τ₂
            (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
              @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
                F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, g')) * (ω₀ x₁ : ℂ))) J →
          J' = J := by
  classical
  intro γ' δ' y' hγ' hδ' hy' τ₂ τ₂' hτ₂ hτ₂' hτ₂'i hcpl' J J' hJ' hJ

  haveI := fun i => locallyCompactSpace_Gi A i
  haveI := fun i => secondCountableTopology_Gi A i
  haveI := fun i => isTopologicalGroup_Hi K L A i
  haveI := fun i => t2Space_Hi K L A i
  haveI := fun i => locallyCompactSpace_Hi K L A i
  haveI := fun i => secondCountableTopology_Hi K L A i

  letI mG1 : MeasurableSpace (Gi A i₀) := glBorelOf (A i₀)
  haveI : BorelSpace (Gi A i₀) := borelSpace_glBorelOf (A i₀)
  letI mH1 : MeasurableSpace (Hi K L A i₀) := glBorelOf (L ⊗[K] A i₀)
  haveI : BorelSpace (Hi K L A i₀) := borelSpace_glBorelOf (L ⊗[K] A i₀)
  letI mG2 : MeasurableSpace (∀ j : {j // j ≠ i₀}, Gi A j) := borel _
  haveI : BorelSpace (∀ j : {j // j ≠ i₀}, Gi A j) := ⟨rfl⟩
  letI mH2 : MeasurableSpace (∀ j : {j // j ≠ i₀}, Hi K L A j) := borel _
  haveI : BorelSpace (∀ j : {j // j ≠ i₀}, Hi K L A j) := ⟨rfl⟩
  letI mG : MeasurableSpace (∀ i, Gi A i) := borel _
  haveI : BorelSpace (∀ i, Gi A i) := ⟨rfl⟩
  letI mH : MeasurableSpace (∀ i, Hi K L A i) := borel _
  haveI : BorelSpace (∀ i, Hi K L A i) := ⟨rfl⟩
  letI mGb : MeasurableSpace (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j) := borel _
  haveI : BorelSpace (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j) := ⟨rfl⟩
  letI mHb : MeasurableSpace (Hi K L A i₀ × ∀ j : {j // j ≠ i₀}, Hi K L A j) := borel _
  haveI : BorelSpace (Hi K L A i₀ × ∀ j : {j // j ≠ i₀}, Hi K L A j) := ⟨rfl⟩
  haveI := hμ i₀
  haveI := hμ' i₀
  haveI := hν; haveI := hν'; haveI := hν₂; haveI := hν₂'

  letI mT0 : MeasurableSpace (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) := ⟨rfl⟩
  letI mT0' : MeasurableSpace (sigmaCentralizer (θfam K L σ A i₀) δ₀) := borel _
  haveI : BorelSpace (sigmaCentralizer (θfam K L σ A i₀) δ₀) := ⟨rfl⟩
  letI mT2 : MeasurableSpace (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := ⟨rfl⟩
  letI mT2' : MeasurableSpace (sigmaCentralizer (η' K L σ A i₀) δ') := borel _
  haveI : BorelSpace (sigmaCentralizer (η' K L σ A i₀) δ') := ⟨rfl⟩
  letI mTb : MeasurableSpace (Subgroup.centralizer ({(γ₀, γ')} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) :=
    borel _
  haveI : BorelSpace (Subgroup.centralizer ({(γ₀, γ')} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) := ⟨rfl⟩
  letI mTb' : MeasurableSpace (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (δ₀, δ')) := borel _
  haveI : BorelSpace (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (δ₀, δ')) := ⟨rfl⟩
  haveI := hτ₀; haveI := hτ₀'; haveI := hτ₂; haveI := hτ₂'; haveI := hτ₂'i
  have hT0c := GroupOrbital.isClosed_centralizer γ₀
  have hT0'c := GroupOrbital.isClosed_sigmaCentralizer (continuous_θfam K L σ A i₀) δ₀
  have hT2c := GroupOrbital.isClosed_centralizer γ'
  have hT2'c := GroupOrbital.isClosed_sigmaCentralizer (continuous_η' K L σ A i₀) δ'
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) := hT0c.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer (θfam K L σ A i₀) δ₀) := hT0'c.locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) :=
    hT2c.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer (η' K L σ A i₀) δ') := hT2'c.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer (θfam K L σ A i₀) δ₀) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer (η' K L σ A i₀) δ') :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SFinite τ₀ := inferInstance
  haveI : SFinite τ₀' := inferInstance
  haveI : SFinite τ₂ := inferInstance
  haveI : SFinite τ₂' := inferInstance
  haveI : BorelSpace (Subgroup.centralizer ({γ₀} : Set (Gi A i₀)) ×
      Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := Prod.borelSpace
  haveI : BorelSpace (sigmaCentralizer (θfam K L σ A i₀) δ₀ × sigmaCentralizer (η' K L σ A i₀) δ') := Prod.borelSpace

  have hτ₀'i : Measure.IsInvInvariant τ₀' := isInvInvariant_of_regular_head K L σ A i₀ δ₀ hδ₀ τ₀' hτ₀'
  have hτ₀i : Measure.IsInvInvariant τ₀ :=
    Carriers.OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _ hT0c
      (Carriers.RegularCentralizer.isMulCommutative_centralizer_of_isRegularSemisimple hγ₀) τ₀ hτ₀
  have hτ₂i : Measure.IsInvInvariant τ₂ :=
    Carriers.OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _ hT2c
      (Carriers.isMulCommutative_centralizer_pi_of_isRegularSemisimple (fun j : {j // j ≠ i₀} => A j) γ' hγ') τ₂ hτ₂
  haveI := hτ₀'i; haveI := hτ₀i; haveI := hτ₂i

  have hνb : Measure.IsHaarMeasure (Measure.map (eG A i₀) ν) := (eG A i₀).isHaarMeasure_map ν
  have hνb' : Measure.IsHaarMeasure (Measure.map (eH K L A i₀) ν') := (eH K L A i₀).isHaarMeasure_map ν'

  set fL : Hi K L A i₀ × (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ := Φ ∘ (eH K L A i₀).symm with hfL
  set fK : Gi A i₀ × (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ := F ∘ (eG A i₀).symm with hfK
  have hfLc : Continuous fL := hΦ.comp (eH K L A i₀).symm.continuous
  have hfKc : Continuous fK := hF.comp (eG A i₀).symm.continuous
  have hfLs : HasCompactSupport fL := hΦc.comp_homeomorph (eH K L A i₀).symm.toHomeomorph
  have hfKs : HasCompactSupport fK := hFc.comp_homeomorph (eG A i₀).symm.toHomeomorph

  obtain ⟨ΨL, hΨLc, hΨLs, hΨL1⟩ := Env.exists_bump_eq_one (hfLs.image continuous_snd)
  obtain ⟨ΨK, hΨKc, hΨKs, hΨK1⟩ := Env.exists_bump_eq_one (hfKs.image continuous_snd)
  obtain ⟨Ve, hVec, hVe0, hVes, hVe1⟩ := ihCL δ' hδ' τ₂' hτ₂' hτ₂'i ΨL hΨLc hΨLs
  obtain ⟨ve, hvec, hve0, hves, hve1⟩ := ihCK γ' hγ' τ₂ hτ₂ ΨK hΨKc hΨKs

  have hnL : ∀ (x₁ : Hi K L A i₀) (x₂ : ∀ j : {j // j ≠ i₀}, Hi K L A j),
      fL (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂) ≠ 0 →
      ∫ t : sigmaCentralizer (θfam K L σ A i₀) δ₀, W₀ ((t : Hi K L A i₀) * x₁) ∂τ₀' = 1 ∧
      ∫ t : sigmaCentralizer (η' K L σ A i₀) δ', Ve ((t : ∀ j : {j // j ≠ i₀}, Hi K L A j) * x₂) ∂τ₂' = 1 := by
    intro x₁ x₂ h
    refine ⟨hW₀1 x₁ _ h, hVe1 x₂ ?_⟩
    rw [hΨL1 _ ⟨_, subset_tsupport _ h, rfl⟩]
    exact one_ne_zero
  have hnK : ∀ (x₁ : Gi A i₀) (x₂ : ∀ j : {j // j ≠ i₀}, Gi A j),
      fK (x₁⁻¹ * γ₀ * x₁, x₂⁻¹ * γ' * x₂) ≠ 0 →
      ∫ t : Subgroup.centralizer ({γ₀} : Set (Gi A i₀)), ω₀ ((t : Gi A i₀) * x₁) ∂τ₀ = 1 ∧
      ∫ t : Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j)),
        ve ((t : ∀ j : {j // j ≠ i₀}, Gi A j) * x₂) ∂τ₂ = 1 := by
    intro x₁ x₂ h
    refine ⟨hω₀1 x₁ _ h, hve1 x₂ ?_⟩
    rw [hΨK1 _ ⟨_, subset_tsupport _ h, rfl⟩]
    exact one_ne_zero

  set τb' : Measure (sigmaCentralizer ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (δ₀, δ')) :=
    Measure.map (GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) δ₀ δ') (τ₀'.prod τ₂') with hτb'
  set τb : Measure (Subgroup.centralizer ({(γ₀, γ')} : Set (Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j))) :=
    Measure.map (GroupOrbital.prodCentEquiv γ₀ γ') (τ₀.prod τ₂) with hτb
  haveI : (τ₀'.prod τ₂').IsHaarMeasure := inferInstance
  haveI : (τ₀.prod τ₂).IsHaarMeasure := inferInstance
  haveI hτb'H : τb'.IsHaarMeasure := (GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) δ₀ δ').isHaarMeasure_map _
  haveI hτbH : τb.IsHaarMeasure := (GroupOrbital.prodCentEquiv γ₀ γ').isHaarMeasure_map _
  haveI hτb'i : τb'.IsInvInvariant :=
    GroupOrbital.isInvInvariant_map_prod (GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) δ₀ δ') τ₀' τ₂'

  set I' : ℂ := ∫ z : Hi K L A i₀ × (∀ j : {j // j ≠ i₀}, Hi K L A j),
      fL (z⁻¹ * (δ₀, δ') * ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) z) * ((W₀ z.1 * Ve z.2 : ℝ) : ℂ)
        ∂(Measure.map (eH K L A i₀) ν') with hI'
  set I : ℂ := ∫ z : Gi A i₀ × (∀ j : {j // j ≠ i₀}, Gi A j),
      fK (z⁻¹ * (γ₀, γ') * z) * ((ω₀ z.1 * ve z.2 : ℝ) : ℂ) ∂(Measure.map (eG A i₀) ν) with hI
  have hI'val : GroupOrbital.IsValue ((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) (Measure.map (eH K L A i₀) ν')
      (δ₀, δ') τb' fL I' := by
    refine ⟨fun z => W₀ z.1 * Ve z.2, ⟨fun z => mul_nonneg (hW₀0 _) (hVe0 _),
      ((hW₀c.comp continuous_fst).mul (hVec.comp continuous_snd)).measurable,
      Env.hasCompactSupport_prodWeights hW₀s hVes, fun z hz => ?_⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hnL z.1 z.2 hz
    rw [hτb', show (⇑(GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) δ₀ δ')) =
        ⇑((GroupOrbital.prodTorusEquiv (θfam K L σ A i₀) (η' K L σ A i₀) δ₀ δ').toHomeomorph.toMeasurableEquiv) from rfl,
      MeasureTheory.integral_map_equiv]
    show ∫ s : sigmaCentralizer (θfam K L σ A i₀) δ₀ × sigmaCentralizer (η' K L σ A i₀) δ',
        W₀ ((s.1 : Hi K L A i₀) * z.1) * Ve ((s.2 : ∀ j : {j // j ≠ i₀}, Hi K L A j) * z.2) ∂(τ₀'.prod τ₂') = 1
    rw [MeasureTheory.integral_prod_mul (fun s : sigmaCentralizer (θfam K L σ A i₀) δ₀ => W₀ ((s : Hi K L A i₀) * z.1))
      (fun s : sigmaCentralizer (η' K L σ A i₀) δ' => Ve ((s : ∀ j : {j // j ≠ i₀}, Hi K L A j) * z.2)), h1, h2, one_mul]
  have hIval : GroupOrbital.IsValueC (Measure.map (eG A i₀) ν) (γ₀, γ') τb fK I := by
    refine ⟨fun z => ω₀ z.1 * ve z.2, ⟨fun z => mul_nonneg (hω₀0 _) (hve0 _),
      ((hω₀c.comp continuous_fst).mul (hvec.comp continuous_snd)).measurable,
      Env.hasCompactSupport_prodWeights hω₀s hves, fun z hz => ?_⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hnK z.1 z.2 hz
    rw [hτb, show (⇑(GroupOrbital.prodCentEquiv γ₀ γ')) =
        ⇑((GroupOrbital.prodCentEquiv γ₀ γ').toHomeomorph.toMeasurableEquiv) from rfl,
      MeasureTheory.integral_map_equiv]
    show ∫ s : Subgroup.centralizer ({γ₀} : Set (Gi A i₀)) × Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j)),
        ω₀ ((s.1 : Gi A i₀) * z.1) * ve ((s.2 : ∀ j : {j // j ≠ i₀}, Gi A j) * z.2) ∂(τ₀.prod τ₂) = 1
    rw [MeasureTheory.integral_prod_mul (fun s : Subgroup.centralizer ({γ₀} : Set (Gi A i₀)) => ω₀ ((s : Gi A i₀) * z.1))
      (fun s : Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j)) =>
        ve ((s : ∀ j : {j // j ≠ i₀}, Gi A j) * z.2)), h1, h2, one_mul]

  have hI'eq := GroupOrbital.value_eq_mul_iterated (θfam K L σ A i₀) (continuous_θfam K L σ A i₀) (η' K L σ A i₀)
    (continuous_η' K L σ A i₀) δ₀ δ' (Measure.map (eH K L A i₀) ν') hνb' (μ' i₀) (hμ' i₀) ν₂' hν₂' cL hcL
    τ₀' hτ₀' hτ₀'i τ₂' hτ₂' hτ₂'i fL hfLc hfLs W₀ Ve hW₀c hW₀0 hW₀s hVec hVe0 hVes hnL I' hI'val
  have hIeq := GroupOrbital.valueC_eq_mul_iterated γ₀ γ' (Measure.map (eG A i₀) ν) hνb (μ i₀) (hμ i₀) ν₂ hν₂ cK hcK
    τ₀ hτ₀ hτ₀i τ₂ hτ₂ hτ₂i fK hfKc hfKs ω₀ ve hω₀c hω₀0 hω₀s hvec hve0 hves hnK I hIval

  have heH' : ∀ x, (eH K L A i₀).symm (((θfam K L σ A i₀).prodMap (η' K L σ A i₀)) x) =
      etaPi K L σ A ((eH K L A i₀).symm x) :=
    fun x => GroupOrbital.symm_apply_twist (eH K L A i₀) (eH_etaPi K L σ A i₀) x
  have hvalL := GroupOrbital.IsValue.map (eH K L A i₀).symm heH' (Measure.map (eH K L A i₀) ν') (δ₀, δ') τb' fL I' hI'val
  have hvalK := GroupOrbital.IsValueC.map (eG A i₀).symm (Measure.map (eG A i₀) ν) (γ₀, γ') τb fK I hIval
  have hmH : Measurable ((eH K L A i₀) : (∀ i, Hi K L A i) → Hi K L A i₀ × ∀ j : {j // j ≠ i₀}, Hi K L A j) :=
    (eH K L A i₀).continuous.measurable
  have hmH' : Measurable ((eH K L A i₀).symm : Hi K L A i₀ × (∀ j : {j // j ≠ i₀}, Hi K L A j) → ∀ i, Hi K L A i) :=
    (eH K L A i₀).symm.continuous.measurable
  have hmG : Measurable ((eG A i₀) : (∀ i, Gi A i) → Gi A i₀ × ∀ j : {j // j ≠ i₀}, Gi A j) :=
    (eG A i₀).continuous.measurable
  have hmG' : Measurable ((eG A i₀).symm : Gi A i₀ × (∀ j : {j // j ≠ i₀}, Gi A j) → ∀ i, Gi A i) :=
    (eG A i₀).symm.continuous.measurable
  have hνback : Measure.map (eH K L A i₀).symm (Measure.map (eH K L A i₀) ν') = ν' := by
    rw [Measure.map_map hmH' hmH]
    have : ((eH K L A i₀).symm : _ → _) ∘ (eH K L A i₀) = id := funext fun x => (eH K L A i₀).symm_apply_apply x
    rw [this, Measure.map_id]
  have hνbackK : Measure.map (eG A i₀).symm (Measure.map (eG A i₀) ν) = ν := by
    rw [Measure.map_map hmG' hmG]
    have : ((eG A i₀).symm : _ → _) ∘ (eG A i₀) = id := funext fun x => (eG A i₀).symm_apply_apply x
    rw [this, Measure.map_id]
  have hfLback : fL ∘ ((eH K L A i₀).symm.symm : _ → _) = Φ := by
    funext x
    show Φ ((eH K L A i₀).symm ((eH K L A i₀).symm.symm x)) = Φ x
    rw [(eH K L A i₀).symm.apply_symm_apply]
  have hfKback : fK ∘ ((eG A i₀).symm.symm : _ → _) = F := by
    funext x
    show F ((eG A i₀).symm ((eG A i₀).symm.symm x)) = F x
    rw [(eG A i₀).symm.apply_symm_apply]
  rw [hνback, hfLback] at hvalL
  rw [hνbackK, hfKback] at hvalK

  have hsymmG0 : ∀ (a : Gi A i₀) (b : ∀ j : {j // j ≠ i₀}, Gi A j), (eG A i₀).symm (a, b) i₀ = a :=
    fun a b => GroupOrbital.piSplitEquiv_symm_apply_self (Gi A) i₀ a b
  have hsymmG : ∀ (a : Gi A i₀) (b : ∀ j : {j // j ≠ i₀}, Gi A j) (j : {j // j ≠ i₀}), (eG A i₀).symm (a, b) j = b j :=
    fun a b j => GroupOrbital.piSplitEquiv_symm_apply_of_ne (Gi A) i₀ a b j
  have hsymmH0 : ∀ (a : Hi K L A i₀) (b : ∀ j : {j // j ≠ i₀}, Hi K L A j), (eH K L A i₀).symm (a, b) i₀ = a :=
    fun a b => GroupOrbital.piSplitEquiv_symm_apply_self (Hi K L A) i₀ a b
  have hsymmH : ∀ (a : Hi K L A i₀) (b : ∀ j : {j // j ≠ i₀}, Hi K L A j) (j : {j // j ≠ i₀}),
      (eH K L A i₀).symm (a, b) j = b j :=
    fun a b j => GroupOrbital.piSplitEquiv_symm_apply_of_ne (Hi K L A) i₀ a b j
  have hγreg : ∀ i, IsRegularSemisimple ((eG A i₀).symm (γ₀, γ') i) := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hsymmG0]; exact hγ₀
    · rw [show (eG A i₀).symm (γ₀, γ') i = γ' ⟨i, hi⟩ from hsymmG γ₀ γ' ⟨i, hi⟩]; exact hγ' ⟨i, hi⟩
  have hδreg : ∀ i, IsRegularSemisimple (normString K L (A i) σ ((eH K L A i₀).symm (δ₀, δ') i)) := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hsymmH0]; exact hδ₀
    · rw [show (eH K L A i₀).symm (δ₀, δ') i = δ' ⟨i, hi⟩ from hsymmH δ₀ δ' ⟨i, hi⟩]; exact hδ' ⟨i, hi⟩
  have hyNC : ∀ i, IsNormConjugator K L (A i) σ ((eG A i₀).symm (γ₀, γ') i) ((eH K L A i₀).symm (δ₀, δ') i)
      ((eH K L A i₀).symm (y₀, y') i) := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hsymmG0, hsymmH0, hsymmH0]; exact hy₀
    · rw [show (eG A i₀).symm (γ₀, γ') i = γ' ⟨i, hi⟩ from hsymmG γ₀ γ' ⟨i, hi⟩,
        show (eH K L A i₀).symm (δ₀, δ') i = δ' ⟨i, hi⟩ from hsymmH δ₀ δ' ⟨i, hi⟩,
        show (eH K L A i₀).symm (y₀, y') i = y' ⟨i, hi⟩ from hsymmH y₀ y' ⟨i, hi⟩]
      exact hy' ⟨i, hi⟩

  have hcplb := GroupOrbital.coupling_prod (φfam K L A i₀) (Φ' K L A i₀) (continuous_φfam K L A i₀) (continuous_Φ' K L A i₀)
    (θfam K L σ A i₀) (η' K L σ A i₀) γ₀ γ' δ₀ y₀ δ' y' τ₀ τ₂ τ₀' τ₂' inferInstance inferInstance inferInstance inferInstance
    hc₀ hcpl'
  have hφback : ∀ g, (eH K L A i₀).symm (((φfam K L A i₀).prodMap (Φ' K L A i₀)) g) = PhiPi K L A ((eG A i₀).symm g) := by
    intro g
    apply (eH K L A i₀).injective
    rw [(eH K L A i₀).apply_symm_apply, eH_PhiPi K L A i₀, (eG A i₀).apply_symm_apply]
  have hcpl := GroupOrbital.coupling_transport (eG A i₀).symm (eH K L A i₀).symm
    ((φfam K L A i₀).prodMap (Φ' K L A i₀)) (PhiPi K L A) (continuous_prodMap_φ K L A i₀) (continuous_PhiPi K L A)
    hφback heH' (γ₀, γ') (δ₀, δ') (y₀, y') τb τb' hcplb

  letI mT : MeasurableSpace (Subgroup.centralizer ({(eG A i₀).symm (γ₀, γ')} : Set (∀ i, Gi A i))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({(eG A i₀).symm (γ₀, γ')} : Set (∀ i, Gi A i))) := ⟨rfl⟩
  letI mT' : MeasurableSpace (sigmaCentralizer (etaPi K L σ A) ((eH K L A i₀).symm (δ₀, δ'))) := borel _
  haveI : BorelSpace (sigmaCentralizer (etaPi K L σ A) ((eH K L A i₀).symm (δ₀, δ'))) := ⟨rfl⟩
  have hτH : Measure.IsHaarMeasure (Measure.map (GroupOrbital.centTransport (eG A i₀).symm (γ₀, γ')) τb) :=
    (GroupOrbital.centTransport (eG A i₀).symm (γ₀, γ')).isHaarMeasure_map τb
  have hτ'H : Measure.IsHaarMeasure (Measure.map (GroupOrbital.torusEquiv (eH K L A i₀).symm heH' (δ₀, δ')) τb') :=
    (GroupOrbital.torusEquiv (eH K L A i₀).symm heH' (δ₀, δ')).isHaarMeasure_map τb'
  have hτ'i : Measure.IsInvInvariant (Measure.map (GroupOrbital.torusEquiv (eH K L A i₀).symm heH' (δ₀, δ')) τb') :=
    GroupOrbital.isInvInvariant_map_mulEquiv (GroupOrbital.torusEquiv (eH K L A i₀).symm heH' (δ₀, δ')) τb'

  have hI'I : I' = I := hreg ((eG A i₀).symm (γ₀, γ')) ((eH K L A i₀).symm (δ₀, δ')) ((eH K L A i₀).symm (y₀, y'))
    hγreg hδreg hyNC _ _ hτH hτ'H hτ'i hcpl I I' hvalL hvalK

  have hΦ1c : Continuous (fun h' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => ∫ x₁ : Hi K L A i₀,
      Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, h')) * (W₀ x₁ : ℂ) ∂(μ' i₀)) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support (k := tsupport W₀) hW₀s ?_ ?_
    · refine Continuous.continuousOn ?_
      exact (hΦ.comp ((eH K L A i₀).symm.continuous.comp
        ((((continuous_inv.comp continuous_snd).mul continuous_const).mul
          ((continuous_θfam K L σ A i₀).comp continuous_snd)).prodMk continuous_fst))).mul
        (Complex.continuous_ofReal.comp (hW₀c.comp continuous_snd))
    · intro p x _ hx
      simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, mul_zero]
  have hF1c : Continuous (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
      ∫ x₁ : Gi A i₀, F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, g')) * (ω₀ x₁ : ℂ) ∂(μ i₀)) := by
    refine continuous_const.mul ?_
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support (k := tsupport ω₀) hω₀s ?_ ?_
    · refine Continuous.continuousOn ?_
      exact (hF.comp ((eG A i₀).symm.continuous.comp
        ((((continuous_inv.comp continuous_snd).mul continuous_const).mul continuous_snd).prodMk continuous_fst))).mul
        (Complex.continuous_ofReal.comp (hω₀c.comp continuous_snd))
    · intro p x _ hx
      simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, mul_zero]

  obtain ⟨V', ⟨hV'0, hV'm, -, hV'1⟩, hJ'eq⟩ := hJ'
  have hVe1' : ∀ x : (∀ j : {j // j ≠ i₀}, Hi K L A j),
      (fun h' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => ∫ x₁ : Hi K L A i₀,
        Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, h')) * (W₀ x₁ : ℂ) ∂(μ' i₀))
        (x⁻¹ * δ' * (η' K L σ A i₀) x) ≠ 0 →
      ∫ t : sigmaCentralizer (η' K L σ A i₀) δ', Ve ((t : ∀ j : {j // j ≠ i₀}, Hi K L A j) * x) ∂τ₂' = 1 := by
    intro x hx
    apply hVe1 x
    have hex : ∃ x₁ : Hi K L A i₀, Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x⁻¹ * δ' * (η' K L σ A i₀) x)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hx
      simp only [hall, zero_mul, integral_zero]
    obtain ⟨x₁, hx₁⟩ := hex
    rw [hΨL1 _ ⟨(x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x⁻¹ * δ' * (η' K L σ A i₀) x), subset_tsupport fL hx₁, rfl⟩]
    exact one_ne_zero
  have hJ'1 := GroupOrbital.integral_twistedConj_mul_eq_of_sections (η' K L σ A i₀) (continuous_η' K L σ A i₀) ν₂' hν₂' δ'
    τ₂' hτ₂' hτ₂'i _ hΦ1c V' Ve hV'0 hVe0 hV'm hVec.measurable hV'1 hVe1'

  obtain ⟨v', ⟨hv'0, hv'm, -, hv'1⟩, hJeq⟩ := hJ
  have hve1' : ∀ x : (∀ j : {j // j ≠ i₀}, Gi A j),
      (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
        ∫ x₁ : Gi A i₀, F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, g')) * (ω₀ x₁ : ℂ) ∂(μ i₀)) (x⁻¹ * γ' * x) ≠ 0 →
      ∫ t : Subgroup.centralizer ({γ'} : Set (∀ j : {j // j ≠ i₀}, Gi A j)),
        ve ((t : ∀ j : {j // j ≠ i₀}, Gi A j) * x) ∂τ₂ = 1 := by
    intro x hx
    apply hve1 x
    have hex : ∃ x₁ : Gi A i₀, F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x⁻¹ * γ' * x)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hx
      simp only [hall, zero_mul, integral_zero, mul_zero]
    obtain ⟨x₁, hx₁⟩ := hex
    rw [hΨK1 _ ⟨(x₁⁻¹ * γ₀ * x₁, x⁻¹ * γ' * x), subset_tsupport fK hx₁, rfl⟩]
    exact one_ne_zero
  have hJ1 := GroupOrbital.integral_conj_mul_eq_of_sections ν₂ hν₂ γ' τ₂ hτ₂ hτ₂i _ hF1c v' ve hv'0 hve0 hv'm
    hvec.measurable hv'1 hve1'

  set gL : Hi K L A i₀ → (∀ j : {j // j ≠ i₀}, Hi K L A j) → ℂ := fun x₁ x₂ =>
    fL (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂) * ((W₀ x₁ * Ve x₂ : ℝ) : ℂ) with hgL
  set gK : Gi A i₀ → (∀ j : {j // j ≠ i₀}, Gi A j) → ℂ := fun x₁ x₂ =>
    fK (x₁⁻¹ * γ₀ * x₁, x₂⁻¹ * γ' * x₂) * ((ω₀ x₁ * ve x₂ : ℝ) : ℂ) with hgK

  have hswapL : ∫ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), (∫ x₁ : Hi K L A i₀, gL x₁ x₂ ∂(μ' i₀)) ∂ν₂' =
      ∫ x₁ : Hi K L A i₀, (∫ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), gL x₁ x₂ ∂ν₂') ∂(μ' i₀) := by
    refine MeasureTheory.integral_integral_swap_of_hasCompactSupport (f := fun x₂ x₁ => gL x₁ x₂) ?_ ?_
    · exact (hfLc.comp
        ((((continuous_inv.comp continuous_snd).mul continuous_const).mul
          ((continuous_θfam K L σ A i₀).comp continuous_snd)).prodMk
          (((continuous_inv.comp continuous_fst).mul continuous_const).mul
            ((continuous_η' K L σ A i₀).comp continuous_fst)))).mul
        (Complex.continuous_ofReal.comp ((hW₀c.comp continuous_snd).mul (hVec.comp continuous_fst)))
    · refine HasCompactSupport.intro' (hVes.prod hW₀s) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
      intro p hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with h | h
      · show gL p.2 p.1 = 0
        simp only [hgL, image_eq_zero_of_notMem_tsupport h, mul_zero, Complex.ofReal_zero]
      · show gL p.2 p.1 = 0
        simp only [hgL, image_eq_zero_of_notMem_tsupport h, zero_mul, mul_zero, Complex.ofReal_zero]
  have hswapK : ∫ x₂ : (∀ j : {j // j ≠ i₀}, Gi A j), (∫ x₁ : Gi A i₀, gK x₁ x₂ ∂(μ i₀)) ∂ν₂ =
      ∫ x₁ : Gi A i₀, (∫ x₂ : (∀ j : {j // j ≠ i₀}, Gi A j), gK x₁ x₂ ∂ν₂) ∂(μ i₀) := by
    refine MeasureTheory.integral_integral_swap_of_hasCompactSupport (f := fun x₂ x₁ => gK x₁ x₂) ?_ ?_
    · exact (hfKc.comp
        ((((continuous_inv.comp continuous_snd).mul continuous_const).mul continuous_snd).prodMk
          (((continuous_inv.comp continuous_fst).mul continuous_const).mul continuous_fst))).mul
        (Complex.continuous_ofReal.comp ((hω₀c.comp continuous_snd).mul (hvec.comp continuous_fst)))
    · refine HasCompactSupport.intro' (hves.prod hω₀s) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
      intro p hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with h | h
      · show gK p.2 p.1 = 0
        simp only [hgK, image_eq_zero_of_notMem_tsupport h, mul_zero, Complex.ofReal_zero]
      · show gK p.2 p.1 = 0
        simp only [hgK, image_eq_zero_of_notMem_tsupport h, zero_mul, mul_zero, Complex.ofReal_zero]

  have hJ'2 : J' = ∫ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), (∫ x₁ : Hi K L A i₀, gL x₁ x₂ ∂(μ' i₀)) ∂ν₂' := by
    rw [hJ'eq, hJ'1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₂ => ?_)
    show (∫ x₁ : Hi K L A i₀, Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁,
        x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) * (W₀ x₁ : ℂ) ∂(μ' i₀)) * (Ve x₂ : ℂ) = ∫ x₁ : Hi K L A i₀, gL x₁ x₂ ∂(μ' i₀)
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₁ => ?_)
    show Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂)) * (W₀ x₁ : ℂ) *
        (Ve x₂ : ℂ) = fL (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂⁻¹ * δ' * (η' K L σ A i₀) x₂) * ((W₀ x₁ * Ve x₂ : ℝ) : ℂ)
    rw [Complex.ofReal_mul, mul_assoc]
    rfl
  have hJ2 : J = (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
      ∫ x₂ : (∀ j : {j // j ≠ i₀}, Gi A j), (∫ x₁ : Gi A i₀, gK x₁ x₂ ∂(μ i₀)) ∂ν₂ := by
    rw [hJeq, hJ1, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₂ => ?_)
    show (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * (∫ x₁ : Gi A i₀, F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x₂⁻¹ * γ' * x₂)) *
        (ω₀ x₁ : ℂ) ∂(μ i₀)) * (ve x₂ : ℂ) = (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * ∫ x₁ : Gi A i₀, gK x₁ x₂ ∂(μ i₀)
    rw [mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₁ => ?_)
    show F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x₂⁻¹ * γ' * x₂)) * (ω₀ x₁ : ℂ) * (ve x₂ : ℂ) =
      fK (x₁⁻¹ * γ₀ * x₁, x₂⁻¹ * γ' * x₂) * ((ω₀ x₁ * ve x₂ : ℝ) : ℂ)
    rw [Complex.ofReal_mul, mul_assoc]
    rfl

  have hcL0' : ((cL : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcL0.ne'
  have hcK0' : ((cK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcK0.ne'
  have hXL : ∫ x₁ : Hi K L A i₀, (∫ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), gL x₁ x₂ ∂ν₂') ∂(μ' i₀) =
      I' / ((cL : ℝ) : ℂ) := by
    rw [eq_div_iff hcL0', mul_comm]
    exact hI'eq.symm
  have hXK : ∫ x₁ : Gi A i₀, (∫ x₂ : (∀ j : {j // j ≠ i₀}, Gi A j), gK x₁ x₂ ∂ν₂) ∂(μ i₀) =
      I / ((cK : ℝ) : ℂ) := by
    rw [eq_div_iff hcK0', mul_comm]
    exact hIeq.symm
  rw [hJ'2, hswapL, hJ2, hswapK, hXL, hXK, hI'I]
  field_simp

end StepREG
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

end S30SemilocalCent
p2m_reactivate "P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent.GroupOrbital P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step.S30SemilocalCent"

set_option maxHeartbeats 8000000 in
open S30SemilocalCent MeasureTheory AutomorphicForm Topology in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, SecondCountableTopology (A i)]
    (X Y : ι → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
    (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
    (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
    (c : ∀ i, (A i)ˣ)
    (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
    (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
    (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
    (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
    (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))

    (hsecK : ∀ (i : ι) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
        ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
    (hsecL : ∀ (i : ι) (δ : GL (Fin 2) (L ⊗[K] A i)),
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
        ∃ d : (L ⊗[K] A i)ˣ, IsSigmaConjugate K L (A i) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      ∀ φ : GL (Fin 2) (L ⊗[K] A i) → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : GL (Fin 2) (L ⊗[K] A i) → ℝ, IsTwistedSectionFnOn K L (A i) σ δ τ' φ W ∧ Continuous W)

    (heng : ∀ (i : ι) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
      ((∃ Φ₁ : Y i → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (εL i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (A i) → ℂ),
      ((∃ F₁ : X i → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (εK i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)),
        ∀ δ : GL (Fin 2) (L ⊗[K] A i), IsRegularSemisimple (normString K L (A i) σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] A i), IsNormConjugator K L (A i) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ))
          (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
          Coupled K L (A i) σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] A i),
        IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))))
              (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))))
          (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
          @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
          Coupled K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) τ f I → I' = I)

    (ν : @Measure ((i : ι) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : ι) → GL (Fin 2) (A i)) _ _ (borel _) ν)
    (ν' : @Measure ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
    (F : ((i : ι) → GL (Fin 2) (A i)) → ℂ)
    (hF : (∃ F₁ : ((i : ι) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
    (Φ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
    (hΦ : (∃ Φ₁ : ((i : ι) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)

    (hreg : ∀ (γ : ((i : ι) → GL (Fin 2) (A i))) (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ I I' : ℂ,
          (∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : ι) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
          I' = I)

    (ih : ∀ {κ : Type} [Fintype κ] [DecidableEq κ]
      (A : κ → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
      [∀ i, SecondCountableTopology (A i)]
      (X Y : κ → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
      [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
      (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
      (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
      (c : ∀ i, (A i)ˣ)
      (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
      (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
      (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
      (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
      (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))
      (hsecK : ∀ (i : κ) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
      ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
      (hsecL : ∀ (i : κ) (δ : GL (Fin 2) (L ⊗[K] A i)),
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
      ∃ d : (L ⊗[K] A i)ˣ, IsSigmaConjugate K L (A i) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      ∀ φ : GL (Fin 2) (L ⊗[K] A i) → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ W : GL (Fin 2) (L ⊗[K] A i) → ℝ, IsTwistedSectionFnOn K L (A i) σ δ τ' φ W ∧ Continuous W)
      (heng : ∀ (i : κ) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
      ((∃ Φ₁ : Y i → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (εL i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (A i) → ℂ),
      ((∃ F₁ : X i → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (εK i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)),
      ∀ δ : GL (Fin 2) (L ⊗[K] A i), IsRegularSemisimple (normString K L (A i) σ δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] A i), IsNormConjugator K L (A i) σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ))
      (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      Coupled K L (A i) σ γ δ y τ τ' →
      ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
      IsOrbitalIntegralOn (A i) (μ i) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] A i),
      IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))))
      (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))))
      (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      Coupled K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y τ τ' →
      ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
      IsOrbitalIntegralOn (A i) (μ i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) τ f I → I' = I)
      (ν : @Measure ((i : κ) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : κ) → GL (Fin 2) (A i)) _ _ (borel _) ν)
      (ν' : @Measure ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
      (F : ((i : κ) → GL (Fin 2) (A i)) → ℂ)
      (hF : (∃ F₁ : ((i : κ) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
      (Φ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
      (hΦ : (∃ Φ₁ : ((i : κ) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)
      (hreg : ∀ (γ : ((i : κ) → GL (Fin 2) (A i))) (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : κ) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
      I' = I),
      Fintype.card κ < Fintype.card ι →
      (∀ (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i))) =>
      fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : κ) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (A i))) ν
      (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
      I' = I) ∧
      (∀ (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i))) =>
      fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (δ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (γ : ((i : κ) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : ((i : κ) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1)) :
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer
                ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
              fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ I I' : ℂ,
          (∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : ι) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (A i))) ν
              (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
          I' = I) ∧
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
              fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
    (∀ (δ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
    (∀ (γ : ((i : ι) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
            ∀ x : ((i : ι) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) := by
  rcases (Fintype.card ι).eq_zero_or_pos with hcard | hpos
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro δ y hnc τ τ' hτ hτ' hτ'i hcpl I I' hI' hI
      exact hreg _ δ y (fun i => isEmptyElim i) (fun i => isEmptyElim i) hnc τ τ' hτ hτ' hτ'i hcpl I I' hI' hI
    · intro δ y hnc τ τ' hτ hτ' hτ'i hcpl Ψ hΨ hΨc
      letI mT : MeasurableSpace (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) := borel _
      haveI : BorelSpace (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) := ⟨rfl⟩
      haveI := hτ'
      haveI : ∀ i, CompactSpace (GL (Fin 2) (L ⊗[K] A i)) := fun i => isEmptyElim i
      haveI hU : Unique ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) := Pi.uniqueOfIsEmpty _
      haveI : Finite ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) := Finite.of_subsingleton
      haveI : Finite (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) := Subtype.finite
      have hfin : τ' Set.univ < ⊤ := IsCompact.measure_lt_top isCompact_univ
      have hpos : 0 < τ' Set.univ := IsOpen.measure_pos τ' isOpen_univ ⟨1, trivial⟩
      have hR : (τ' Set.univ).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
      refine ⟨fun _ => ((τ' Set.univ).toReal)⁻¹, continuous_const, fun _ => by positivity, ?_, fun x _ => ?_⟩
      · exact HasCompactSupport.of_compactSpace _
      · rw [integral_const, smul_eq_mul]
        simp only [Measure.real, mul_inv_cancel₀ hR]
    · intro δ hδ τ' hτ' hτ'i Ψ hΨ hΨc
      letI mT : MeasurableSpace (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) := borel _
      haveI : BorelSpace (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) := ⟨rfl⟩
      haveI := hτ'
      haveI : ∀ i, CompactSpace (GL (Fin 2) (L ⊗[K] A i)) := fun i => isEmptyElim i
      haveI hU : Unique ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) := Pi.uniqueOfIsEmpty _
      haveI : Finite ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) := Finite.of_subsingleton
      haveI : Finite (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) := Subtype.finite
      have hfin : τ' Set.univ < ⊤ := IsCompact.measure_lt_top isCompact_univ
      have hpos : 0 < τ' Set.univ := IsOpen.measure_pos τ' isOpen_univ ⟨1, trivial⟩
      have hR : (τ' Set.univ).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
      refine ⟨fun _ => ((τ' Set.univ).toReal)⁻¹, continuous_const, fun _ => by positivity, ?_, fun x _ => ?_⟩
      · exact HasCompactSupport.of_compactSpace _
      · rw [integral_const, smul_eq_mul]
        simp only [Measure.real, mul_inv_cancel₀ hR]
    · intro γ hγ τ hτ Ψ hΨ hΨc
      letI mT : MeasurableSpace (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) := borel _
      haveI : BorelSpace (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) := ⟨rfl⟩
      haveI := hτ
      haveI : ∀ i, CompactSpace (GL (Fin 2) (A i)) := fun i => isEmptyElim i
      haveI hU : Unique ((i : ι) → GL (Fin 2) (A i)) := Pi.uniqueOfIsEmpty _
      haveI : Finite ((i : ι) → GL (Fin 2) (A i)) := Finite.of_subsingleton
      haveI : Finite (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) := Subtype.finite
      have hfin : τ Set.univ < ⊤ := IsCompact.measure_lt_top isCompact_univ
      have hpos : 0 < τ Set.univ := IsOpen.measure_pos τ isOpen_univ ⟨1, trivial⟩
      have hR : (τ Set.univ).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
      refine ⟨fun _ => ((τ Set.univ).toReal)⁻¹, continuous_const, fun _ => by positivity, ?_, fun x _ => ?_⟩
      · exact HasCompactSupport.of_compactSpace _
      · rw [integral_const, smul_eq_mul]
        simp only [Measure.real, mul_inv_cancel₀ hR]
  ·
    have hne : Nonempty ι := Fintype.card_pos_iff.mp hpos
    obtain ⟨i₀⟩ := hne
    let ι' : Type := {j : ι // j ≠ i₀}
    have hlt : Fintype.card ι' < Fintype.card ι := by
      simp only [ι', Fintype.card_subtype_compl, Fintype.card_unique]
      exact Nat.sub_lt hpos Nat.one_pos
    have ih' := ih (κ := ι') (fun j => A j) (fun j => X j) (fun j => Y j) (fun j => εK j) (fun j => hεK j)
      (fun j => εL j) (fun j => hεL j) (fun j => c j) (fun j => μ j) (fun j => hμ j) (fun j => hμr j)
      (fun j => μ' j) (fun j => hμ' j) (fun j => hsecK j) (fun j => hsecL j) (fun j => heng j)

    haveI := fun i => locallyCompactSpace_Gi A i
    haveI := fun i => secondCountableTopology_Gi A i
    haveI := fun i => isTopologicalGroup_Hi K L A i
    haveI := fun i => t2Space_Hi K L A i
    haveI := fun i => locallyCompactSpace_Hi K L A i
    haveI := fun i => secondCountableTopology_Hi K L A i

    letI mG' : MeasurableSpace (∀ j : ι', Gi A j) := borel _
    haveI : BorelSpace (∀ j : ι', Gi A j) := ⟨rfl⟩
    letI mH' : MeasurableSpace (∀ j : ι', Hi K L A j) := borel _
    haveI : BorelSpace (∀ j : ι', Hi K L A j) := ⟨rfl⟩
    obtain ⟨-, ihB, ihCL, ihCK⟩ := ih' MeasureTheory.Measure.haar inferInstance MeasureTheory.Measure.haar inferInstance
      (fun _ => 0) ⟨⟨fun _ => 0, contDiff_const, fun _ => rfl⟩, HasCompactSupport.zero⟩
      (fun _ => 0) ⟨⟨fun _ => 0, contDiff_const, fun _ => rfl⟩, HasCompactSupport.zero⟩
      (by
        intro γ δ y _ _ _ τ τ' _ _ _ _ I I' hI' hI
        obtain ⟨W, -, -, -, -, rfl⟩ := hI'
        obtain ⟨w, -, -, -, -, rfl⟩ := hI
        simp) hlt
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro δ y hnc τ τ' hτ hτ' hτ'i hcpl I I' hI' hI
      letI mG₀ : MeasurableSpace (Gi A i₀) := glBorelOf (A i₀)
      haveI : BorelSpace (Gi A i₀) := borelSpace_glBorelOf _
      letI mH₀ : MeasurableSpace (Hi K L A i₀) := glBorelOf (L ⊗[K] A i₀)
      haveI : BorelSpace (Hi K L A i₀) := borelSpace_glBorelOf _
      haveI := hμ i₀; haveI := hμ' i₀

      set ν₂ : Measure (∀ j : ι', Gi A j) := MeasureTheory.Measure.haar with hν₂def
      set ν₂' : Measure (∀ j : ι', Hi K L A j) := MeasureTheory.Measure.haar with hν₂'def
      have hν₂ : ν₂.IsHaarMeasure := by rw [hν₂def]; infer_instance
      have hν₂' : ν₂'.IsHaarMeasure := by rw [hν₂'def]; infer_instance
      have hνb : @Measure.IsHaarMeasure _ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eG A i₀) ν) := by
        letI : MeasurableSpace (∀ i, Gi A i) := borel _; haveI : BorelSpace (∀ i, Gi A i) := ⟨rfl⟩
        letI : MeasurableSpace ((Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j)) := borel _; haveI : BorelSpace ((Gi A i₀) × (∀ j : {j // j ≠ i₀}, Gi A j)) := ⟨rfl⟩
        haveI := hν
        exact (eG A i₀).isHaarMeasure_map ν
      have hνb' : @Measure.IsHaarMeasure _ _ _ (borel _) (@Measure.map _ _ (borel _) (borel _) (eH K L A i₀) ν') := by
        letI : MeasurableSpace (∀ i, Hi K L A i) := borel _; haveI : BorelSpace (∀ i, Hi K L A i) := ⟨rfl⟩
        letI : MeasurableSpace ((Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j)) := borel _; haveI : BorelSpace ((Hi K L A i₀) × (∀ j : {j // j ≠ i₀}, Hi K L A j)) := ⟨rfl⟩
        haveI := hν'
        exact (eH K L A i₀).isHaarMeasure_map ν'
      obtain ⟨cK, hcK0, hcK⟩ := GroupOrbital.exists_haarRatio _ hνb (μ i₀) (hμ i₀) ν₂ hν₂
      obtain ⟨cL, hcL0, hcL⟩ := GroupOrbital.exists_haarRatio _ hνb' (μ' i₀) (hμ' i₀) ν₂' hν₂'

      obtain ⟨τ₁, τ₂, τ₁', τ₂', hτ₁, hτ₂, hτ₁', hτ₂', hτbeq, hτb'eq, hc₁, hc₂⟩ :=
        step_split K L σ A i₀ _ δ y τ τ' hτ hτ' hcpl
      obtain ⟨hτ₁i, hτ₁'i⟩ := step_inv_head K L σ A i₀ μ hμ hμr (c i₀) (δ i₀) (y i₀) τ₁ τ₁' hτ₁ hc₁
      obtain ⟨hτ₂i, hτ₂'i⟩ := step_inv_tail K L σ A i₀ μ hμ hμr c (fun j => δ j) (fun j => y j) τ₂ τ₂' hτ₂ hc₂

      letI mC₁ : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)} : Set (Gi A i₀))) := borel _
      haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)} : Set (Gi A i₀))) := ⟨rfl⟩
      letI mC₂ : MeasurableSpace (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := borel _
      haveI : BorelSpace (Subgroup.centralizer ({(fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))} : Set (∀ j : {j // j ≠ i₀}, Gi A j))) := ⟨rfl⟩
      letI mT₁ : MeasurableSpace (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) := borel _
      haveI : BorelSpace (sigmaCentralizer (θfam K L σ A i₀) (δ i₀)) := ⟨rfl⟩
      letI mT₂ : MeasurableSpace (sigmaCentralizer (η' K L σ A i₀) (fun j : ι' => δ j)) := borel _
      haveI : BorelSpace (sigmaCentralizer (η' K L σ A i₀) (fun j : ι' => δ j)) := ⟨rfl⟩
      haveI := hτ₁; haveI := hτ₂; haveI := hτ₁'; haveI := hτ₂'

      haveI := hμr i₀
      obtain ⟨ω₀, hω₀c, hω₀0, hω₀s, hω₀1⟩ := exists_central_sectionK (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀))
        (fun g => scalar_central (c i₀) g) (μ i₀) τ₁
      obtain ⟨μpi, hμpi, hμpir⟩ : ∃ μ₀ : @Measure (∀ j : {j // j ≠ i₀}, Gi A j) (borel _),
          @Measure.IsHaarMeasure _ _ _ (borel _) μ₀ ∧ @Measure.IsMulRightInvariant _ (borel _) _ μ₀ := by
        letI mGj : ∀ j : ι', MeasurableSpace (Gi A j) := fun j => glBorelOf (A j)
        haveI : ∀ j : ι', BorelSpace (Gi A j) := fun j => borelSpace_glBorelOf (A j)
        haveI := fun j : ι' => hμ j
        haveI := fun j : ι' => hμr j
        have hpi : (borel (∀ j : {j // j ≠ i₀}, Gi A j)) = MeasurableSpace.pi :=
          (@BorelSpace.measurable_eq (∀ j : {j // j ≠ i₀}, Gi A j) _ MeasurableSpace.pi Pi.borelSpace).symm
        rw [hpi]
        exact ⟨Measure.pi fun j : ι' => μ j, inferInstance, inferInstance⟩
      haveI := hμpi; haveI := hμpir
      obtain ⟨ω', hω'c, hω'0, hω's, hω'1⟩ := exists_central_sectionK (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j))
        (fun g => scalar_family_central (fun j : ι' => A j) (fun j => c j) g) μpi τ₂

      have hΦb : Continuous (Φ ∘ (eH K L A i₀).symm) := hΦ.1.elim fun Φ₁ h => by
        exact (h.1.continuous.comp (continuous_pi fun i => (hεL i).comp (continuous_apply i))).congr
          (fun g => (h.2 g).symm) |>.comp (eH K L A i₀).symm.continuous
      have hΦcont : Continuous Φ := hΦ.1.elim fun Φ₁ h =>
        (h.1.continuous.comp (continuous_pi fun i => (hεL i).comp (continuous_apply i))).congr (fun g => (h.2 g).symm)
      have hFcont : Continuous F := hF.1.elim fun F₁ h =>
        (h.1.continuous.comp (continuous_pi fun i => (hεK i).comp (continuous_apply i))).congr (fun g => (h.2 g).symm)
      have hΦbc : HasCompactSupport (Φ ∘ (eH K L A i₀).symm) :=
        hΦ.2.comp_isClosedEmbedding (eH K L A i₀).symm.toHomeomorph.isClosedEmbedding
      obtain ⟨ψ₁, hψ₁c, hψ₁s, hψ₁1⟩ := S30SemilocalCent.Env.exists_bump_eq_one (hΦbc.isCompact.image continuous_fst)
      obtain ⟨ψ₂, hψ₂c, hψ₂s, hψ₂1⟩ := S30SemilocalCent.Env.exists_bump_eq_one (hΦbc.isCompact.image continuous_snd)
      have hsc : ∃ d : (L ⊗[K] A i₀)ˣ,
          IsSigmaConjugate K L (A i₀) σ (δ i₀) (Matrix.GeneralLinearGroup.scalar (Fin 2) d) :=
        AutomorphicForm.exists_isSigmaConjugate_scalar_of_coupled K L σ (A i₀)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i₀)) ⟨c i₀, rfl⟩ (δ i₀) (y i₀) τ₁ τ₁' inferInstance hc₁
      obtain ⟨W₀, ⟨hW₀0, hW₀m, hW₀s, hW₀1⟩, hW₀c⟩ := hsecL i₀ (δ i₀) (Or.inr hsc) τ₁' hτ₁' hτ₁'i ψ₁ hψ₁c hψ₁s
      have hW₀E : ∀ x₁ : (Hi K L A i₀), (∃ z : (∀ j : {j // j ≠ i₀}, Hi K L A j),
          Φ ((eH K L A i₀).symm (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁, z)) ≠ 0) →
          @integral _ ℝ _ _ (borel _) τ₁' (fun t => W₀ ((t : (Hi K L A i₀)) * x₁)) = 1 := by
        rintro x₁ ⟨z, hz⟩
        apply hW₀1 x₁
        have h1 := hψ₁1 (x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁)
          ⟨(x₁⁻¹ * δ i₀ * (θfam K L σ A i₀) x₁, z), subset_tsupport _ hz, rfl⟩
        rw [h1]
        exact one_ne_zero
      obtain ⟨W', hW'c, hW'0, hW's, hW'1⟩ := ihB (fun j => δ j) (fun j => y j) (fun j => hnc j) τ₂ τ₂' hτ₂ hτ₂' hτ₂'i
        hc₂ ψ₂ hψ₂c hψ₂s
      have hW'E : ∀ x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j), (∃ z : (Hi K L A i₀),
          Φ ((eH K L A i₀).symm (z, x₂⁻¹ * (fun j : ι' => δ j) * (η' K L σ A i₀) x₂)) ≠ 0) →
          @integral _ ℝ _ _ (borel _) τ₂' (fun t => W' ((t : (∀ j : {j // j ≠ i₀}, Hi K L A j)) * x₂)) = 1 := by
        rintro x₂ ⟨z, hz⟩
        apply hW'1 x₂
        have h1 := hψ₂1 (x₂⁻¹ * (fun j : ι' => δ j) * (η' K L σ A i₀) x₂)
          ⟨(z, x₂⁻¹ * (fun j : ι' => δ j) * (η' K L σ A i₀) x₂), subset_tsupport _ hz, rfl⟩
        have h2 : ψ₂ (x₂⁻¹ * (fun j : ι' => δ j) * (η' K L σ A i₀) x₂) ≠ 0 := by rw [h1]; exact one_ne_zero
        exact h2
      have hW'm : Measurable[borel (∀ j : {j // j ≠ i₀}, Hi K L A j)] W' := hW'c.measurable
      have hω'm : Measurable[borel (∀ j : {j // j ≠ i₀}, Gi A j)] ω' := hω'c.measurable

      have hΦpeel := smooth_through_peel i₀ (Hi K L A) Y εL Φ hΦ.1
      have hFpeel := smooth_through_peel i₀ (Gi A) X εK F hF.1
      have hFbc : HasCompactSupport (F ∘ (eG A i₀).symm) :=
        hF.2.comp_isClosedEmbedding (eG A i₀).symm.toHomeomorph.isClosedEmbedding
      have hε₂L : Continuous (fun g' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => fun j : ι' => εL j (g' j)) :=
        continuous_pi fun j => (hεL j).comp (continuous_apply j)
      have hε₂K : Continuous (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => fun j : ι' => εK j (g' j)) :=
        continuous_pi fun j => (hεK j).comp (continuous_apply j)
      have hκL' : Continuous (fun x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j) => x₂⁻¹ * (fun j : ι' => δ j) * (η' K L σ A i₀) x₂) :=
        (continuous_inv.mul continuous_const).mul (continuous_η' K L σ A i₀)
      have hκK' : Continuous (fun x₂ : (∀ j : {j // j ≠ i₀}, Gi A j) => x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂) :=
        (continuous_inv.mul continuous_const).mul continuous_id

      obtain ⟨hΦ₀s, hΦ₀cs, hΦ₀cont⟩ := S30SemilocalCent.Partial.partial_snd (εL i₀) (hεL i₀) _ hε₂L ν₂'
        (Φ ∘ (eH K L A i₀).symm) hΦpeel hΦbc _ hκL' W' hW'c hW's
      obtain ⟨⟨F₂, hF₂s, hF₂rep⟩, hF₀cs, hF₀cont⟩ := S30SemilocalCent.Partial.partial_snd (εK i₀) (hεK i₀) _ hε₂K ν₂
        (F ∘ (eG A i₀).symm) hFpeel hFbc _ hκK' ω' hω'c hω's

      have hcent : ∀ (γ₀ : (Gi A i₀)) (δ₀ y₀ : (Hi K L A i₀)), IsRegularSemisimple γ₀ →
      IsRegularSemisimple (normString K L (A i₀) σ δ₀) → IsNormConjugator K L (A i₀) σ γ₀ δ₀ y₀ →
      ∀ (τ₀ : @Measure (Subgroup.centralizer ({γ₀} : Set (Gi A i₀))) (borel _))
        (τ₀' : @Measure (sigmaCentralizer (θfam K L σ A i₀) δ₀) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ₀ → @Measure.IsHaarMeasure _ _ _ (borel _) τ₀' →
        @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
            (fun t : sigmaCentralizer (θfam K L σ A i₀) δ₀ => y₀⁻¹ * (t : (Hi K L A i₀)) * y₀) τ₀' =
          @Measure.map _ _ (borel _) (borel (Hi K L A i₀))
            (fun s : Subgroup.centralizer ({γ₀} : Set (Gi A i₀)) => φfam K L A i₀ (s : (Gi A i₀))) τ₀ →
      ∀ (ω₀ : (Gi A i₀) → ℝ) (W₀ : (Hi K L A i₀) → ℝ),
      Continuous ω₀ → (∀ x, 0 ≤ ω₀ x) → HasCompactSupport ω₀ →
      (∀ (x₁ : (Gi A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Gi A j)), F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, x₂)) ≠ 0 →
        @integral _ ℝ _ _ (borel _) τ₀ (fun t => ω₀ ((t : (Gi A i₀)) * x₁)) = 1) →
      Continuous W₀ → (∀ x, 0 ≤ W₀ x) → HasCompactSupport W₀ →
      (∀ (x₁ : (Hi K L A i₀)) (x₂ : (∀ j : {j // j ≠ i₀}, Hi K L A j)), Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, x₂)) ≠ 0 →
        @integral _ ℝ _ _ (borel _) τ₀' (fun t => W₀ ((t : (Hi K L A i₀)) * x₁)) = 1) →
      ∀ J J' : ℂ,
        GroupOrbital.IsValue (η' K L σ A i₀) ν₂' (fun j : {j // j ≠ i₀} => δ j) τ₂'
          (fun h' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
            Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, h')) * (W₀ x₁ : ℂ))) J' →
        GroupOrbital.IsValueC ν₂ (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) τ₂
          (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
            @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
              F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, g')) * (ω₀ x₁ : ℂ))) J →
        J' = J := by
        intro γ₀ δ₀ y₀ hγ₀ hδ₀ hy₀ τ₀ τ₀' hτ₀ hτ₀' hc₀ ω₀ W₀ hω₀c hω₀0 hω₀s hω₀E hW₀c hW₀0 hW₀s hW₀E J J' hJ' hJ
        have hκL : Continuous (fun x₁ : (Hi K L A i₀) => x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁) :=
          (continuous_inv.mul continuous_const).mul (continuous_θfam K L σ A i₀)
        have hκK : Continuous (fun x₁ : (Gi A i₀) => x₁⁻¹ * γ₀ * x₁) :=
          (continuous_inv.mul continuous_const).mul continuous_id
        obtain ⟨hPhi1s, hPhi1cs, -⟩ := S30SemilocalCent.Partial.partial_fst (εL i₀) (hεL i₀) _ hε₂L (μ' i₀)
          (Φ ∘ (eH K L A i₀).symm) hΦpeel hΦbc _ hκL W₀ hW₀c hW₀s
        obtain ⟨⟨F₃, hF₃s, hF₃rep⟩, hF1cs, -⟩ := S30SemilocalCent.Partial.partial_fst (εK i₀) (hεK i₀) _ hε₂K (μ i₀)
          (F ∘ (eG A i₀).symm) hFpeel hFbc _ hκK ω₀ hω₀c hω₀s
        have key := (ih' ν₂ hν₂ ν₂' hν₂'
          (fun g' : (∀ j : {j // j ≠ i₀}, Gi A j) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) *
            @integral _ ℂ _ _ (glBorelOf (A i₀)) (μ i₀) (fun x₁ =>
              F ((eG A i₀).symm (x₁⁻¹ * γ₀ * x₁, g')) * (ω₀ x₁ : ℂ)))
          ⟨⟨fun q => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * F₃ q, contDiff_const.mul hF₃s, fun g' => by
              have h := hF₃rep g'
              simp only [Function.comp_apply] at h
              beta_reduce
              rw [← h]⟩,
            hF1cs.mul_left⟩
          (fun h' : (∀ j : {j // j ≠ i₀}, Hi K L A j) => @integral _ ℂ _ _ (glBorelOf (L ⊗[K] A i₀)) (μ' i₀) (fun x₁ =>
              Φ ((eH K L A i₀).symm (x₁⁻¹ * δ₀ * (θfam K L σ A i₀) x₁, h')) * (W₀ x₁ : ℂ)))
          ⟨hPhi1s, hPhi1cs⟩
          (fun γ' δ' y' g1 g2 g3 τ₂ τ₂' g4 g5 g6 g7 J J' gJ' gJ =>
            step_REG K L σ A i₀ μ hμ μ' hμ' ν hν ν' hν' ν₂ hν₂ ν₂' hν₂' cK cL hcK0 hcL0 hcK hcL F hFcont hF.2 Φ hΦcont hΦ.2
              (fun γ δ y h1 h2 h3 τ τ' h4 h5 h6 h7 I I' hI' hI =>
                hreg γ δ y h1 h2 h3 τ τ' h4 h5 h6 h7 I I' ((GroupOrbital.isValue_iff_inline _ _ _ _ _ _).1 hI')
                  ((GroupOrbital.isValueC_iff_inline _ _ _ _ _).1 hI))
              ihCL ihCK γ₀ hγ₀ δ₀ y₀ hδ₀ hy₀ τ₀ τ₀' hτ₀ hτ₀' hc₀ ω₀ hω₀c hω₀0 hω₀s hω₀E W₀ hW₀c hW₀0 hW₀s hW₀E
              γ' δ' y' g1 g2 g3 τ₂ τ₂' g4 g5 g6 g7 J J' ((GroupOrbital.isValue_iff_inline _ _ _ _ _ _).2 gJ')
              ((GroupOrbital.isValueC_iff_inline _ _ _ _ _).2 gJ))
          hlt).1
        exact key (fun j => δ j) (fun j => y j) (fun j => hnc j) τ₂ τ₂' hτ₂ hτ₂' hτ₂'i hc₂ J J'
          ((GroupOrbital.isValue_iff_inline _ _ _ _ _ _).1 hJ') ((GroupOrbital.isValueC_iff_inline _ _ _ _ _).1 hJ)

      have hone := heng i₀ _ ⟨hΦ₀s, hΦ₀cs⟩
        (fun g : (Gi A i₀) => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * ∫ x₂, (F ∘ (eG A i₀).symm) (g, x₂⁻¹ * (fun j : {j // j ≠ i₀} => Matrix.GeneralLinearGroup.scalar (Fin 2) (c j) : (∀ j : {j // j ≠ i₀}, Gi A j)) * x₂) * (ω' x₂ : ℂ) ∂ν₂)
        ⟨⟨fun q => (((cK : ℝ) : ℂ) / ((cL : ℝ) : ℂ)) * F₂ q, contDiff_const.mul hF₂s, fun g => by
            have h := hF₂rep g
            beta_reduce
            rw [← h]⟩,
          hF₀cs.mul_left⟩
        ⟨Set.univ, Filter.univ_mem,
          step_ONE K L σ A i₀ c μ hμ μ' hμ' ν₂ hν₂ ν₂' hν₂' cK cL F hFcont hF.2 Φ hΦcont hΦ.2 (hsecK i₀) (hsecL i₀)
            (fun j => δ j) τ₂ τ₂' ω' hω'c hω'0 hω's hω'm hω'1 W' hW'c hW'0 hW's hW'm hW'E hcent hΦ₀cont
            (continuous_const.mul hF₀cont)⟩
        (δ i₀) (y i₀) (hnc i₀) τ₁ τ₁' hτ₁ hτ₁' hτ₁'i hc₁
      exact step_ASM K L σ A i₀ c μ hμ μ' hμ' ν hν ν' hν' ν₂ hν₂ ν₂' hν₂' cK cL hcK0 hcL0 hcK hcL F hFcont hF.2 Φ hΦcont hΦ.2
        δ τ τ' τ₁ τ₂ τ₁' τ₂' hτ₁ hτ₂ hτ₁' hτ₂' hτ₁i hτ₂i hτ₁'i hτ₂'i hτbeq hτb'eq ω₀ hω₀c hω₀0 hω₀s hω₀1
        ω' hω'c hω'0 hω's hω'1 W₀ hW₀c hW₀0 hW₀s hW₀E W' hW'c hW'0 hW's hW'E hone I I'
        ((GroupOrbital.isValue_iff_inline _ _ _ _ _ _).2 hI') ((GroupOrbital.isValueC_iff_inline _ _ _ _ _).2 hI)
    ·
      intro δ y hnc τ τ' hτ hτ' hτ'i hcpl Ψ hΨ hΨc
      exact step_B K L σ A i₀ c μ hμ hμr (hsecL i₀) ihB δ y hnc τ τ' hτ hτ' hτ'i hcpl Ψ hΨ hΨc
    ·
      intro δ hδ τ' hτ' hτ'i Ψ hΨ hΨc
      exact step_CL K L σ A i₀ (hsecL i₀) ihCL δ hδ τ' hτ' hτ'i Ψ hΨ hΨc
    ·
      intro γ hγ τ hτ Ψ hΨ hΨc
      exact step_CK A i₀ (hsecK i₀) ihCK γ hγ τ hτ Ψ hΨ hΨc

end S_AutomorphicForm_semilocal_central_transfer_peel_step
end P2MW
export P2MW.S_AutomorphicForm_semilocal_central_transfer_peel_step (solution)
