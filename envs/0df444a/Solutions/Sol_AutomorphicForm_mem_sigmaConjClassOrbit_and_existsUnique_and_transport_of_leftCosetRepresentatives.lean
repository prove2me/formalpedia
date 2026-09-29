-- Prove2me | solution 1 for AutomorphicForm.mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f997321e-875c-5098-93c7-b5dfcf9713f4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar sigmaAdelicAct sigmaAdelicAct_globalPoints"
namespace C1CP
p2m_open "AutomorphicForm"

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  ext i j
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar, M4aHerbrand.IdeleGaloisDescent.unitsAct,
      Matrix.diagonal]

theorem globalPoints_eq_centralScalar_of_val_eq_scalar (ζ : GL (Fin 2) L) (u : Lˣ)
    (h : (ζ : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) (u : L)) :
    AutomorphicForm.globalPoints (𝓞 L) L ζ =
      AutomorphicForm.centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) := by
  ext i j
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar]
  have hij := congrFun (congrFun h i) j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.scalar_apply] at hij ⊢ <;>
    simp [hij]

theorem centralScalar_mem_center (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L z ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨z, rfl⟩

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * y = y * AutomorphicForm.centralScalar (𝓞 L) L z :=
  ((Subgroup.mem_center_iff.mp (centralScalar_mem_center L z)) y).symm

theorem scalar_mem_center (ζ : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) ζ ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨ζ, rfl⟩

theorem exists_scalar_eq_of_mem_center {g : GL (Fin 2) L} (hg : g ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ ζ : Lˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) ζ = g := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  exact hg

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Lˣ → GL (Fin 2) L) := by
  intro a b h
  have h00 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using h00

end AutomorphicForm.C1CP

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives.AutomorphicForm AutomorphicForm.C1CP in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ) :
    (∀ (i : ι) (ζ : Lˣ),
      r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i))⁻¹ ∈ I) ∧
    (∀ δ ∈ I, ∃! p : ι × Lˣ,
      δ = r p.1 * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r p.1))⁻¹) ∧
    (∀ (i : ι) (ζ : Lˣ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L
          (r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i))⁻¹) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
      ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L
              (D.unitsAct σ⁻¹ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ) * z) *
            ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) := by
  classical
  set S : Lˣ →* GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) with hS
  set σM : GL (Fin 2) L →* GL (Fin 2) L := Matrix.GeneralLinearGroup.map (σ : L →+* L) with hσM
  have hSZ : ∀ ζ : Lˣ, S ζ ∈ Subgroup.center (GL (Fin 2) L) := fun ζ => by
    rw [hS]; exact scalar_mem_center L ζ
  have hScomm : ∀ (ζ : Lˣ) (g : GL (Fin 2) L), g * S ζ = S ζ * g := fun ζ g =>
    Subgroup.mem_center_iff.mp (hSZ ζ) g
  have hZS : ∀ {g : GL (Fin 2) L}, g ∈ Subgroup.center (GL (Fin 2) L) → ∃ ζ : Lˣ, S ζ = g := fun hg => by
    rw [hS]; exact exists_scalar_eq_of_mem_center L hg
  have hSinj : ∀ {a b : Lˣ}, S a = S b → a = b := fun h => scalar_injective L (by rwa [hS] at h)

  have part1 : ∀ (i : ι) (ζ : Lˣ), r i * δ₀ * S ζ * (σM (r i))⁻¹ ∈ I := by
    intro i ζ
    rw [hI]
    refine ⟨r i, ?_⟩
    have : δ₀⁻¹ * ((r i)⁻¹ * (r i * δ₀ * S ζ * (σM (r i))⁻¹) * σM (r i)) = S ζ := by group
    rw [this]
    exact hSZ ζ
  refine ⟨part1, ?_, ?_⟩
  ·
    intro δ hδ
    obtain ⟨g, hg⟩ := (hI δ).mp hδ
    obtain ⟨ζ₁, hζ₁⟩ := hZS hg
    obtain ⟨i, hi, -⟩ := hr g
    set lam : GL (Fin 2) L := (r i)⁻¹ * g with hlam
    obtain ⟨ζ₂, hζ₂⟩ := hZS ((hΛ lam).mp hi)
    have e1 : δ = g * δ₀ * S ζ₁ * (σM g)⁻¹ := by
      calc δ = g * δ₀ * (δ₀⁻¹ * (g⁻¹ * δ * σM g)) * (σM g)⁻¹ := by group
        _ = g * δ₀ * S ζ₁ * (σM g)⁻¹ := by rw [hζ₁]
    have e2 : lam * δ₀ = δ₀ * S ζ₂ * σM lam := by
      calc lam * δ₀ = δ₀ * (δ₀⁻¹ * (lam * δ₀ * (σM lam)⁻¹)) * σM lam := by group
        _ = δ₀ * S ζ₂ * σM lam := by rw [hζ₂]
    have hg' : g = r i * lam := by rw [hlam]; group
    have key : δ = r i * δ₀ * S (ζ₂ * ζ₁) * (σM (r i))⁻¹ := by
      rw [hg'] at e1
      calc δ = r i * lam * δ₀ * S ζ₁ * (σM (r i * lam))⁻¹ := e1
        _ = r i * (lam * δ₀) * S ζ₁ * ((σM lam)⁻¹ * (σM (r i))⁻¹) := by rw [map_mul]; group
        _ = r i * (δ₀ * S ζ₂ * σM lam) * S ζ₁ * ((σM lam)⁻¹ * (σM (r i))⁻¹) := by rw [e2]
        _ = r i * δ₀ * S ζ₂ * (σM lam * S ζ₁) * (σM lam)⁻¹ * (σM (r i))⁻¹ := by group
        _ = r i * δ₀ * S ζ₂ * (S ζ₁ * σM lam) * (σM lam)⁻¹ * (σM (r i))⁻¹ := by rw [hScomm ζ₁ (σM lam)]
        _ = r i * δ₀ * S (ζ₂ * ζ₁) * (σM (r i))⁻¹ := by rw [map_mul S]; group
    refine ⟨(i, ζ₂ * ζ₁), key, ?_⟩
    rintro ⟨j, ζ'⟩ hj
    dsimp only at hj
    have E : r j * δ₀ * S ζ' * (σM (r j))⁻¹ = r i * δ₀ * S (ζ₂ * ζ₁) * (σM (r i))⁻¹ := hj.symm.trans key

    have hc1 : (σM (r j))⁻¹ * S ζ' = S ζ' * (σM (r j))⁻¹ := hScomm ζ' (σM (r j))⁻¹
    have E2 : r j * δ₀ * (σM (r j))⁻¹ = r i * δ₀ * S (ζ₂ * ζ₁) * (σM (r i))⁻¹ * (S ζ')⁻¹ := by
      calc r j * δ₀ * (σM (r j))⁻¹ = r j * δ₀ * ((σM (r j))⁻¹ * S ζ') * (S ζ')⁻¹ := by group
        _ = r j * δ₀ * (S ζ' * (σM (r j))⁻¹) * (S ζ')⁻¹ := by rw [hc1]
        _ = (r j * δ₀ * S ζ' * (σM (r j))⁻¹) * (S ζ')⁻¹ := by group
        _ = r i * δ₀ * S (ζ₂ * ζ₁) * (σM (r i))⁻¹ * (S ζ')⁻¹ := by rw [E]
    have hc2 : (S ζ')⁻¹ * σM (r i) = σM (r i) * (S ζ')⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hSZ ζ')) (σM (r i))).symm
    have hT : δ₀⁻¹ * ((r i)⁻¹ * r j * δ₀ * (σM ((r i)⁻¹ * r j))⁻¹) = S (ζ₂ * ζ₁) * (S ζ')⁻¹ := by
      rw [map_mul σM, map_inv σM]
      calc δ₀⁻¹ * ((r i)⁻¹ * r j * δ₀ * ((σM (r i))⁻¹ * σM (r j))⁻¹)
          = δ₀⁻¹ * (r i)⁻¹ * (r j * δ₀ * (σM (r j))⁻¹) * σM (r i) := by group
        _ = δ₀⁻¹ * (r i)⁻¹ * (r i * δ₀ * S (ζ₂ * ζ₁) * (σM (r i))⁻¹ * (S ζ')⁻¹) * σM (r i) := by rw [E2]
        _ = S (ζ₂ * ζ₁) * (σM (r i))⁻¹ * ((S ζ')⁻¹ * σM (r i)) := by group
        _ = S (ζ₂ * ζ₁) * (σM (r i))⁻¹ * (σM (r i) * (S ζ')⁻¹) := by rw [hc2]
        _ = S (ζ₂ * ζ₁) * (S ζ')⁻¹ := by group
    have hγ : (r i)⁻¹ * r j ∈ Λ := by
      rw [hΛ, hT, ← map_inv S, ← map_mul S]
      exact hSZ _
    have hij : i = j := by
      obtain ⟨k, -, hkuniq⟩ := hr (r j)
      have h1 : i = k := hkuniq i hγ
      have h2 : j = k := hkuniq j (by show (r j)⁻¹ * r j ∈ Λ; rw [inv_mul_cancel]; exact Λ.one_mem)
      exact h1.trans h2.symm
    subst hij
    have hζζ : S ζ' = S (ζ₂ * ζ₁) := mul_left_cancel (mul_right_cancel E)
    rw [hSinj hζζ]
  ·
    intro i ζ x z
    set ζh : (AdeleRing (𝓞 L) L)ˣ := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ with hζh
    set gp := AutomorphicForm.globalPoints (𝓞 L) L with hgp
    set σA := AutomorphicForm.sigmaAdelicAct K L D σ with hσA
    set c := AutomorphicForm.centralScalar (𝓞 L) L with hc
    have L1 : gp (S ζ) = c ζh := by
      rw [hgp, hc, hS, hζh]
      exact globalPoints_eq_centralScalar_of_val_eq_scalar L _ ζ rfl
    have L2 : ∀ g : GL (Fin 2) L, gp (σM g) = σA (gp g) := fun g => by
      rw [hgp, hσA, hσM]
      exact (AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g).symm
    have L3 : ∀ w : (AdeleRing (𝓞 L) L)ˣ, σA (c w) = c (D.unitsAct σ w) := fun w => by
      rw [hσA, hc]; exact sigmaAdelicAct_centralScalar K L D σ w
    have L4 : (D.unitsAct σ) ((D.unitsAct σ)⁻¹ ζh) = ζh := MulAut.apply_inv_self _ _ _
    have hcomm : (σA (gp (r i)))⁻¹ * c (D.unitsAct σ z) = c (D.unitsAct σ z) * (σA (gp (r i)))⁻¹ := by
      rw [hc]; exact (centralScalar_comm L _ _).symm
    simp only [map_mul, map_inv, L1, L2, L3, L4]
    calc x⁻¹ * (gp (r i) * gp δ₀ * c ζh * (σA (gp (r i)))⁻¹) * (c (D.unitsAct σ z) * σA x)
        = x⁻¹ * gp (r i) * gp δ₀ * c ζh * ((σA (gp (r i)))⁻¹ * c (D.unitsAct σ z)) * σA x := by group
      _ = x⁻¹ * gp (r i) * gp δ₀ * c ζh * (c (D.unitsAct σ z) * (σA (gp (r i)))⁻¹) * σA x := by rw [hcomm]
      _ = ((gp (r i))⁻¹ * x)⁻¹ * gp δ₀ * (c ζh * c (D.unitsAct σ z) * ((σA (gp (r i)))⁻¹ * σA x)) := by group

end S_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
end P2MW
export P2MW.S_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives (solution)
