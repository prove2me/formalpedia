-- Prove2me | solution 1 for AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6863693d-49b9-5905-805d-b1900d644b2f

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

namespace SplitCoordAux
open AutomorphicForm AutomorphicForm.SplitPlace

def unitsCME {R S : Type} [Monoid R] [Monoid S] [TopologicalSpace R] [TopologicalSpace S]
    (e : R ≃* S) (he : Continuous e) (he' : Continuous e.symm) : Rˣ ≃ₜ* Sˣ where
  __ := Units.mapEquiv e
  continuous_toFun := he.units_map e.toMonoidHom
  continuous_invFun := he'.units_map e.symm.toMonoidHom

theorem continuous_piRingEquiv (F : Type) [Semiring F] [TopologicalSpace F] (m : ℕ) :
    Continuous (Matrix.piRingEquiv (β := fun _ : Fin m => F) (n := Fin 2)) :=
  continuous_pi fun i => continuous_id.matrix_map (continuous_apply i)

theorem continuous_piRingEquiv_symm (F : Type) [Semiring F] [TopologicalSpace F] (m : ℕ) :
    Continuous (Matrix.piRingEquiv (β := fun _ : Fin m => F) (n := Fin 2)).symm :=
  continuous_matrix fun a b => continuous_pi fun i => (continuous_apply i).matrix_elem a b

theorem iterate_add_one_val {n : ℕ} (m : ℕ) (j : Fin (n + 1)) :
    (((fun x : Fin (n + 1) => x + 1)^[m] j) : ℕ) = (j + m) % (n + 1) := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt j.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply', Fin.val_add, ih, Fin.val_one', Nat.add_mod_mod,
      Nat.mod_add_mod, ← Nat.add_assoc]

theorem iterate_add_one_eq_add {n : ℕ} (j k : Fin (n + 1)) :
    (fun x : Fin (n + 1) => x + 1)^[(k : ℕ)] j = j + k := by
  apply Fin.ext
  rw [iterate_add_one_val, Fin.val_add]

theorem apply_iterate_of_apply_eq {X Y : Type} {n : ℕ} (f : X → X) (θ : X → Fin (n + 1) → Y)
    (hθ : ∀ g i, θ (f g) i = θ g (i + 1)) (k : ℕ) (g : X) (i : Fin (n + 1)) :
    θ (f^[k] g) i = θ g ((fun x : Fin (n + 1) => x + 1)^[k] i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', hθ, ih, Function.iterate_succ_apply]

theorem apply_iterate_val_of_apply_eq {X Y : Type} {n : ℕ} (f : X → X) (θ : X → Fin (n + 1) → Y)
    (hθ : ∀ g i, θ (f g) i = θ g (i + 1)) (g : X) (j k : Fin (n + 1)) :
    θ (f^[(k : ℕ)] g) j = θ g (j + k) := by
  rw [apply_iterate_of_apply_eq f θ hθ, iterate_add_one_eq_add]

theorem secondCountableTopology_gl (A : Type) [CommRing A] [TopologicalSpace A] [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_gl (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem exists_map_eq_smul_pi {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i))
    [∀ i, (ν i).IsHaarMeasure] (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν := by
  haveI : (Measure.map Θ μ).IsHaarMeasure := Θ.isHaarMeasure_map μ hΘ hΘs
  exact ⟨Measure.haarScalarFactor (Measure.map Θ μ) (Measure.pi ν),
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end SplitCoordAux

open SplitCoordAux in

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA) :
    letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
    Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) ∧
    Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ).symm ∧
    (∀ (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.sigmaGL K L A σ g) j =
        AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ g (j + 1)) ∧
    (∀ g : GL (Fin 2) A,
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.toTensorGL K L A g) = fun _ => g) ∧
    (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) j =
        (List.ofFn fun k : Fin (Module.finrank K L - 1 + 1) =>
          AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ (j + k)).prod) ∧
    (∀ δ : GL (Fin 2) (L ⊗[K] A),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) 0 =
        (List.ofFn (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ)).prod) ∧
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) μL =
        c • Measure.pi (fun _ : Fin (Module.finrank K L - 1 + 1) => μA) := by
  classical

  haveI : IsTopologicalRing (L ⊗[K] A) := AutomorphicForm.isTopologicalRing_tensor K L A

  have hcψ : Continuous (AutomorphicForm.SplitPlace.psiEquiv A σ ι hdeg hσ) :=
    (AutomorphicForm.SplitPlace.psiHomeomorph A σ ι hdeg hσ).continuous
  have hcψ' : Continuous (AutomorphicForm.SplitPlace.psiEquiv A σ ι hdeg hσ).symm :=
    AutomorphicForm.SplitPlace.continuous_psiEquiv_symm A σ ι hdeg hσ
  have hcM : Continuous ((AutomorphicForm.SplitPlace.psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix (m := Fin 2)).toMulEquiv := by
    show Continuous fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => M.map (AutomorphicForm.SplitPlace.psiEquiv A σ ι hdeg hσ)
    exact continuous_id.matrix_map hcψ
  have hcM' : Continuous ((AutomorphicForm.SplitPlace.psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix (m := Fin 2)).toMulEquiv.symm := by
    show Continuous fun M : Matrix (Fin 2) (Fin 2) (Fin (Module.finrank K L) → A) => M.map (AutomorphicForm.SplitPlace.psiEquiv A σ ι hdeg hσ).symm
    exact continuous_id.matrix_map hcψ'
  let Θ : GL (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L) → GL (Fin 2) A) :=
    ((unitsCME _ hcM hcM').trans
      (unitsCME (Matrix.piRingEquiv (β := fun _ : Fin (Module.finrank K L) => A) (n := Fin 2)).toMulEquiv
        (continuous_piRingEquiv A _) (continuous_piRingEquiv_symm A _))).trans ContinuousMulEquiv.piUnits
  have hΘ : ∀ g, Θ g = AutomorphicForm.SplitPlace.psiGL A σ ι hdeg hσ g := fun g => rfl
  have hcoordsΘ : ∀ g, AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ g =
      AutomorphicForm.SplitPlace.reindex K L (GL (Fin 2) A) (Θ g) := fun g => rfl
  have hcre : Continuous (AutomorphicForm.SplitPlace.reindex K L (GL (Fin 2) A)) :=
    continuous_pi fun j => continuous_apply _
  have hcre' : Continuous (AutomorphicForm.SplitPlace.reindex K L (GL (Fin 2) A)).symm :=
    continuous_pi fun i => continuous_apply _
  have hc1 : Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) := by
    have : ⇑(AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) = (AutomorphicForm.SplitPlace.reindex K L (GL (Fin 2) A)) ∘ Θ := funext hcoordsΘ
    rw [this]; exact hcre.comp Θ.continuous
  have hc2 : Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ).symm := by
    have : ⇑(AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ).symm = Θ.symm ∘ (AutomorphicForm.SplitPlace.reindex K L (GL (Fin 2) A)).symm := by
      funext h; apply (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ).injective
      rw [MulEquiv.apply_symm_apply]; show h = AutomorphicForm.SplitPlace.reindex K L _ (Θ (Θ.symm _)); simp
    rw [this]; exact Θ.symm.continuous.comp hcre'

  have hℓ : Module.finrank K L = Module.finrank K L - 1 + 1 := AutomorphicForm.SplitPlace.finrank_eq_succ K L
  have hσ1 : σ ^ Module.finrank K L = 1 := AutomorphicForm.SplitPlace.pow_finrank_eq_one hdeg σ hσ
  have hσ1' : σ ^ (Module.finrank K L - 1 + 1) = 1 := by rw [← hℓ]; exact hσ1
  have hpow : ∀ j : Fin (Module.finrank K L - 1 + 1),
      σ ^ ((Fin.cast hℓ.symm (j + 1) : Fin (Module.finrank K L)) : ℕ) = σ ^ ((Fin.cast hℓ.symm j : Fin (Module.finrank K L)) : ℕ) * σ := by
    intro j
    rw [Fin.coe_cast, Fin.coe_cast, ← pow_succ, Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last, hσ1', pow_zero]
    · rfl
  have hψσ : ∀ (z : L ⊗[K] A) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.psi K L A σ ι (AutomorphicForm.sigmaTensor K L A σ z) (Fin.cast hℓ.symm j) =
        AutomorphicForm.SplitPlace.psi K L A σ ι z (Fin.cast hℓ.symm (j + 1)) := by
    intro z j
    induction z with
    | zero => simp
    | tmul x a =>
      have hσt : AutomorphicForm.sigmaTensor K L A σ (x ⊗ₜ a) = σ x ⊗ₜ a := rfl
      rw [hσt, AutomorphicForm.SplitPlace.psi_tmul, AutomorphicForm.SplitPlace.psi_tmul, hpow, AlgEquiv.mul_apply]
    | add y w hy hw => simp only [map_add, Pi.add_apply, hy, hw]
  have hshift : ∀ (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.sigmaGL K L A σ g) j =
        AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ g (j + 1) := by
    intro g j
    refine Units.ext (Matrix.ext fun p q => ?_)
    rw [AutomorphicForm.SplitPlace.coords_apply_val, AutomorphicForm.SplitPlace.coords_apply_val]
    exact hψσ _ j
  have hdiag : ∀ g : GL (Fin 2) A,
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.toTensorGL K L A g) = fun _ => g := by
    intro g; funext j
    refine Units.ext (Matrix.ext fun p q => ?_)
    rw [AutomorphicForm.SplitPlace.coords_apply_val]
    show AutomorphicForm.SplitPlace.psi K L A σ ι ((1 : L) ⊗ₜ ((g : Matrix (Fin 2) (Fin 2) A) p q)) _ = _
    rw [AutomorphicForm.SplitPlace.psi_one_tmul]
  have hnorm : ∀ (δ : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) j =
        (List.ofFn fun k : Fin (Module.finrank K L - 1 + 1) =>
          AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ (j + k)).prod := by
    intro δ j
    have hrange : List.range (Module.finrank K L) = List.range (Module.finrank K L - 1 + 1) := congrArg List.range hℓ
    rw [AutomorphicForm.normString, hrange, map_list_prod, Pi.list_prod_apply, List.map_map, List.map_map,
      List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    exact apply_iterate_val_of_apply_eq (⇑(AutomorphicForm.sigmaGL K L A σ))
      (fun g => AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ g) hshift δ j k
  have hnorm0 : ∀ δ : GL (Fin 2) (L ⊗[K] A),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) 0 =
        (List.ofFn (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ)).prod := by
    intro δ; rw [hnorm]; simp only [zero_add]

  letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) A) := AutomorphicForm.borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI : LocallyCompactSpace (GL (Fin 2) A) := locallyCompactSpace_gl A
  haveI : SecondCountableTopology (GL (Fin 2) A) := secondCountableTopology_gl A
  haveI : μL.IsHaarMeasure := hμL
  haveI : μA.IsHaarMeasure := hμA
  obtain ⟨c, hc0, hc⟩ := exists_map_eq_smul_pi μL (fun _ : Fin (Module.finrank K L - 1 + 1) => μA)
    (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) hc1 hc2
  exact ⟨hc1, hc2, hshift, hdiag, hnorm, hnorm0, c, pos_iff_ne_zero.mpr hc0, hc⟩

#print axioms solution

end S_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
end P2MW
export P2MW.S_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi (solution)
