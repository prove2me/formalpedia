-- Prove2me | solution 1 for AutomorphicForm.exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/80353fb0-bcff-5d30-8528-f4121a014469

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL semiLocalIntegers semiLocalIntegralSet one_mem_semiLocalIntegralSet sigmaTensor sigmaGL normString IsNormOf mem_integralUnitsSet localIntegralSet IsRegularSemisimple exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime"
namespace AdelicNormGluing
p2m_open "AutomorphicForm"

section General

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]

def piFin (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K :=
  { (AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K) with
    commutes' := fun _ => rfl }

def piArch : AdeleRing (𝓞 K) K →ₐ[K] InfiniteAdeleRing K :=
  { AdelicLevel.adeleArch (𝓞 K) K with commutes' := fun _ => rfl }

@[scoped simp] theorem piFin_apply (v : HeightOneSpectrum (𝓞 K)) (a : AdeleRing (𝓞 K) K) :
    piFin K v a = a.2 v := rfl

@[scoped simp] theorem piArch_apply (a : AdeleRing (𝓞 K) K) : piArch K a = a.1 := rfl

def compFin (v : HeightOneSpectrum (𝓞 K)) :
    L ⊗[K] AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] v.adicCompletion K :=
  Algebra.TensorProduct.map (AlgHom.id K L) (piFin K v)

def compArch : L ⊗[K] AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] InfiniteAdeleRing K :=
  Algebra.TensorProduct.map (AlgHom.id K L) (piArch K)

@[scoped simp] theorem compFin_tmul (v : HeightOneSpectrum (𝓞 K)) (l : L) (a : AdeleRing (𝓞 K) K) :
    compFin K L v (l ⊗ₜ a) = l ⊗ₜ (a.2 v) := rfl

@[scoped simp] theorem compArch_tmul (l : L) (a : AdeleRing (𝓞 K) K) :
    compArch K L (l ⊗ₜ a) = l ⊗ₜ a.1 := rfl

theorem compFin_includeRight (v : HeightOneSpectrum (𝓞 K)) (a : AdeleRing (𝓞 K) K) :
    compFin K L v (Algebra.TensorProduct.includeRight a) =
      Algebra.TensorProduct.includeRight (a.2 v) := rfl

theorem compArch_includeRight (a : AdeleRing (𝓞 K) K) :
    compArch K L (Algebra.TensorProduct.includeRight a) =
      Algebra.TensorProduct.includeRight a.1 := rfl

theorem compFin_sigmaTensor (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    compFin K L v (sigmaTensor K L (AdeleRing (𝓞 K) K) σ z) =
      sigmaTensor K L (v.adicCompletion K) σ (compFin K L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul l a => rfl

theorem compArch_sigmaTensor (σ : L ≃ₐ[K] L) (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    compArch K L (sigmaTensor K L (AdeleRing (𝓞 K) K) σ z) =
      sigmaTensor K L (InfiniteAdeleRing K) σ (compArch K L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul l a => rfl

section GLmaps

variable {R S : Type} [CommRing R] [CommRing S]

theorem glmap_iterate_comm {f : R →+* S} {τR : R →+* R} {τS : S →+* S}
    (h : ∀ x, f (τR x) = τS (f x)) (n : ℕ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map f ((⇑(Matrix.GeneralLinearGroup.map τR))^[n] g) =
      (⇑(Matrix.GeneralLinearGroup.map τS))^[n] (Matrix.GeneralLinearGroup.map f g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply, h]

end GLmaps

variable (σ : L ≃ₐ[K] L)

theorem glmap_compFin_toTensorGL (v : HeightOneSpectrum (𝓞 K)) (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom (toTensorGL K L (AdeleRing (𝓞 K) K) γ) =
      toTensorGL K L (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) := by
  ext i j
  rfl

theorem glmap_compArch_toTensorGL (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compArch K L).toRingHom (toTensorGL K L (AdeleRing (𝓞 K) K) γ) =
      toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ) := by
  ext i j
  rfl

theorem glmap_compFin_sigmaGL (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom (sigmaGL K L (AdeleRing (𝓞 K) K) σ g) =
      sigmaGL K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom g) := by
  ext i j
  simp only [sigmaGL, Matrix.GeneralLinearGroup.map_apply]
  exact compFin_sigmaTensor K L σ v _

theorem glmap_compArch_sigmaGL (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compArch K L).toRingHom (sigmaGL K L (AdeleRing (𝓞 K) K) σ g) =
      sigmaGL K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (compArch K L).toRingHom g) := by
  ext i j
  simp only [sigmaGL, Matrix.GeneralLinearGroup.map_apply]
  exact compArch_sigmaTensor K L σ _

theorem glmap_compFin_normString (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom δ) := by
  simp only [normString, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, sigmaGL]
  exact glmap_iterate_comm (fun x => compFin_sigmaTensor K L σ v x) i δ

theorem glmap_compArch_normString (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compArch K L).toRingHom (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (compArch K L).toRingHom δ) := by
  simp only [normString, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, sigmaGL]
  exact glmap_iterate_comm (fun x => compArch_sigmaTensor K L σ x) i δ

end General

section Coordinates

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

section Coord

variable (M : Type) [CommRing M] [Algebra K M]

abbrev bL : Module.Basis (Fin (Module.finrank K L)) K L := Module.finBasis K L

def coord (z : L ⊗[K] M) : Fin (Module.finrank K L) → M :=
  fun i => ((bL K L).baseChange M).repr (Algebra.TensorProduct.comm K L M z) i

theorem coord_add (z z' : L ⊗[K] M) : coord K L M (z + z') = coord K L M z + coord K L M z' := by
  funext i; simp [coord]

theorem coord_zero : coord K L M 0 = 0 := by
  funext i; simp [coord]

theorem sum_tmul_coord (z : L ⊗[K] M) :
    ∑ i, (bL K L i) ⊗ₜ[K] (coord K L M z i) = z := by
  apply (Algebra.TensorProduct.comm K L M).injective
  rw [map_sum]
  have h := ((bL K L).baseChange M).sum_repr (Algebra.TensorProduct.comm K L M z)
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Algebra.TensorProduct.comm_tmul, coord, Module.Basis.baseChange_apply]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem coord_sum_tmul (c : Fin (Module.finrank K L) → M) :
    coord K L M (∑ i, (bL K L i) ⊗ₜ[K] c i) = c := by
  funext j
  simp only [coord, map_sum, Algebra.TensorProduct.comm_tmul]
  have : ∀ i, (c i) ⊗ₜ[K] (bL K L i) = (c i) • ((bL K L).baseChange M i) := fun i => by
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp_rw [this]
  simp [Finsupp.single_apply]

theorem coord_tmul (l : L) (m : M) (i : Fin (Module.finrank K L)) :
    coord K L M (l ⊗ₜ m) i = algebraMap K M ((bL K L).repr l i) * m := by
  have hl : l = ∑ j, (bL K L).repr l j • bL K L j := ((bL K L).sum_repr l).symm
  have : l ⊗ₜ[K] m = ∑ j, (bL K L j) ⊗ₜ[K] (algebraMap K M ((bL K L).repr l j) * m) := by
    conv_lhs => rw [hl]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, Algebra.smul_def]
  rw [this, coord_sum_tmul]

variable {M} {N : Type} [CommRing N] [Algebra K N]

theorem coord_map (f : M →ₐ[K] N) (z : L ⊗[K] M) (i : Fin (Module.finrank K L)) :
    coord K L N (Algebra.TensorProduct.map (AlgHom.id K L) f z) i = f (coord K L M z i) := by
  conv_lhs => rw [← sum_tmul_coord K L M z]
  rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [coord_sum_tmul]

theorem eq_of_coord_eq {z z' : L ⊗[K] M} (h : coord K L M z = coord K L M z') : z = z' := by
  rw [← sum_tmul_coord K L M z, ← sum_tmul_coord K L M z', h]

end Coord

end Coordinates

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem eq_of_comp_eq {z z' : L ⊗[K] AdeleRing (𝓞 K) K} (ha : compArch K L z = compArch K L z')
    (hf : ∀ v, compFin K L v z = compFin K L v z') : z = z' := by
  apply eq_of_coord_eq K L (M := AdeleRing (𝓞 K) K)
  funext i
  refine Prod.ext ?_ ?_
  · have := congrArg (fun t => coord K L (InfiniteAdeleRing K) t i) ha
    simpa only [compArch, coord_map, piArch_apply] using this
  · refine FiniteAdeleRing.ext K fun v => ?_
    have := congrArg (fun t => coord K L (v.adicCompletion K) t i) (hf v)
    simpa only [compFin, coord_map, piFin_apply] using this

theorem exists_comp_eq (xa : L ⊗[K] InfiniteAdeleRing K)
    (xf : ∀ v : HeightOneSpectrum (𝓞 K), L ⊗[K] v.adicCompletion K)
    (hint : ∀ i, ∀ᶠ v in Filter.cofinite,
      coord K L (v.adicCompletion K) (xf v) i ∈ v.adicCompletionIntegers K) :
    ∃ z : L ⊗[K] AdeleRing (𝓞 K) K, compArch K L z = xa ∧ ∀ v, compFin K L v z = xf v := by
  let af : Fin (Module.finrank K L) → FiniteAdeleRing (𝓞 K) K :=
    fun i => ⟨fun v => coord K L (v.adicCompletion K) (xf v) i, hint i⟩
  let a : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K :=
    fun i => (coord K L (InfiniteAdeleRing K) xa i, af i)
  refine ⟨∑ i, (bL K L i) ⊗ₜ[K] a i, ?_, fun v => ?_⟩
  · rw [map_sum]
    simp only [compArch_tmul]
    exact sum_tmul_coord K L (InfiniteAdeleRing K) xa
  · rw [map_sum]
    simp only [compFin_tmul]
    exact sum_tmul_coord K L (v.adicCompletion K) (xf v)

variable [NumberField L]

theorem eventually_coord_mem_of_mem_semiLocalIntegers :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ x ∈ semiLocalIntegers K L v, ∀ i,
        coord K L (v.adicCompletion K) x i ∈ v.adicCompletionIntegers K := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite (𝓞 K) (𝓞 L))

  have hgen : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ g ∈ s, ∀ i,
      algebraMap K (v.adicCompletion K) ((bL K L).repr (algebraMap (𝓞 L) L g) i) ∈
        v.adicCompletionIntegers K := by
    rw [Filter.eventually_all_finset]
    intro g _
    rw [Filter.eventually_all]
    intro i
    exact (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((bL K L).repr (algebraMap (𝓞 L) L g) i)).2
  filter_upwards [hgen] with v hv

  have hOL : ∀ y : 𝓞 L, ∀ i,
      algebraMap K (v.adicCompletion K) ((bL K L).repr (algebraMap (𝓞 L) L y) i) ∈
        v.adicCompletionIntegers K := by
    intro y
    have hy : y ∈ Submodule.span (𝓞 K) (s : Set (𝓞 L)) := by rw [hs]; trivial
    refine Submodule.span_induction
      (p := fun (y : 𝓞 L) (_ : y ∈ Submodule.span (𝓞 K) (s : Set (𝓞 L))) => ∀ i,
        algebraMap K (v.adicCompletion K) ((bL K L).repr (algebraMap (𝓞 L) L y) i) ∈
          v.adicCompletionIntegers K)
      ?_ ?_ ?_ ?_ hy
    · intro g hg i
      exact hv g hg i
    · intro i
      rw [map_zero, map_zero, Finsupp.zero_apply, map_zero]
      exact zero_mem _
    · intro y z _ _ hy hz i
      rw [map_add, map_add, Finsupp.add_apply, map_add]
      exact add_mem (hy i) (hz i)
    · intro c y _ hy i
      have : algebraMap (𝓞 L) L (c • y) = (c : K) • algebraMap (𝓞 L) L y := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      exact mul_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v c) (hy i)

  rintro x ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => intro i; simp [coord_zero]
  | add t₁ t₂ h₁ h₂ =>
    intro i
    rw [map_add, coord_add, Pi.add_apply]
    exact add_mem (h₁ i) (h₂ i)
  | tmul y o =>
    intro i
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, coord_tmul]
    exact mul_mem (hOL y i) o.2

omit [NumberField L] in

theorem gl_eq_of_comp_eq {g h : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)}
    (ha : Matrix.GeneralLinearGroup.map (compArch K L).toRingHom g =
      Matrix.GeneralLinearGroup.map (compArch K L).toRingHom h)
    (hf : ∀ v, Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom g =
      Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom h) : g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  apply eq_of_comp_eq K L
  · have := congrArg (fun t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) ha
    simpa only [Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
  · intro v
    have := congrArg (fun t : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) (hf v)
    simpa only [Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this

omit [NumberField L] in

theorem matrix_eq_of_comp_eq {M M' : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)}
    (ha : (compArch K L).toRingHom.mapMatrix M = (compArch K L).toRingHom.mapMatrix M')
    (hf : ∀ v, (compFin K L v).toRingHom.mapMatrix M = (compFin K L v).toRingHom.mapMatrix M') :
    M = M' := by
  ext i j
  apply eq_of_comp_eq K L
  · have := congrArg (fun t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => t i j) ha
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
  · intro v
    have := congrArg (fun t : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) => t i j) (hf v)
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this

theorem gl_exists_comp_eq (ga : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (gf : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hint : ∀ᶠ v in Filter.cofinite, gf v ∈ semiLocalIntegralSet K L v) :
    ∃ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      Matrix.GeneralLinearGroup.map (compArch K L).toRingHom g = ga ∧
      ∀ v, Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom g = gf v := by
  have hden := eventually_coord_mem_of_mem_semiLocalIntegers K L

  have hE : ∀ i j : Fin 2, ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      coord K L (v.adicCompletion K)
        ((gf v : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) k ∈
          v.adicCompletionIntegers K := by
    intro i j k
    filter_upwards [hint, hden] with v h1 h2
    exact h2 _ ((mem_integralUnitsSet.1 h1).1 i j) k
  have hE' : ∀ i j : Fin 2, ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      coord K L (v.adicCompletion K) (((gf v)⁻¹).val i j) k ∈ v.adicCompletionIntegers K := by
    intro i j k
    filter_upwards [hint, hden] with v h1 h2
    exact h2 _ ((mem_integralUnitsSet.1 h1).2 i j) k
  have hD : ∀ i j : Fin 2, ∃ z : L ⊗[K] AdeleRing (𝓞 K) K,
      compArch K L z = (ga : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j ∧
      ∀ v, compFin K L v z = (gf v : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j :=
    fun i j => exists_comp_eq K L _ _ (hE i j)
  have hD' : ∀ i j : Fin 2, ∃ z : L ⊗[K] AdeleRing (𝓞 K) K,
      compArch K L z = (ga⁻¹).val i j ∧ ∀ v, compFin K L v z = ((gf v)⁻¹).val i j :=
    fun i j => exists_comp_eq K L _ _ (hE' i j)
  choose D hDa hDf using hD
  choose D' hD'a hD'f using hD'
  let Dm : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := Matrix.of fun i j => D i j
  let D'm : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := Matrix.of fun i j => D' i j
  have hDma : (compArch K L).toRingHom.mapMatrix Dm =
      (ga : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
    ext i j; exact hDa i j
  have hDmf : ∀ v, (compFin K L v).toRingHom.mapMatrix Dm =
      (gf v : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
    intro v; ext i j; exact hDf i j v
  have hD'ma : (compArch K L).toRingHom.mapMatrix D'm = (ga⁻¹).val := by
    ext i j; exact hD'a i j
  have hD'mf : ∀ v, (compFin K L v).toRingHom.mapMatrix D'm = ((gf v)⁻¹).val := by
    intro v; ext i j; exact hD'f i j v
  have h1 : Dm * D'm = 1 := by
    apply matrix_eq_of_comp_eq K L
    · rw [map_mul, map_one, hDma, hD'ma, Units.mul_inv]
    · intro v; rw [map_mul, map_one, hDmf, hD'mf, Units.mul_inv]
  have h2 : D'm * Dm = 1 := by
    apply matrix_eq_of_comp_eq K L
    · rw [map_mul, map_one, hDma, hD'ma, Units.inv_mul]
    · intro v; rw [map_mul, map_one, hDmf, hD'mf, Units.inv_mul]
  refine ⟨⟨Dm, D'm, h1, h2⟩, ?_, fun v => ?_⟩
  · exact Units.ext hDma
  · exact Units.ext (hDmf v)

omit [FiniteDimensional K L] [NumberField L] in

theorem eventually_finComponent_mem_localIntegralSet (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) ∈ localIntegralSet K v := by
  have hent : ∀ i j : Fin 2, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K :=
    fun i j => ((γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2.2
  have hent' : ∀ i j : Fin 2, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (((γ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈
        v.adicCompletionIntegers K :=
    fun i j => (((γ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2.2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ i j : Fin 2,
      ((γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K ∧
      (((γ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈
        v.adicCompletionIntegers K := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (hent i j).and (hent' i j)
  filter_upwards [hall] with v hv
  refine mem_integralUnitsSet.2 ⟨fun i j => (hv i j).1, fun i j => ?_⟩
  rw [← map_inv, ← map_inv]
  exact (hv i j).2

omit [FiniteDimensional K L] [NumberField L] in

theorem eventually_valuation_discr_eq_one (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hγ : IsRegularSemisimple γ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (Matrix.trace (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
  obtain ⟨u, hu⟩ := hγ

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K),
      Matrix.trace (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = piFin K v (u : AdeleRing (𝓞 K) K) := by
    intro v
    rw [hu, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [map_sub, map_pow, map_add, map_mul, map_ofNat]
    rfl
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (u : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K := (u : AdeleRing (𝓞 K) K).2.2
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K :=
    ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2.2
  filter_upwards [h1, h2] with v hv1 hv2
  rw [hloc v, piFin_apply]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv1 hv2
  have hprod : (u : AdeleRing (𝓞 K) K).2 v * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
    have := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) u.mul_inv
    exact this
  refine le_antisymm hv1 ?_
  have hv : Valued.v ((u : AdeleRing (𝓞 K) K).2 v) *
      Valued.v (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) = 1 := by
    rw [← map_mul, hprod, map_one]
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((u : AdeleRing (𝓞 K) K).2 v) *
          Valued.v (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) := hv.symm
    _ ≤ Valued.v ((u : AdeleRing (𝓞 K) K).2 v) * 1 := by gcongr
    _ = Valued.v ((u : AdeleRing (𝓞 K) K).2 v) := mul_one _

omit [FiniteDimensional K L] in

theorem eventually_forall_ramificationIdx_eq_one :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1 := by
  letI : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hram : {w : HeightOneSpectrum (𝓞 L) |
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal ≠ 1}.Finite := by
    refine (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    by_contra hdvd
    apply hw
    have hun : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.mp hdvd
    haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := ⟨rfl⟩
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := (HeightOneSpectrum.under (𝓞 K) w).asIdeal)
      (q := w.asIdeal) (HeightOneSpectrum.under (𝓞 K) w).ne_bot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (p := w.asIdeal)
  rw [Filter.eventually_cofinite]
  refine (hram.image (HeightOneSpectrum.under (𝓞 K))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hwv, hw⟩ := hv
  exact ⟨w, hw, hwv⟩

end Adelic

end AutomorphicForm.AdelicNormGluing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.AutomorphicForm P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.AutomorphicForm.AdelicNormGluing"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.AutomorphicForm P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.AutomorphicForm.AdelicNormGluing"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.AutomorphicForm AutomorphicForm.AdelicNormGluing in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) δv)
    (harch : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K γ) δa) :
    ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ γ δ := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos

  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) ∈ localIntegralSet K v ∧
      Valued.v (Matrix.trace (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) :=
    ((eventually_finComponent_mem_localIntegralSet K γ).and
      ((eventually_valuation_discr_eq_one K γ hγ).and
        (eventually_forall_ramificationIdx_eq_one K L)))

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ (δv yv : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) =
          yv⁻¹ * normString K L (v.adicCompletion K) σ δv * yv ∧
        ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) ∈ localIntegralSet K v ∧
          Valued.v (Matrix.trace (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
            4 * Matrix.det (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 ∧
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)) →
          δv ∈ semiLocalIntegralSet K L v ∧ yv = 1) := by
    intro v
    by_cases hg :
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) ∈ localIntegralSet K v ∧
        Valued.v (Matrix.trace (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
          4 * Matrix.det (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 ∧
        (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
          Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1))
    · obtain ⟨δv, hδv, hN⟩ :=
        AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
          K L hdeg σ hσ v hg.2.2 _ hg.1 hg.2.1
      exact ⟨δv, 1, by rw [inv_one, one_mul, mul_one, hN], fun _ => ⟨hδv, rfl⟩⟩
    · obtain ⟨δv, yv, h⟩ := hfin v
      exact ⟨δv, yv, h, fun h' => absurd h' hg⟩
  choose δf yf hNf hint using hloc
  obtain ⟨δa, ya, hNa⟩ := harch
  obtain ⟨δ, hδa, hδf⟩ := gl_exists_comp_eq K L δa δf (hgood.mono fun v hv => (hint v hv).1)
  obtain ⟨y, hya, hyf⟩ := gl_exists_comp_eq K L ya yf (hgood.mono fun v hv => by
    rw [(hint v hv).2]; exact one_mem_semiLocalIntegralSet K L v)
  refine ⟨δ, y, ?_⟩
  show toTensorGL K L (AdeleRing (𝓞 K) K) γ = y⁻¹ * normString K L (AdeleRing (𝓞 K) K) σ δ * y
  apply gl_eq_of_comp_eq K L
  · rw [glmap_compArch_toTensorGL, map_mul, map_mul, map_inv, glmap_compArch_normString, hδa, hya]
    exact hNa
  · intro v
    rw [glmap_compFin_toTensorGL, map_mul, map_mul, map_inv, glmap_compFin_normString, hδf, hyf]
    exact hNf v

end S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime (solution)
