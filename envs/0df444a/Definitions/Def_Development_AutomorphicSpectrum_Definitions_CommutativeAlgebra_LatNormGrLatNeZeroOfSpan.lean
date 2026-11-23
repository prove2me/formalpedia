-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
-- name    : Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:24.992743+00:00
-- url     : https://prove2.me/theorems/c5e1479e-04ab-40cc-8d9d-dad60cf89920
-- title:
--   Lat Norm Gr Lat Ne Zero Of Span
-- statement:
--   Definitions and structural lemmas for Lat Norm Gr Lat Ne Zero Of Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_HTLat_mem_scaleLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
section Norms
variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
def latNorm (L : Submodule O V) (x : V) : NNReal :=
  sInf {r : NNReal | ∃ a : C, v a = r ∧ ∃ y ∈ L, x = a • y}
def latIn (L : Submodule O V) (U : Submodule C V) : Submodule O U :=
  L.comap (U.subtype.restrictScalars O)
def grLat {n : ℕ} (L : Submodule O V) (b : Basis (Fin n) C V) (i : Fin n) : Submodule O C :=
  (L ⊓ (b.flag i.succ).restrictScalars O).map ((b.coord i).restrictScalars O)
def grLog {n : ℕ} (L : Submodule O V) (b : Basis (Fin n) C V) (i : Fin n) : ℝ :=
  Real.log (latNorm v (grLat L b i) (1 : C))
def dualLat {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V'] [IsScalarTower O C V']
    (B : V →ₗ[C] V' →ₗ[C] C) (L : Submodule O V) : Submodule O V' where
  carrier := {y | ∀ x ∈ L, B x y ∈ (algebraMap O C).range}
  zero_mem' := fun x _ => by simpa using (algebraMap O C).range.zero_mem
  add_mem' := fun {a b} ha hb x hx => by
    simpa using (algebraMap O C).range.add_mem (ha x hx) (hb x hx)
  smul_mem' := fun c y hy x hx => by
    obtain ⟨t, ht⟩ := hy x hx
    refine ⟨c * t, ?_⟩
    rw [map_mul, ht, ← IsScalarTower.algebraMap_smul C c y, map_smul, smul_eq_mul]
end Norms
section Eigen
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
def eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) : Submodule K V :=
  ⨅ a : 𝓞 E, LinearMap.ker (ρ a - σ (a : E) • (1 : Module.End K V))
def eigSub (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) : Submodule A V :=
  X ⊓ (eigSp ρ σ).restrictScalars A
def dualInt (E : Type) [Field E] [NumberField E] (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) k
def eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) : Module.End K V :=
  ∑ k, σ (dualInt E k) • ρ (RingOfIntegers.basis E k)
def eigQuot (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) : Submodule A V :=
  X.map ((eigProj ρ σ).restrictScalars A)
def IsFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V) : Prop :=
  LinearIndependent K (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (t q.1)) ∧
    Submodule.span K (X : Set V) = ⊤ ∧
    X = Submodule.span A (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (t q.1))
def diffAbs (v : Valuation K NNReal) (σ : E →+* K) : NNReal :=
  ⨆ x : differentIdeal ℤ (𝓞 E), v (σ ((x : 𝓞 E) : E))
end Eigen
namespace LatBasic
section Norms
variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
theorem latNorm_eq (L : Submodule O V) (x : V) : latNorm v L x = GlobalTheory.HTLat.latNorm v L x := by
  unfold latNorm GlobalTheory.HTLat.latNorm
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, GlobalTheory.HTLat.mem_scaleLat]
  constructor
  · rintro ⟨a, h, y, hy, e⟩; exact ⟨a, ⟨y, hy, e.symm⟩, h⟩
  · rintro ⟨a, ⟨y, hy, e⟩, h⟩; exact ⟨a, h, y, hy, e.symm⟩
theorem latNorm_span (hv : v.Integers O) {g : V} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  rw [latNorm_eq, GlobalTheory.HTLat.latNorm_span_singleton hv hg]
theorem grLog_of_eq_span (hv : v.Integers O) {n : ℕ} {L : Submodule O V} {b : Basis (Fin n) C V}
    {i : Fin n} {c : C} (hc : c ≠ 0) (h : grLat L b i = Submodule.span O {c}) :
    grLog v L b i = -Real.log (v c) := by
  have h1 := latNorm_span v hv hc c⁻¹
  rw [smul_eq_mul, inv_mul_cancel₀ hc] at h1
  rw [grLog, h, h1, map_inv₀, NNReal.coe_inv, Real.log_inv]
theorem grLat_diag {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n) :
    grLat (Submodule.span O (Set.range fun j => c j • b j)) b i = Submodule.span O {c i} := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    change b.coord i x ∈ _
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨j, rfl⟩ := h
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨c i • b i, ⟨Submodule.subset_span ⟨i, rfl⟩, ?_⟩, by simp⟩
    exact Submodule.smul_mem (b.flag i.succ) _ (b.self_mem_flag Fin.castSucc_lt_succ)
example (hv : v.Integers O) {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n)
    (hc : c i ≠ 0) :
    grLog v (Submodule.span O (Set.range fun j => c j • b j)) b i = -Real.log (v (c i)) :=
  grLog_of_eq_span v hv hc (grLat_diag b c i)
example {c : C} (hc : c ≠ 0) :
    dualLat (LinearMap.mul C C) (Submodule.span O {c}) = Submodule.span O {c⁻¹} := by
  ext y
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h c (Submodule.mem_span_singleton_self c)
    refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
    rw [Algebra.smul_def, ho]; simp; field_simp
  · intro h x hx
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 h
    obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine ⟨o' * o, ?_⟩
    simp [Algebra.smul_def]; field_simp
end Norms
section Eigen
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl
theorem sum_dualInt_mul : ∑ k, dualInt E k * integralBasis E k = 1 := by
  classical
  rw [← sub_eq_zero]
  apply (traceForm_nondegenerate ℚ E).1
  intro y
  rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, mul_assoc, mul_comm _ y]
  generalize y * integralBasis E k = z
  conv_lhs => rw [← (integralBasis E).sum_repr z]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, trace_dualInt]
  simp
def regAct (K : Type) [Field K] (E : Type) [Field E] [NumberField E] :
    𝓞 E →+* Module.End K (K ⊗[ℤ] 𝓞 E) :=
  (Algebra.lmul K (K ⊗[ℤ] 𝓞 E)).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := K) (B := 𝓞 E)).toRingHom
theorem regAct_basis (k) :
    regAct K E (RingOfIntegers.basis E k) 1 =
      Algebra.TensorProduct.basis K (RingOfIntegers.basis E) k := by
  simp [regAct, Algebra.TensorProduct.basis_apply]
example (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  intro h
  let φ : K ⊗[ℤ] 𝓞 E →ₐ[K] K := Algebra.TensorProduct.lift (AlgHom.id K K)
    (σ.comp (algebraMap (𝓞 E) E)).toIntAlgHom (fun _ _ => Commute.all _ _)
  have h1 := congrArg φ h
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, regAct_basis,
    Algebra.TensorProduct.basis_apply, map_zero] at h1
  have h2 : ∑ k, σ (dualInt E k * integralBasis E k) = 0 := by
    simpa [φ] using h1
  rw [← map_sum, sum_dualInt_mul, map_one] at h2
  exact one_ne_zero h2
end Eigen
end LatBasic
end GlobalTheory.CompanionTheory.Ar.HT


