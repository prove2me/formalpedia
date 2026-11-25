-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:39.946346+00:00
-- url     : https://prove2.me/theorems/f303a259-bf8b-5583-b671-f8b2b5cb59a3
-- title:
--   Exists Smul Mem Of Mem Span Lattice
-- statement:
--   Definitions and structural lemmas for Exists Smul Mem Of Mem Span Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_eq_of_le_of_finrank_eq
import Theorems.Thm_GlobalTheory_abs_norm_eq_prod_complexEmbeddings
import Theorems.Thm_GlobalTheory_rank_eq_rank_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
namespace GlobalTheory
section Gram
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
def sesqGram (B : V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ) {ι : Type*} (e : ι → V) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => B (e i) (e j)
@[simp]
theorem sesqGram_apply (B : V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ) {ι : Type*}
    (e : ι → V) (i j : ι) : sesqGram B e i j = B (e i) (e j) := rfl
theorem sesqGram_of_eq_sum (B : V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ) {ι κ : Type*}
    [Fintype ι] {e : ι → V} {f : κ → V} {g : Matrix κ ι K} (hf : ∀ i, f i = ∑ j, g i j • e j) :
    sesqGram B f = g.map σ * sesqGram B e * (g.map σ)ᴴ := by
  ext i j
  simp only [sesqGram_apply, hf, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, ComplexEmbedding.conjugate_coe_eq, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [RCLike.star_def]
  ring
theorem sesqGram_posDef_of_basis (B : V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ)
    {ι κ : Type*} [Finite ι] [Finite κ] (b : Basis ι K V) (hb : (sesqGram B b).PosDef)
    {e : κ → V} (he : LinearIndependent K e) : (sesqGram B e).PosDef := by
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  let g : Matrix κ ι K := Matrix.of fun i j => b.repr (e i) j
  have hf : ∀ i, e i = ∑ j, g i j • b j := fun i => (b.sum_repr (e i)).symm
  rw [sesqGram_of_eq_sum B hf]
  refine hb.mul_mul_conjTranspose_same ?_
  rw [Matrix.vecMul_injective_iff]
  letI := σ.toAlgebra
  have h1 : LinearIndependent K (fun i => (g i : ι → K)) :=
    he.map' (b.equivFun : V →ₗ[K] (ι → K)) b.equivFun.ker
  exact (linearIndependent_algebraMap_comp_iff (R := K) (S := ℂ)).2 h1
end Gram
@[ext]
structure ArchMetric (K : Type*) (V : Type*) [Field K] [AddCommGroup V] [Module K V] where

  form : ∀ σ : K →+* ℂ, V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ

  form_symm : ∀ (σ : K →+* ℂ) (x y : V), form σ y x = conj (form σ x y)

  posDef : ∀ (σ : K →+* ℂ) {n : ℕ} (e : Fin n → V), LinearIndependent K e →
    (sesqGram (form σ) e).PosDef
namespace ArchMetric
section Field
variable {K : Type*} [Field K] {V V' V'' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
def ofBasis {ι : Type*} [Finite ι] (b : Basis ι K V)
    (B : ∀ σ : K →+* ℂ, V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ)
    (symm : ∀ σ x y, B σ y x = conj (B σ x y)) (pos : ∀ σ, (sesqGram (B σ) b).PosDef) :
    ArchMetric K V where
  form := B
  form_symm := symm
  posDef σ _ _ he := sesqGram_posDef_of_basis (B σ) b (pos σ) he
@[simp]
theorem ofBasis_form {ι : Type*} [Finite ι] (b : Basis ι K V)
    (B : ∀ σ : K →+* ℂ, V →ₛₗ[σ] V →ₛₗ[ComplexEmbedding.conjugate σ] ℂ)
    (symm : ∀ σ x y, B σ y x = conj (B σ x y)) (pos : ∀ σ, (sesqGram (B σ) b).PosDef) :
    (ofBasis b B symm pos).form = B := rfl
def ofFun {ι : Type*} [Finite ι] (b : Basis ι K V) (H : (K →+* ℂ) → V → V → ℂ)
    (add : ∀ σ x x' y, H σ (x + x') y = H σ x y + H σ x' y)
    (smul : ∀ σ (a : K) x y, H σ (a • x) y = σ a * H σ x y)
    (symm : ∀ σ x y, H σ y x = conj (H σ x y))
    (pos : ∀ σ, (Matrix.of fun i j => H σ (b i) (b j)).PosDef) : ArchMetric K V :=
  ofBasis b
    (fun σ => LinearMap.mk₂'ₛₗ σ (ComplexEmbedding.conjugate σ) (H σ) (add σ) (smul σ)
      (fun x y y' => by rw [symm σ (y + y') x, add, map_add, ← symm, ← symm])
      (fun a x y => by
        rw [symm σ (a • y) x, smul, map_mul, ← symm, ComplexEmbedding.conjugate_coe_eq,
          smul_eq_mul]))
    symm pos
@[simp]
theorem ofFun_form {ι : Type*} [Finite ι] (b : Basis ι K V) (H : (K →+* ℂ) → V → V → ℂ)
    (add : ∀ σ x x' y, H σ (x + x') y = H σ x y + H σ x' y)
    (smul : ∀ σ (a : K) x y, H σ (a • x) y = σ a * H σ x y)
    (symm : ∀ σ x y, H σ y x = conj (H σ x y))
    (pos : ∀ σ, (Matrix.of fun i j => H σ (b i) (b j)).PosDef) (σ : K →+* ℂ) (x y : V) :
    (ofFun b H add smul symm pos).form σ x y = H σ x y := rfl
noncomputable def ofGram {ι : Type*} [Fintype ι] (b : Basis ι K V)
    (G : (K →+* ℂ) → Matrix ι ι ℂ) (hG : ∀ σ, (G σ).PosDef) : ArchMetric K V :=
  ofFun b (fun σ x y => ∑ i, ∑ j, σ (b.repr x i) * G σ i j * conj (σ (b.repr y j)))
    (fun σ x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun σ a x y => by simp [Finset.mul_sum, mul_assoc])
    (fun σ x y => by
      rw [Finset.sum_comm]
      simp only [map_sum, map_mul, Complex.conj_conj]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have := (hG σ).isHermitian.apply j i
      rw [RCLike.star_def] at this
      rw [this]
      ring)
    (fun σ => by
      classical
      convert hG σ using 1
      ext i j
      simp [Finsupp.single_apply, apply_ite σ, apply_ite (starRingEnd ℂ)])
theorem ofGram_form {ι : Type*} [Fintype ι] (b : Basis ι K V)
    (G : (K →+* ℂ) → Matrix ι ι ℂ) (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) (x y : V) :
    (ofGram b G hG).form σ x y = ∑ i, ∑ j, σ (b.repr x i) * G σ i j * conj (σ (b.repr y j)) :=
  rfl
noncomputable def diag {ι : Type*} [Fintype ι] (d : (K →+* ℂ) → ι → ℝ) (hd : ∀ σ i, 0 < d σ i) :
    ArchMetric K (ι → K) :=
  ofFun (Pi.basisFun K ι) (fun σ x y => ∑ i, (d σ i : ℂ) * (σ (x i) * conj (σ (y i))))
    (fun σ x x' y => by simp [add_mul, mul_add, Finset.sum_add_distrib])
    (fun σ a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun σ x y => by
      simp only [map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun σ => by
      classical
      have : (Matrix.diagonal fun i => (d σ i : ℂ)).PosDef :=
        Matrix.PosDef.diagonal fun i => by exact_mod_cast hd σ i
      convert this using 1
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Pi.single_apply, apply_ite σ, apply_ite (starRingEnd ℂ)]
      · simp [Pi.single_apply, apply_ite σ, apply_ite (starRingEnd ℂ), hij, Ne.symm hij])
theorem diag_form {ι : Type*} [Fintype ι] (d : (K →+* ℂ) → ι → ℝ) (hd : ∀ σ i, 0 < d σ i)
    (σ : K →+* ℂ) (x y : ι → K) :
    (diag d hd).form σ x y = ∑ i, (d σ i : ℂ) * (σ (x i) * conj (σ (y i))) := rfl
variable (K) in

noncomputable def std (ι : Type*) [Fintype ι] : ArchMetric K (ι → K) :=
  diag (fun _ _ => 1) fun _ _ => one_pos
theorem std_form {ι : Type*} [Fintype ι] (σ : K →+* ℂ) (x y : ι → K) :
    (std K ι).form σ x y = ∑ i, σ (x i) * conj (σ (y i)) := by
  simp [std, diag_form]
variable (K) in

noncomputable def stdField : ArchMetric K K :=
  ofFun (Basis.singleton Unit K) (fun σ x y => σ x * conj (σ y))
    (fun σ x x' y => by simp [add_mul]) (fun σ a x y => by simp [mul_assoc])
    (fun σ x y => by simp [mul_comm])
    (fun σ => by
      convert (Matrix.PosDef.one : (1 : Matrix Unit Unit ℂ).PosDef) using 1
      ext i j
      simp)
@[simp]
theorem stdField_form (σ : K →+* ℂ) (x y : K) : (stdField K).form σ x y = σ x * conj (σ y) := rfl
instance [FiniteDimensional K V] : Nonempty (ArchMetric K V) :=
  ⟨ofGram (Module.finBasis K V) (fun _ => 1) fun _ => Matrix.PosDef.one⟩
variable (h : ArchMetric K V)
@[simp]
theorem conj_form (σ : K →+* ℂ) (x y : V) : conj (h.form σ x y) = h.form σ y x :=
  (h.form_symm σ x y).symm
def ConjInvariant : Prop :=
  ∀ (σ : K →+* ℂ) (x y : V), h.form (ComplexEmbedding.conjugate σ) x y = conj (h.form σ x y)
def gram (σ : K →+* ℂ) {ι : Type*} (e : ι → V) : Matrix ι ι ℂ := sesqGram (h.form σ) e
@[simp]
theorem gram_apply (σ : K →+* ℂ) {ι : Type*} (e : ι → V) (i j : ι) :
    h.gram σ e i j = h.form σ (e i) (e j) := rfl
theorem gram_comp (σ : K →+* ℂ) {ι κ : Type*} (e : ι → V) (p : κ → ι) :
    h.gram σ (e ∘ p) = (h.gram σ e).submatrix p p := rfl
theorem gram_of_eq_sum (σ : K →+* ℂ) {ι κ : Type*} [Fintype ι] {e : ι → V} {f : κ → V}
    {g : Matrix κ ι K} (hf : ∀ i, f i = ∑ j, g i j • e j) :
    h.gram σ f = g.map σ * h.gram σ e * (g.map σ)ᴴ :=
  sesqGram_of_eq_sum _ hf
theorem posDef_gram (σ : K →+* ℂ) {ι : Type*} [Finite ι] {e : ι → V}
    (he : LinearIndependent K e) : (h.gram σ e).PosDef := by
  obtain ⟨n, ⟨p⟩⟩ := Finite.exists_equiv_fin ι
  have := (h.posDef σ (e ∘ p.symm) (he.comp _ p.symm.injective)).submatrix p.injective
  convert this using 1
  ext i j
  simp
theorem posSemidef_gram (σ : K →+* ℂ) {ι : Type*} [Finite ι] (e : ι → V) :
    (h.gram σ e).PosSemidef := by
  haveI : FiniteDimensional K (Submodule.span K (Set.range e)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range e)
  let W := Submodule.span K (Set.range e)
  let b := Module.finBasis K W
  have hb : LinearIndependent K (fun i => (b i : V)) :=
    b.linearIndependent.map' W.subtype W.ker_subtype
  let g : Matrix ι (Fin (finrank K W)) K :=
    Matrix.of fun i j => b.repr ⟨e i, Submodule.subset_span ⟨i, rfl⟩⟩ j
  have hf : ∀ i, e i = ∑ j, g i j • (b j : V) := fun i => by
    have := congrArg W.subtype (b.sum_repr ⟨e i, Submodule.subset_span ⟨i, rfl⟩⟩).symm
    rw [map_sum] at this
    exact this
  rw [h.gram_of_eq_sum σ hf]
  exact (h.posDef_gram σ hb).posSemidef.mul_mul_conjTranspose_same _
@[simp]
theorem gram_ofGram {ι : Type*} [Fintype ι] (b : Basis ι K V)
    (G : (K →+* ℂ) → Matrix ι ι ℂ) (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) :
    (ofGram b G hG).gram σ b = G σ := by
  classical
  ext i j
  simp [ofGram_form, Finsupp.single_apply, apply_ite σ, apply_ite (starRingEnd ℂ)]
theorem gram_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : (K →+* ℂ) → ι → ℝ)
    (hd : ∀ σ i, 0 < d σ i) (σ : K →+* ℂ) :
    (diag d hd).gram σ (Pi.basisFun K ι) = Matrix.diagonal fun i => (d σ i : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diag_form, Pi.single_apply, apply_ite σ, apply_ite (starRingEnd ℂ)]
  · simp [diag_form, Pi.single_apply, apply_ite σ, apply_ite (starRingEnd ℂ), hij, Ne.symm hij]
section GramDet
variable (σ : K →+* ℂ) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
noncomputable def gramDet (e : ι → V) : ℝ := (h.gram σ e).det.re
theorem ofReal_gramDet (e : ι → V) : (h.gramDet σ e : ℂ) = (h.gram σ e).det := by
  have := (h.posSemidef_gram σ e).det_nonneg
  exact Complex.ext (by simp [gramDet]) (by simpa using (Complex.nonneg_iff.1 this).2)
theorem gramDet_pos {e : ι → V} (he : LinearIndependent K e) : 0 < h.gramDet σ e :=
  (Complex.pos_iff.1 (h.posDef_gram σ he).det_pos).1
theorem gramDet_comp_equiv (e : ι → V) (p : κ ≃ ι) : h.gramDet σ (e ∘ p) = h.gramDet σ e := by
  rw [gramDet, gram_comp, Matrix.det_submatrix_equiv_self, gramDet]
theorem gramDet_of_eq_sum {e f : ι → V} {g : Matrix ι ι K} (hf : ∀ i, f i = ∑ j, g i j • e j) :
    h.gramDet σ f = ‖σ g.det‖ ^ 2 * h.gramDet σ e := by
  apply Complex.ofReal_injective
  have h1 : (g.map σ).det = σ g.det := (σ.map_det g).symm
  rw [Complex.ofReal_mul, ofReal_gramDet, ofReal_gramDet, h.gram_of_eq_sum σ hf, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_conjTranspose, h1, ← Complex.normSq_eq_norm_sq,
    ← Complex.mul_conj, RCLike.star_def]
  ring
@[simp]
theorem gramDet_of_isEmpty [IsEmpty ι] (e : ι → V) : h.gramDet σ e = 1 := by
  simp [gramDet]
theorem gramDet_diag (d : (K →+* ℂ) → ι → ℝ) (hd : ∀ σ i, 0 < d σ i) :
    (diag d hd).gramDet σ (Pi.basisFun K ι) = ∏ i, d σ i := by
  rw [gramDet, gram_diag, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
end GramDet
theorem form_self_nonneg (σ : K →+* ℂ) (x : V) : 0 ≤ h.form σ x x := by
  simpa using (h.posSemidef_gram σ fun _ : Unit => x).det_nonneg
noncomputable def norm (σ : K →+* ℂ) (x : V) : ℝ := Real.sqrt (h.form σ x x).re
theorem norm_nonneg (σ : K →+* ℂ) (x : V) : 0 ≤ h.norm σ x := Real.sqrt_nonneg _
theorem norm_sq (σ : K →+* ℂ) (x : V) : h.norm σ x ^ 2 = (h.form σ x x).re :=
  Real.sq_sqrt (Complex.nonneg_iff.1 (h.form_self_nonneg σ x)).1
theorem gramDet_unique (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]
    (e : ι → V) : h.gramDet σ e = h.norm σ (e default) ^ 2 := by
  rw [gramDet, norm_sq, Matrix.det_unique, gram_apply]
@[simp]
theorem norm_zero (σ : K →+* ℂ) : h.norm σ 0 = 0 := by simp [norm]
theorem norm_pos (σ : K →+* ℂ) {x : V} (hx : x ≠ 0) : 0 < h.norm σ x := by
  have h1 := h.gramDet_pos σ (e := fun _ : Unit => x) (linearIndependent_unique_iff.2 hx)
  rw [gramDet_unique] at h1
  exact lt_of_le_of_ne (h.norm_nonneg σ x) fun h0 => by simp [← h0] at h1
@[simp]
theorem norm_eq_zero {σ : K →+* ℂ} {x : V} : h.norm σ x = 0 ↔ x = 0 :=
  ⟨fun h0 => by_contra fun hx => (h.norm_pos σ hx).ne' h0, fun h0 => by simp [h0]⟩
@[simp]
theorem stdField_norm (σ : K →+* ℂ) (x : K) : (stdField K).norm σ x = ‖σ x‖ := by
  rw [norm, stdField_form, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (_root_.norm_nonneg _)]
@[simp]
theorem norm_neg (σ : K →+* ℂ) (x : V) : h.norm σ (-x) = h.norm σ x := by simp [norm]
def comap (f : V' →ₗ[K] V) (hf : Function.Injective f) : ArchMetric K V' where
  form σ := LinearMap.mk₂'ₛₗ σ (ComplexEmbedding.conjugate σ) (fun x y => h.form σ (f x) (f y))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp [LinearMap.map_smulₛₗ])
    (fun _ _ _ => by simp) (fun _ _ _ => by simp [LinearMap.map_smulₛₗ])
  form_symm σ x y := h.form_symm σ (f x) (f y)
  posDef σ _ e he := h.posDef σ (f ∘ e) (he.map' f (LinearMap.ker_eq_bot.2 hf))
section Comap
variable (f : V' →ₗ[K] V) (hf : Function.Injective f) (σ : K →+* ℂ)
@[simp]
theorem comap_form (x y : V') : (h.comap f hf).form σ x y = h.form σ (f x) (f y) := rfl
@[simp]
theorem comap_norm (x : V') : (h.comap f hf).norm σ x = h.norm σ (f x) := rfl
@[simp]
theorem comap_id : h.comap LinearMap.id Function.injective_id = h := rfl
variable {h} in

theorem ConjInvariant.comap (hc : h.ConjInvariant) : (h.comap f hf).ConjInvariant :=
  fun σ x y => hc σ (f x) (f y)
end Comap
def restrict (W : Submodule K V) : ArchMetric K W := h.comap W.subtype W.injective_subtype
@[simp]
theorem restrict_form (W : Submodule K V) (σ : K →+* ℂ) (x y : W) :
    (h.restrict W).form σ x y = h.form σ x y := rfl
@[simp]
theorem restrict_norm (W : Submodule K V) (σ : K →+* ℂ) (x : W) :
    (h.restrict W).norm σ x = h.norm σ x := rfl
variable {h} in

theorem ConjInvariant.restrict (hc : h.ConjInvariant) (W : Submodule K V) :
    (h.restrict W).ConjInvariant := hc.comap _ _
noncomputable def scale (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) : ArchMetric K V where
  form σ := (c σ : ℂ) • h.form σ
  form_symm σ x y := by simp
  posDef σ _ e he := (h.posDef σ e he).smul (a := (c σ : ℂ)) (by exact_mod_cast hc σ)
section Scale
variable (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (σ : K →+* ℂ)
@[simp]
theorem scale_form (x y : V) : (h.scale c hc).form σ x y = c σ * h.form σ x y := rfl
variable {h c} in

theorem ConjInvariant.scale (hh : h.ConjInvariant)
    (hcc : ∀ σ, c (ComplexEmbedding.conjugate σ) = c σ) : (h.scale c hc).ConjInvariant :=
  fun σ x y => by simp [hcc, hh σ]
end Scale
noncomputable def scaleNormExp (t : (K →+* ℂ) → ℝ) : ArchMetric K V :=
  h.scale (fun σ => Real.exp (2 * t σ)) fun _ => Real.exp_pos _
end Field
end ArchMetric
section Index
theorem relIndex_toAddSubgroup_eq_card {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (B A : Submodule R M) :
    B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A ⧸ B.submoduleOf A) := rfl
theorem index_range_eq_natAbs_norm_det {S M : Type*} [CommRing S] [Module.Free ℤ S]
    [Module.Finite ℤ S] [AddCommGroup M] [Module S M] [Module.Free S M] [Module.Finite S M]
    (φ : M →ₗ[S] M) (hφ : Function.Injective φ) :
    (LinearMap.range φ).toAddSubgroup.index = (Algebra.norm ℤ (LinearMap.det φ)).natAbs := by
  haveI : Module.Free ℤ M := Module.Free.trans (S := S)
  haveI : Module.Finite ℤ M := Module.Finite.trans S M
  rw [← LinearMap.det_restrictScalars]
  have := Submodule.natAbs_det_equiv (LinearMap.range (φ.restrictScalars ℤ))
    (LinearEquiv.ofInjective (φ.restrictScalars ℤ) hφ)
  exact this.symm
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
theorem finrank_lattice_eq_finrank_span (A : Submodule (𝓞 K) V) :
    finrank (𝓞 K) A = finrank K (Submodule.span K (A : Set V)) := by
  rw [Module.finrank, Module.finrank, rank_eq_rank_span K]
omit [NumberField K] in

theorem finiteDimensional_span_of_fg {A : Submodule (𝓞 K) V} (hA : A.FG) :
    FiniteDimensional K (Submodule.span K (A : Set V)) := by
  obtain ⟨s, rfl⟩ := hA
  rw [Submodule.span_span_of_tower]
  exact FiniteDimensional.span_finset K s
theorem finrank_lattice_pos {A : Submodule (𝓞 K) V} (hA : A.FG) (h0 : A ≠ ⊥) :
    0 < finrank (𝓞 K) A := by
  haveI := finiteDimensional_span_of_fg hA
  rw [finrank_lattice_eq_finrank_span]
  refine Nat.pos_of_ne_zero fun h => h0 ?_
  rw [Submodule.finrank_eq_zero, Submodule.span_eq_bot] at h
  exact (Submodule.eq_bot_iff _).2 h
theorem mem_span_of_le_of_finrank_eq {A B : Submodule (𝓞 K) V} (hA : A.FG) (hBA : B ≤ A)
    (hr : finrank (𝓞 K) B = finrank (𝓞 K) A) : ∀ x ∈ A, x ∈ Submodule.span K (B : Set V) := by
  haveI := finiteDimensional_span_of_fg hA
  rw [finrank_lattice_eq_finrank_span, finrank_lattice_eq_finrank_span] at hr
  rw [Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hBA) hr]
  exact fun x hx => Submodule.subset_span hx
theorem exists_smul_mem_of_mem_span_lattice {B : Submodule (𝓞 K) V} {x : V}
    (hx : x ∈ Submodule.span K (B : Set V)) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ B := by
  rw [← mem_saturation_iff, saturation_eq_span K]
  exact hx
theorem relIndex_ne_zero_of_le_span {A B : Submodule (𝓞 K) V} (hA : A.FG)
    (hAB : ∀ x ∈ A, x ∈ Submodule.span K (B : Set V)) :
    B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 := by
  rw [relIndex_toAddSubgroup_eq_card]
  haveI : Module.Finite (𝓞 K) A := Module.Finite.iff_fg.2 hA
  haveI : Module.Finite ℤ (A ⧸ B.submoduleOf A) := Module.Finite.trans (𝓞 K) _
  haveI : Finite (A ⧸ B.submoduleOf A) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, hax⟩ := exists_smul_mem_of_mem_span_lattice (hAB x x.2)
    have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨⟨(Ideal.absNorm (Ideal.span {a}) : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul]
    exact Submodule.smul_mem _ c hax
  exact Nat.card_pos.ne'
theorem relIndex_span_eq_natAbs_norm_det {ι : Type*} [Fintype ι] [DecidableEq ι] {e f : ι → V}
    (he : LinearIndependent K e) {g : Matrix ι ι (𝓞 K)} (hg : g.det ≠ 0)
    (hf : ∀ i, f i = ∑ j, g i j • e j) :
    (Submodule.span (𝓞 K) (Set.range f)).toAddSubgroup.relIndex
        (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup = (Algebra.norm ℤ g.det).natAbs := by
  let L : (ι → 𝓞 K) →ₗ[𝓞 K] V := Fintype.linearCombination (𝓞 K) e
  have hL : Function.Injective L :=
    (he.restrict_scalars' (𝓞 K)).fintypeLinearCombination_injective
  let φ : (ι → 𝓞 K) →ₗ[𝓞 K] (ι → 𝓞 K) := Matrix.toLin' gᵀ
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hv
  have h1 : Submodule.span (𝓞 K) (Set.range e) = (⊤ : Submodule (𝓞 K) (ι → 𝓞 K)).map L := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have h2 : Submodule.span (𝓞 K) (Set.range f) = (LinearMap.range φ).map L := by
    rw [← LinearMap.range_comp, ← Fintype.range_linearCombination]
    congr 1
    ext i
    simp [L, φ, Fintype.linearCombination_apply, hf, Pi.single_apply]
  rw [h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hL, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, index_range_eq_natAbs_norm_det φ hφ, LinearMap.det_toLin',
    Matrix.det_transpose]
theorem log_natAbs_norm_eq_sum {a : 𝓞 K} (ha : a ≠ 0) :
    Real.log ((Algebra.norm ℤ a).natAbs : ℝ) = ∑ σ : K →+* ℂ, Real.log ‖σ (a : K)‖ := by
  have ha' : (a : K) ≠ 0 := by simpa using ha
  rw [← Real.log_prod fun σ _ => by simpa using ha', ← abs_norm_eq_prod_complexEmbeddings,
    ← Algebra.coe_norm_int, Nat.cast_natAbs]
  simp
structure IsLatticeFrame {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (A : Submodule (𝓞 K) V) {ι : Type*} (e : ι → V) : Prop where

  mem : ∀ i, e i ∈ A

  linearIndependent : LinearIndependent K e

  mem_span : ∀ x ∈ A, x ∈ Submodule.span K (Set.range e)
namespace IsLatticeFrame
variable {A : Submodule (𝓞 K) V} {ι κ : Type*} {e : ι → V}
omit [NumberField K] [IsScalarTower (𝓞 K) K V] in

theorem span_eq (he : IsLatticeFrame A e) :
    Submodule.span K (Set.range e) = Submodule.span K (A : Set V) :=
  le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 he.mem))
    (Submodule.span_le.2 he.mem_span)
omit [NumberField K] [IsScalarTower (𝓞 K) K V] in

theorem span_le (he : IsLatticeFrame A e) : Submodule.span (𝓞 K) (Set.range e) ≤ A :=
  Submodule.span_le.2 (Set.range_subset_iff.2 he.mem)
theorem card_eq [Fintype ι] (he : IsLatticeFrame A e) : Fintype.card ι = finrank (𝓞 K) A := by
  rw [finrank_lattice_eq_finrank_span, ← he.span_eq, finrank_span_eq_card he.linearIndependent]
omit [NumberField K] [IsScalarTower (𝓞 K) K V] in

theorem comp_equiv (he : IsLatticeFrame A e) (p : κ ≃ ι) : IsLatticeFrame A (e ∘ p) :=
  ⟨fun i => he.mem _, he.linearIndependent.comp _ p.injective, by
    rw [p.surjective.range_comp]
    exact he.mem_span⟩
theorem relIndex_ne_zero (he : IsLatticeFrame A e) (hA : A.FG) :
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 :=
  relIndex_ne_zero_of_le_span hA fun x hx => by
    rw [Submodule.span_span_of_tower]
    exact he.mem_span x hx
omit [NumberField K] [IsScalarTower (𝓞 K) K V] in

theorem of_le {B : Submodule (𝓞 K) V} (he : IsLatticeFrame A e) (hAB : A ≤ B)
    (hB : ∀ x ∈ B, x ∈ Submodule.span K (A : Set V)) : IsLatticeFrame B e :=
  ⟨fun i => hAB (he.mem i), he.linearIndependent, fun x hx => he.span_eq ▸ hB x hx⟩
omit [NumberField K] in

theorem map (he : IsLatticeFrame A e) (f : V →ₗ[K] V') (hf : Function.Injective f) :
    IsLatticeFrame (A.map (f.restrictScalars (𝓞 K))) (f ∘ e) where
  mem i := ⟨e i, he.mem i, rfl⟩
  linearIndependent := he.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
  mem_span := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.range_comp, ← Submodule.map_span]
    exact ⟨x, he.mem_span x hx, rfl⟩
omit [NumberField K] in

theorem smul (he : IsLatticeFrame A e) {d : ι → 𝓞 K} (hd : ∀ i, d i ≠ 0) :
    IsLatticeFrame A fun i => d i • e i := by
  have hd' : ∀ i, (d i : K) ≠ 0 := fun i => by simpa using hd i
  have hs : ∀ i, d i • e i = (d i : K) • e i := fun i => (algebraMap_smul K (d i) (e i)).symm
  refine ⟨fun i => A.smul_mem _ (he.mem i), ?_, fun x hx => ?_⟩
  · simp only [hs]
    exact he.linearIndependent.units_smul fun i => Units.mk0 _ (hd' i)
  · refine Submodule.span_le.2 ?_ (he.mem_span x hx)
    rintro _ ⟨i, rfl⟩
    have : e i = (d i : K)⁻¹ • d i • e i := by rw [hs, inv_smul_smul₀ (hd' i)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end IsLatticeFrame
omit [NumberField K] in

theorem isLatticeFrame_span {ι : Type*} {e : ι → V} (he : LinearIndependent K e) :
    IsLatticeFrame (Submodule.span (𝓞 K) (Set.range e)) e :=
  ⟨fun i => Submodule.subset_span ⟨i, rfl⟩, he,
    fun _ hx => Submodule.span_le_restrictScalars (𝓞 K) K _ hx⟩
theorem exists_isLatticeFrame {A : Submodule (𝓞 K) V} (hA : A.FG) :
    ∃ e : Fin (finrank (𝓞 K) A) → V, IsLatticeFrame A e := by
  haveI := finiteDimensional_span_of_fg hA
  rw [finrank_lattice_eq_finrank_span]
  obtain ⟨e, h1, h2, h3⟩ := Submodule.exists_fun_fin_finrank_span_eq K (A : Set V)
  exact ⟨e, h1, h3, fun x hx => h2.ge (Submodule.subset_span hx)⟩
end Index
namespace ArchMetric
section NumberField
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
noncomputable def frameDeg (A : Submodule (𝓞 K) V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → V) : ℝ :=
  Real.log (Nat.card (A ⧸ (Submodule.span (𝓞 K) (Set.range e)).submoduleOf A)) -
    ∑ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ e)
section FrameDeg
variable {A : Submodule (𝓞 K) V} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]
omit [IsScalarTower (𝓞 K) K V] in

theorem frameDeg_eq_relIndex (A : Submodule (𝓞 K) V) (e : ι → V) :
    h.frameDeg A e =
      Real.log ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex A.toAddSubgroup) -
        ∑ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ e) := rfl
omit [IsScalarTower (𝓞 K) K V] in

theorem frameDeg_comp_equiv (A : Submodule (𝓞 K) V) (e : ι → V) (p : κ ≃ ι) :
    h.frameDeg A (e ∘ p) = h.frameDeg A e := by
  simp only [frameDeg_eq_relIndex, gramDet_comp_equiv, p.surjective.range_comp]
theorem frameDeg_eq_of_mem_span (hA : A.FG) {e f : ι → V} (he : IsLatticeFrame A e)
    (hf : IsLatticeFrame A f) (hfe : ∀ i, f i ∈ Submodule.span (𝓞 K) (Set.range e)) :
    h.frameDeg A f = h.frameDeg A e := by
  choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hfe i)
  let G : Matrix ι ι (𝓞 K) := Matrix.of g
  have hG : ∀ i, f i = ∑ j, G i j • e j := fun i => (hg i).symm
  have hG' : ∀ i, f i = ∑ j, G.map (algebraMap (𝓞 K) K) i j • e j := fun i => by
    simp only [hG i, Matrix.map_apply, algebraMap_smul]
  have hdet : (G.map (algebraMap (𝓞 K) K)).det = (G.det : K) :=
    ((algebraMap (𝓞 K) K).map_det G).symm
  have hgram : ∀ σ, h.gramDet σ f = ‖σ (G.det : K)‖ ^ 2 * h.gramDet σ e := fun σ => by
    rw [h.gramDet_of_eq_sum σ hG', hdet]
  have h0 : G.det ≠ 0 := fun h0 => by
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := h.gramDet_pos σ hf.linearIndependent
    simp [hgram, h0] at this
  have h0' : (G.det : K) ≠ 0 := by simpa using h0
  have hle : Submodule.span (𝓞 K) (Set.range f) ≤ Submodule.span (𝓞 K) (Set.range e) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hfe)
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (Submodule.span (𝓞 K) (Set.range f)).toAddSubgroup
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup A.toAddSubgroup hle he.span_le
  rw [relIndex_span_eq_natAbs_norm_det he.linearIndependent h0 hG] at hmul
  have hne := hf.relIndex_ne_zero hA
  rw [← hmul] at hne
  have hlog : ∀ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ f) =
      Real.log ‖σ (G.det : K)‖ + 1 / 2 * Real.log (h.gramDet σ e) := fun σ => by
    rw [hgram, Real.log_mul (pow_ne_zero _ (by simpa using h0'))
      (h.gramDet_pos σ he.linearIndependent).ne', Real.log_pow]
    push_cast
    ring
  rw [frameDeg_eq_relIndex, frameDeg_eq_relIndex, ← hmul, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul hne))
      (Nat.cast_ne_zero.2 (right_ne_zero_of_mul hne)), log_natAbs_norm_eq_sum h0]
  simp only [hlog, Finset.sum_add_distrib]
  ring
theorem frameDeg_eq_frameDeg (hA : A.FG) {e : ι → V} {f : κ → V} (he : IsLatticeFrame A e)
    (hf : IsLatticeFrame A f) : h.frameDeg A e = h.frameDeg A f := by
  let p : ι ≃ κ := Fintype.equivOfCardEq (he.card_eq.trans hf.card_eq.symm)
  have hf' := hf.comp_equiv p
  rw [← h.frameDeg_comp_equiv A f p]
  have : ∀ i, ∃ a : 𝓞 K, a ≠ 0 ∧ a • (f ∘ p) i ∈ Submodule.span (𝓞 K) (Set.range e) := fun i =>
    exists_smul_mem_of_mem_span_lattice (by
      rw [Submodule.span_span_of_tower]
      exact he.mem_span _ (hf'.mem i))
  choose d hd hde using this
  rw [← h.frameDeg_eq_of_mem_span hA he (hf'.smul hd) hde,
    h.frameDeg_eq_of_mem_span hA hf' (hf'.smul hd) fun i =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)]
end FrameDeg
open Classical in

noncomputable def arDeg (A : Submodule (𝓞 K) V) : ℝ :=
  if hA : A.FG then h.frameDeg A (exists_isLatticeFrame hA).choose else 0
section ArDeg
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem arDeg_eq_frameDeg (hA : A.FG) {e : ι → V} (he : IsLatticeFrame A e) :
    h.arDeg A = h.frameDeg A e := by
  rw [arDeg, dif_pos hA]
  exact h.frameDeg_eq_frameDeg hA (exists_isLatticeFrame hA).choose_spec he
theorem arDeg_span {e : ι → V} (he : LinearIndependent K e) :
    h.arDeg (Submodule.span (𝓞 K) (Set.range e)) =
      -∑ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ e) := by
  rw [h.arDeg_eq_frameDeg (Submodule.fg_span (Set.finite_range e)) (isLatticeFrame_span he),
    frameDeg_eq_relIndex]
  simp
@[simp]
theorem arDeg_bot : h.arDeg ⊥ = 0 := by
  have := h.arDeg_span (e := fun i : Empty => i.elim) linearIndependent_empty_type
  simpa [Set.range_eq_empty] using this
theorem arDeg_span_singleton {x : V} (hx : x ≠ 0) :
    h.arDeg (Submodule.span (𝓞 K) {x}) = -∑ σ : K →+* ℂ, Real.log (h.norm σ x) := by
  have := h.arDeg_span (e := fun _ : Unit => x) (linearIndependent_unique_iff.2 hx)
  rw [Set.range_const] at this
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [gramDet_unique, Real.log_pow]
  push_cast
  ring
theorem arDeg_eq_add_log_relIndex {B : Submodule (𝓞 K) V} (hA : A.FG) (hBA : B ≤ A)
    (hAB : ∀ x ∈ A, x ∈ Submodule.span K (B : Set V)) :
    h.arDeg A = h.arDeg B + Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup) := by
  have hB := hA.of_le hBA
  obtain ⟨e, he⟩ := exists_isLatticeFrame hB
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup B.toAddSubgroup A.toAddSubgroup
    he.span_le hBA
  rw [arDeg_eq_frameDeg _ hA (he.of_le hBA hAB), arDeg_eq_frameDeg _ hB he, frameDeg_eq_relIndex,
    frameDeg_eq_relIndex, ← hmul, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (he.relIndex_ne_zero hB))
      (Nat.cast_ne_zero.2 (relIndex_ne_zero_of_le_span hA hAB))]
  ring
theorem arDeg_le_of_finrank_eq {B : Submodule (𝓞 K) V} (hA : A.FG) (hBA : B ≤ A)
    (hr : finrank (𝓞 K) B = finrank (𝓞 K) A) : h.arDeg B ≤ h.arDeg A := by
  rw [h.arDeg_eq_add_log_relIndex hA hBA (mem_span_of_le_of_finrank_eq hA hBA hr)]
  exact le_add_of_nonneg_right (Real.log_natCast_nonneg _)
theorem arDeg_diag (d : (K →+* ℂ) → ι → ℝ) (hd : ∀ σ i, 0 < d σ i) :
    (diag d hd).arDeg (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K ι))) =
      -∑ σ : K →+* ℂ, 1 / 2 * ∑ i, Real.log (d σ i) := by
  rw [arDeg_span _ (Pi.basisFun K ι).linearIndependent]
  simp only [gramDet_diag, Real.log_prod fun i _ => (hd _ i).ne']
theorem arDeg_stdField_span_singleton {a : K} (ha : a ≠ 0) :
    (stdField K).arDeg (Submodule.span (𝓞 K) {a}) = -Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  rw [arDeg_span_singleton _ ha, abs_norm_eq_prod_complexEmbeddings,
    Real.log_prod fun σ _ => by simpa using ha]
  simp only [stdField_norm]
end ArDeg
noncomputable def degNorm (A : Submodule (𝓞 K) V) : ℝ := h.arDeg A / finrank ℚ K
noncomputable def lcv_sq (A : Submodule (𝓞 K) V) : ℝ := -2 * h.degNorm A
noncomputable def deg_sq (A : Submodule (𝓞 K) V) : ℝ := -h.lcv_sq A
noncomputable def slope (A : Submodule (𝓞 K) V) : ℝ := h.degNorm A / finrank (𝓞 K) A
noncomputable def slope_sq (A : Submodule (𝓞 K) V) : ℝ := -h.lcv_sq A / finrank (𝓞 K) A
noncomputable def arSlope (A : Submodule (𝓞 K) V) : ℝ := h.arDeg A / finrank (𝓞 K) A
noncomputable def quotSlope (A B : Submodule (𝓞 K) V) : ℝ :=
  (h.degNorm A - h.degNorm B) / ((finrank (𝓞 K) A : ℝ) - finrank (𝓞 K) B)
noncomputable def muMax (A : Submodule (𝓞 K) V) : EReal :=
  ⨆ (B : Submodule (𝓞 K) V) (_ : B ≤ A) (_ : B ≠ ⊥), (h.slope B : EReal)
noncomputable def muMin (A : Submodule (𝓞 K) V) : EReal :=
  ⨅ (W : Submodule K V) (_ : ¬ A ≤ W.restrictScalars (𝓞 K)),
    (h.quotSlope A (A ⊓ W.restrictScalars (𝓞 K)) : EReal)
noncomputable def muMax_sq (A : Submodule (𝓞 K) V) : EReal := 2 * h.muMax A
noncomputable def muMin_sq (A : Submodule (𝓞 K) V) : EReal := 2 * h.muMin A
section Slopes
variable {A B : Submodule (𝓞 K) V}
@[simp]
theorem degNorm_bot : h.degNorm ⊥ = 0 := by simp [degNorm]
theorem slope_of_finrank_eq_one (h1 : finrank (𝓞 K) A = 1) : h.slope A = h.degNorm A := by
  simp [slope, h1]
@[simp]
theorem quotSlope_bot (A : Submodule (𝓞 K) V) : h.quotSlope A ⊥ = h.slope A := by
  simp [quotSlope, slope]
theorem slope_le_muMax (hBA : B ≤ A) (h0 : B ≠ ⊥) : (h.slope B : EReal) ≤ h.muMax A :=
  le_iSup_of_le B (le_iSup_of_le hBA (le_iSup_of_le h0 le_rfl))
theorem muMax_le_iff {c : EReal} : h.muMax A ≤ c ↔ ∀ B ≤ A, B ≠ ⊥ → (h.slope B : EReal) ≤ c := by
  simp [muMax]
theorem muMax_le_coe_iff {c : ℝ} : h.muMax A ≤ c ↔ ∀ B ≤ A, B ≠ ⊥ → h.slope B ≤ c := by
  simp [muMax_le_iff]
@[simp]
theorem muMax_bot : h.muMax ⊥ = ⊥ := by simp [muMax]
@[simp]
theorem muMin_bot : h.muMin ⊥ = ⊤ := by simp [muMin]
theorem muMax_of_finrank_eq_one (hA : A.FG) (h1 : finrank (𝓞 K) A = 1) :
    h.muMax A = h.slope A := by
  have h0 : A ≠ ⊥ := by
    rintro rfl
    simp at h1
  refine le_antisymm (h.muMax_le_coe_iff.2 fun B hBA hB => ?_) (h.slope_le_muMax le_rfl h0)
  haveI : Module.Finite (𝓞 K) A := Module.Finite.iff_fg.2 hA
  have hr : finrank (𝓞 K) B = 1 :=
    le_antisymm (h1 ▸ Submodule.finrank_mono hBA) (finrank_lattice_pos (hA.of_le hBA) hB)
  rw [h.slope_of_finrank_eq_one hr, h.slope_of_finrank_eq_one h1]
  exact div_le_div_of_nonneg_right (h.arDeg_le_of_finrank_eq hA hBA (hr.trans h1.symm))
    (Nat.cast_nonneg _)
section Comap
variable (f : V' →ₗ[K] V) (hf : Function.Injective f) {A' : Submodule (𝓞 K) V'}
end Comap
end Slopes
end NumberField
example : (std ℂ Unit).form (RingHom.id ℂ) (fun _ => Complex.I) (fun _ => 1) = Complex.I := by
  simp [std_form]
example : (diag (K := ℚ) (fun _ => ![1, 4]) (fun _ i => by fin_cases i <;> simp)).arDeg
    (Submodule.span (𝓞 ℚ) (Set.range (Pi.basisFun ℚ (Fin 2)))) = -Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [arDeg_diag]
  simp [h4, Embeddings.card]
example : (std ℚ Unit).arDeg (Submodule.span (𝓞 ℚ) {fun _ => 3}) = -Real.log 3 := by
  rw [arDeg_span_singleton _ (fun h0 => by simpa using congrFun h0 ())]
  have : ∀ σ : ℚ →+* ℂ, (std ℚ Unit).norm σ (fun _ => 3) = 3 := fun σ => by
    rw [norm, std_form]
    simp
  simp [this, Embeddings.card]
example {K : Type*} [Field K] [NumberField K] :
    (stdField K).muMax (Submodule.span (𝓞 K) {1}) = 0 := by
  have h1 : finrank (𝓞 K) (Submodule.span (𝓞 K) {(1 : K)}) = 1 := by
    rw [finrank_lattice_eq_finrank_span, Submodule.span_span_of_tower,
      finrank_span_singleton one_ne_zero]
  rw [muMax_of_finrank_eq_one _ (Submodule.fg_span_singleton _) h1, slope, degNorm,
    arDeg_stdField_span_singleton one_ne_zero]
  simp
example {K : Type*} [Field K] (σ : K →+* ℂ) (hσ : ComplexEmbedding.conjugate σ ≠ σ) :
    ∃ h : ArchMetric K (Unit → K), ¬ h.ConjInvariant := by
  classical
  refine ⟨diag (fun τ _ => if τ = σ then 1 else 2) fun τ _ => by split_ifs <;> norm_num,
    fun hc => ?_⟩
  have := hc σ (fun _ => 1) (fun _ => 1)
  simp [diag_form, hσ] at this
end ArchMetric
end GlobalTheory


