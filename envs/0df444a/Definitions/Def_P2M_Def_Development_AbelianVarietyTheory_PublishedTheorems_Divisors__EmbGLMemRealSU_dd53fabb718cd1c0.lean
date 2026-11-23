-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EmbGLMemRealSU_dd53fabb718cd1c0
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EmbGLMemRealSU_dd53fabb718cd1c0
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:51.411803+00:00
-- url     : https://prove2.me/theorems/3abbfabe-df6b-48d2-8758-b0f5e42452f5
-- title:
--   Emb GLMem Real SU
-- statement:
--   Definitions and structural lemmas for Emb GLMem Real SU, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EmbGLMemRealSU.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PlaceShiftStatements_DefiniteBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SUVol
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal NNReal
section General
variable {ι : Type} [Fintype ι] {r : ℕ}
def tanBall (ι : Type) (r : ℕ) (ε : ℝ) : Set (ι → Fin r → Fin r → ℂ) := {X | ∀ τ a b, ‖X τ a b‖ < ε}
def grpBall (H : Subgroup (ι → GL (Fin r) ℂ)) (ε : ℝ) : Set H :=
  {g | ∀ τ a b, ‖(g.1 τ : Matrix (Fin r) (Fin r) ℂ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε}
def HasDensityOne (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H)
    (ν : Measure (ι → Fin r → Fin r → ℂ)) : Prop :=
  Tendsto (fun ε : ℝ => μ (grpBall H ε) / ν (tanBall ι r ε)) (𝓝[>] 0) (𝓝 1)
def tangentHaar (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure (ι → Fin r → Fin r → ℂ)) : Measure H :=
  limsup (fun ε : ℝ => ν (tanBall ι r ε) / (Measure.haar : Measure H) (grpBall H ε)) (𝓝[>] 0) •
    (Measure.haar : Measure H)
instance (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure (ι → Fin r → Fin r → ℂ)) : (tangentHaar H ν).IsMulLeftInvariant := by
  unfold tangentHaar; infer_instance
end General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def realSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : Subgroup (Ψ → GL (Fin r) ℂ) where
  carrier := {g | ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 ∧ ∀ u w,
    hermC τ.1 G ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w}
  one_mem' τ := by simp
  mul_mem' {g g'} hg hg' τ := by
    refine ⟨by simp [(hg τ).1, (hg' τ).1], fun u w => ?_⟩
    simp only [Pi.mul_apply, Units.val_mul, ← mulVec_mulVec, (hg τ).2, (hg' τ).2]
  inv_mem' {g} hg τ := by
    refine ⟨?_, fun u w => ?_⟩
    · have := congrArg Matrix.det (g τ).mul_inv
      rwa [det_mul, (hg τ).1, one_mul, det_one] at this
    · rw [← (hg τ).2]
      simp only [Pi.inv_apply, mulVec_mulVec, Units.mul_inv, one_mulVec]
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology in
open scoped ENNReal NNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.SUVol.isClosed_realSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    IsClosed (_root_.GlobalTheory.SUVol.realSU Ψ G : Set (Ψ → GL (Fin r) ℂ)) := by
  show IsClosed {g : Ψ → GL (Fin r) ℂ | ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 ∧ ∀ u w,
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w}
  have hc : ∀ τ : Ψ, Continuous fun g : Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    fun τ => Units.continuous_val.comp (continuous_apply τ)
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isClosed_iInter fun τ => ((isClosed_eq (hc τ).matrix_det continuous_const).inter
    (isClosed_iInter fun u => isClosed_iInter fun w => isClosed_eq ?_ continuous_const))
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC
  have hu := (hc τ).matrix_mulVec (continuous_const (y := u))
  have hw := (hc τ).matrix_mulVec (continuous_const (y := w))
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact (((continuous_apply a).comp hu).mul continuous_const).mul
    (Complex.continuous_conj.comp ((continuous_apply b).comp hw))
instance (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : LocallyCompactSpace (realSU Ψ G) := by
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin r) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact (isClosed_realSU Ψ G).locallyCompactSpace
instance (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : SecondCountableTopology (realSU Ψ G) := by
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Subtype.secondCountableTopology _
def realLie (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : Submodule ℝ (Ψ → Fin r → Fin r → ℂ) where
  carrier := {X | ∀ τ : Ψ, (Matrix.of (X τ)).trace = 0 ∧ ∀ u w,
    hermC τ.1 G (Matrix.of (X τ) *ᵥ u) w + hermC τ.1 G u (Matrix.of (X τ) *ᵥ w) = 0}
  zero_mem' τ := by simp [hermC]
  add_mem' {X Y} hX hY τ := by
    have e : Matrix.of ((X + Y) τ) = Matrix.of (X τ) + Matrix.of (Y τ) := rfl
    refine ⟨by rw [e, trace_add, (hX τ).1, (hY τ).1, add_zero], fun u w => ?_⟩
    have h1 := (hX τ).2 u w
    have h2 := (hY τ).2 u w
    rw [e]
    simp only [hermC, add_mulVec, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX τ := by
    have e : Matrix.of ((c • X) τ) = (c : ℂ) • Matrix.of (X τ) := rfl
    refine ⟨by rw [e, trace_smul, (hX τ).1, smul_zero], fun u w => ?_⟩
    have h1 := congrArg (fun z => (c : ℂ) * z) ((hX τ).2 u w)
    rw [e]
    simp only [hermC, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, mul_add,
      Finset.mul_sum, mul_zero] at h1 ⊢
    rw [← h1]
    congr 1 <;> refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_ <;> ring
def fromFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun Y τ := (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
  map_add' Y Z := by
    funext τ
    have e : Matrix.of (fun a b => (Y + Z) (τ, a, b)) =
      Matrix.of (fun a b => Y (τ, a, b)) + Matrix.of (fun a b => Z (τ, a, b)) := rfl
    rw [e, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c Y := by
    funext τ
    have e : Matrix.of (fun a b => (c • Y) (τ, a, b)) = c • Matrix.of (fun a b => Y (τ, a, b)) := rfl
    rw [e, Matrix.mul_smul, Matrix.smul_mul]; rfl
def riemLie (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) :
    Measure (Ψ → Fin r → Fin r → ℂ) :=
  Measure.map (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1)
    (stdOrthonormalBasis ℝ ((realLie Ψ G).comap (fromFrame x))).toBasis.addHaar
def riemHaar (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)] : Measure (realSU Ψ G) :=
  tangentHaar (realSU Ψ G) (riemLie Ψ G x)
def formLie (Ψ : Finset (E →+* ℂ)) {n : ℕ} (e : Fin n → Matrix (Fin r) (Fin r) E) :
    Measure (Ψ → Fin r → Fin r → ℂ) :=
  Measure.map (fun (c : Ψ → Fin n → ℝ) (τ : Ψ) (a b : Fin r) => ∑ i, (c τ i : ℂ) * τ.1 (e i a b)) volume
def lieLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) ∧ ∀ x ∈ Λ, X *ᵥ x ∈ Λ}
  zero_mem' := ⟨by simp, by simp [herm, cc], by simp⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], fun u w => ?_, fun x hx => ?_⟩
    · have h1 := hX.2.1 u w
      have h2 := hY.2.1 u w
      simp only [herm, cc, add_mulVec, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
      linear_combination h1 + h2
    · rw [add_mulVec]; exact Λ.add_mem (hX.2.2 x hx) (hY.2.2 x hx)
  neg_mem' {X} hX := by
    refine ⟨by rw [trace_neg, hX.1, neg_zero], fun u w => ?_, fun x hx => ?_⟩
    · have h1 := hX.2.1 u w
      simp only [herm, cc, neg_mulVec, Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib] at h1 ⊢
      linear_combination -h1
    · rw [neg_mulVec]; exact Λ.neg_mem (hX.2.2 x hx)
def IsSA (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) : Prop :=
  IsUA (IsCMField.complexConj E) G g ∧ g.det = 1
def SEquiv (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ)
    (g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) : Prop :=
  ∃ γ : Matrix (Fin r) (Fin r) E, IsSA G (ratM (maximalRealSubfield E) γ) ∧
    ∃ k, IsKM (IsCMField.complexConj E) G L M k ∧ k.det = 1 ∧ g' = ratM (maximalRealSubfield E) γ * g * k
def IsSReps (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) {J : Type}
    (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) : Prop :=
  (∀ j, IsSA G (s j)) ∧ (∀ i j, SEquiv G L M (s i) (s j) → i = j) ∧ ∀ g, IsSA G g → ∃ j, SEquiv G L M (s j) g
theorem ratM_mul (γ δ : Matrix (Fin r) (Fin r) E) :
    ratM (maximalRealSubfield E) (γ * δ) = ratM (maximalRealSubfield E) γ * ratM (maximalRealSubfield E) δ :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E))
theorem ratM_one : ratM (maximalRealSubfield E) (1 : Matrix (Fin r) (Fin r) E) = 1 :=
  Matrix.map_one _ (TensorProduct.tmul_zero _ _) rfl
def ratStab (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E))
    (s : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) : Subgroup (GL (Fin r) E) where
  carrier := {γ | (γ : Matrix (Fin r) (Fin r) E).det = 1 ∧
    (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧
    ∀ x, ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈
        s.mulVec '' (hat (maximalRealSubfield E) L : Set _) ↔
      x ∈ s.mulVec '' (hat (maximalRealSubfield E) L : Set _)}
  one_mem' := ⟨by simp, by simp, by simp [ratM_one]⟩
  mul_mem' {g g'} hg hg' := by
    refine ⟨by simp [hg.1, hg'.1], fun u w => ?_, fun x => ?_⟩
    · simp only [Units.val_mul, ← mulVec_mulVec, hg.2.1, hg'.2.1]
    · rw [Units.val_mul, ratM_mul, ← mulVec_mulVec, hg.2.2, hg'.2.2]
  inv_mem' {g} hg := by
    refine ⟨?_, fun u w => ?_, fun x => ?_⟩
    · have := congrArg Matrix.det g.mul_inv
      rwa [det_mul, hg.1, one_mul, det_one] at this
    · rw [← hg.2.1]
      simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]
    · rw [← hg.2.2, mulVec_mulVec, ← ratM_mul, Units.mul_inv, ratM_one, one_mulVec]
def embGL (Ψ : Finset (E →+* ℂ)) (r : ℕ) : GL (Fin r) E →* (Ψ → GL (Fin r) ℂ) :=
  Pi.monoidHom fun τ => Matrix.GeneralLinearGroup.map τ.1
def inReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) :
    Subgroup (realSU Ψ G) :=
  (Γ.map (embGL Ψ r)).subgroupOf (realSU Ψ G)
def resOrder (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ℕ :=
  open Classical in
  if (v.asIdeal.map (algebraMap _ (𝓞 E))).IsPrime then
    Set.ncard ((fun g : Matrix (Fin r) (Fin r) (𝓞 E) =>
        g.map (Ideal.Quotient.mk (v.asIdeal.map (algebraMap _ (𝓞 E))))) ''
      {g | g.det - 1 ∈ v.asIdeal.map (algebraMap _ (𝓞 E)) ∧ ∀ a b,
        (gᵀ * g.map (IsCMField.ringOfIntegersComplexConj E) - 1) a b ∈ v.asIdeal.map (algebraMap _ (𝓞 E))})
  else Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal))
def locFactor (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ℝ :=
  (resOrder E r v : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ (r ^ 2 - 1)
end GlobalTheory.SUVol


