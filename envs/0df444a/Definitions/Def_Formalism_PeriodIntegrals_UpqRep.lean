-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- name    : Formalism_PeriodIntegrals_UpqRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:26.170745+00:00
-- url     : https://prove2.me/theorems/763b9ab0-d936-413f-a093-3d98af932b74
-- title:
--   Upq Rep
-- statement:
--   Definitions and structural lemmas for Upq Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UpqRep.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI.UpqRep
def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1
def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gᴴ * Jm ε * g = Jm ε
def inG {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Xᴴ * Jm ε + Jm ε * X = 0
def inK {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = Jm ε * X
def inP {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = -(Jm ε * X)
def Kset {n : ℕ} (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g}
def hs {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2
lemma Jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
lemma Jm_conjTranspose {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]
def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε (g : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq, inUJ] at *
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg]
      _ = Jm ε := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]
abbrev toM {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
def UJEmb : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    Topology.IsClosedEmbedding (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ∧
    Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
      {g | inUJ ε g}
def UJLocCompact : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), LocallyCompactSpace (UJ ε)
def coeMatrixAlt {n : ℕ} (ε : Fin n → Bool) : UJ ε → Matrix (Fin n) (Fin n) ℂ :=
  fun g => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
lemma coeMatrix_left_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jm_mul_self]
lemma coeMatrix_inv_eq {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε := Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ g.2)
lemma continuous_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Continuous (coeMatrixAlt ε) := Units.continuous_val.comp continuous_subtype_val
lemma isClosed_pseudoUnitary {n : ℕ} (ε : Fin n → Bool) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const
lemma range_coeMatrix {n : ℕ} (ε : Fin n → Bool) :
    Set.range (coeMatrixAlt ε) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact h.2
  · intro hg
    exact ⟨⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.1 (coeMatrix_left_inv ε g hg), coeMatrix_left_inv ε g hg⟩, hg⟩, rfl⟩
lemma isInducing_coeMatrix {n : ℕ} (ε : Fin n → Bool) : IsInducing (coeMatrixAlt ε) := by
  have hc : Continuous (fun m : Matrix (Fin n) (Fin n) ℂ => (m, MulOpposite.op (Jm ε * mᴴ * Jm ε))) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  refine IsInducing.of_comp (continuous_coeMatrix ε) hc ?_
  have e : (fun m : Matrix (Fin n) (Fin n) ℂ => (m, MulOpposite.op (Jm ε * mᴴ * Jm ε))) ∘ coeMatrixAlt ε =
      Units.embedProduct _ ∘ Subtype.val := funext fun g => by
    simp only [Function.comp_apply, Units.embedProduct_apply, ← coeMatrix_inv_eq]
    rfl
  rw [e]
  exact Units.isInducing_embedProduct.comp IsInducing.subtypeVal
lemma injective_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Function.Injective (coeMatrixAlt ε) := by
  intro a b h
  exact Subtype.ext (Units.ext h)
theorem isClosedEmbeddingMatrix : UJEmb := by
  intro n ε
  refine ⟨⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, ?_⟩, range_coeMatrix ε⟩
  have h := range_coeMatrix ε
  unfold coeMatrixAlt at h
  rw [h]
  exact isClosed_pseudoUnitary ε
theorem uJLocCompact_of (h : UJEmb) : UJLocCompact := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (h n ε).1.locallyCompactSpace
instance instLocallyCompactUJ (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) :=
  uJLocCompact_of isClosedEmbeddingMatrix n ε
instance instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _
instance instBorelSpaceUJ (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩
instance instSecondCountableUJ (n : ℕ) (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbeddingMatrix n ε).1.isInducing.secondCountableTopology
def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) := Measure.haar
instance instIsHaarMuG (n : ℕ) (ε : Fin n → Bool) : (muG ε).IsHaarMeasure := by
  unfold muG; infer_instance
lemma Kset_mul {n : ℕ} (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) : g * h ∈ Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]
lemma Kset_star {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star g ∈ Kset ε := by
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  have h := congrArg Matrix.conjTranspose hg.2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at h
  rw [Matrix.star_eq_conjTranspose]
  exact h.symm
def KG {n : ℕ} (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | toM g ∈ Kset ε}
  mul_mem' := by
    intro g h hg hh
    show toM g * toM h ∈ Kset ε
    exact Kset_mul ε hg hh
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    refine ⟨Submonoid.one_mem _, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro g hg
    have hinv : ((((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) =
        star (toM g) := by
      show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = _
      exact Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem hg.1)
    have h2 : toM g⁻¹ = star (toM g) := hinv
    show toM g⁻¹ ∈ Kset ε
    rw [h2]
    exact Kset_star ε hg
abbrev toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε) : Matrix (Fin n) (Fin n) ℂ := toM (k : UJ ε)
def rhoC {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ)) / 2
def rhoN {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2
def dot {n : ℕ} (u v : Fin n → ℝ) : ℝ := ∑ a, u a * v a
def nsq {n : ℕ} (u : Fin n → ℝ) : ℝ := dot u u
def root {n : ℕ} (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1
def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}
def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0
def IsCRepOn {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {m : ℕ}
    (U : Set (Matrix (Fin m) (Fin m) ℂ)) (π : Matrix (Fin m) (Fin m) ℂ → (Wp →L[ℂ] Wp)) : Prop :=
  π 1 = 1 ∧ ∀ a ∈ U, ∀ b ∈ U, π (a * b) = (π a).comp (π b)
def IsHCParam {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)
def lowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε
def fdegHC {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) /
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))
section SmoothH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def inUH (H g : Matrix (Fin n) (Fin n) ℂ) : Prop := gᴴ * H * g = H
def SmoothOnH (H : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUH H g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUH H g → f g = F g
end SmoothH
abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
section Rep
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsURepOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsCRepOn G σ ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G
def IsIrredOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤
def coefOn {ε : Fin n → Bool} (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H) :
    UJ ε → ℂ :=
  fun g => ⟪w, σ (umat g) v⟫_ℂ
def IsSqIntOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (muG ε)
def IsFdeg {ε : Fin n → Bool} (μ : Measure (UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => coefOn σ v w g * star (coefOn σ v' w' g)) μ ∧
    ∫ g, coefOn σ v w g * star (coefOn σ v' w' g) ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)
def fdegOf {ε : Fin n → Bool} (μ : Measure (UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ
def IsWtOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ G →
    σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v
def CDom (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
    Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b
def IsKStableOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Prop :=
  ∀ g ∈ Kset ε, ∀ v ∈ S, σ g v ∈ S
def IsKTypeOf (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (Kset ε) σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Kset ε) σ μ v → CDom ε μ Λ
def vNormSq (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + (2 : ℝ) • rhoC ε)
def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | inUJ ε g}
def IsDS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ ∧
    (∃ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      vNormSq ε (lowK ε lam) ≤ vNormSq ε μ
def lowKSub (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Submodule ℂ H :=
  sSup {S | IsKTypeOf ε σ (lowK ε lam) S}
def IsOrthProjOnto (E : H →L[ℂ] H) (S : Submodule ℂ H) : Prop :=
  E.comp E = E ∧ (∀ x y : H, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ) ∧ LinearMap.range (E : H →ₗ[ℂ] H) = S
def IsHighestUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (w : H) : Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧ IsWtOn (Kset ε) σ (lowK ε lam) w
def IsLowUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ
def allPos (k : ℕ) : Fin k → Bool := fun _ => true
def IsHCTypeU (k : ℕ) (u : Fin k → ℝ) (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ FiniteDimensional ℂ H ∧ IsURepOn (UJset (allPos k)) π ∧
    IsKTypeOf (allPos k) π (lowK (allPos k) u) ⊤
end Rep
section Hpk
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsCayley (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  IsUnit P ∧ Pᴴ * Jm ε * P = Hpk k r
def IsCayleyU (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  IsCayley k r ε P ∧ P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ
def IsDSHpk (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsDS ε lam (fun g => σ (P⁻¹ * g * P))
end Hpk
section Bessel
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsSmoothVec (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  SmoothOnH (Hpk k r) (fun g => σ g v)
def smoothVecs (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | IsSmoothVec (k := k) (r := r) σ v}
end Bessel
section KFin
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsKFinHpk (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
    ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, σ g x ∈ S
end KFin
def eqImg {K H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : K → H →L[ℂ] H) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  sSup {S' | ∃ Θ : S →ₗ[ℂ] H, (∀ (a : K) (v w : S), (w : H) = ρ a v → Θ w = ρ a (Θ v)) ∧ S' = LinearMap.range Θ}
end PI.UpqRep
end


