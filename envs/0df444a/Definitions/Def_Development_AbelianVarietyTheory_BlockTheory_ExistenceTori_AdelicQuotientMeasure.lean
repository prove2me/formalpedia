-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicQuotientMeasure
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicQuotientMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:50.018969+00:00
-- url     : https://prove2.me/theorems/3869242b-ed9c-45d3-abc3-fd1670844d2b
-- title:
--   Adelic Quotient Measure
-- statement:
--   Definitions and structural lemmas for Adelic Quotient Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AdelicQuotientMeasure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped TensorProduct Matrix ENNReal
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses
section General
variable {H : Type} [Group H] (Γ : Subgroup H)
abbrev LQuot : Type := MulAction.orbitRel.Quotient Γ H
def cls (g : H) : LQuot Γ := Quotient.mk (MulAction.orbitRel Γ H) g
theorem cls_eq_iff (g g' : H) : cls Γ g = cls Γ g' ↔ ∃ γ ∈ Γ, g = γ * g' := by
  rw [cls, cls, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, h⟩
    exact ⟨γ, γ.2, h.symm⟩
  · rintro ⟨γ, hγ, h⟩
    exact ⟨⟨γ, hγ⟩, h.symm⟩
def rightMul (k : H) : LQuot Γ → LQuot Γ :=
  Quotient.lift (fun g => cls Γ (g * k)) fun a b hab => by
    obtain ⟨γ, hγ, h⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
    exact (cls_eq_iff Γ _ _).2 ⟨γ, hγ, by rw [h, mul_assoc]⟩
variable [MeasurableSpace H]
theorem measurable_cls : Measurable (cls Γ) := measurable_quotient_mk' (s := MulAction.orbitRel Γ H)
def quotMeasure (μ : Measure H) (D : Set H) (_hD : IsFundamentalDomain Γ D μ) : Measure (LQuot Γ) :=
  (μ.restrict D).map (cls Γ)
theorem quotMeasure_apply (μ : Measure H) (D : Set H) (hD : IsFundamentalDomain Γ D μ)
    {S : Set (LQuot Γ)} (hS : MeasurableSet S) : quotMeasure Γ μ D hD S = μ (cls Γ ⁻¹' S ∩ D) := by
  rw [quotMeasure, Measure.map_apply (measurable_cls Γ) hS, Measure.restrict_apply (measurable_cls Γ hS)]
theorem quotMeasure_univ (μ : Measure H) (D : Set H) (hD : IsFundamentalDomain Γ D μ) :
    quotMeasure Γ μ D hD Set.univ = μ D := by
  rw [quotMeasure_apply Γ μ D hD MeasurableSet.univ]; simp
def probMeasure (μ : Measure H) (D : Set H) (hD : IsFundamentalDomain Γ D μ) (h0 : μ D ≠ 0) (h1 : μ D ≠ ∞) :
    ProbabilityMeasure (LQuot Γ) :=
  ⟨(μ D)⁻¹ • quotMeasure Γ μ D hD,
    ⟨by rw [Measure.smul_apply, quotMeasure_univ, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩⟩
example (μ : Measure H) : IsFundamentalDomain (⊥ : Subgroup H) Set.univ μ where
  nullMeasurableSet := MeasurableSet.univ.nullMeasurableSet
  ae_covers := Eventually.of_forall fun _ => ⟨1, Set.mem_univ _⟩
  aedisjoint := fun a b hab => absurd (Subsingleton.elim a b) hab
end General
def unitaryOf {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) :
    Subgroup (GL (Fin n) R) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) R)ᵀ * J * (g : Matrix (Fin n) (Fin n) R).map s = J}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at ha hb ⊢
    calc _ = (b : Matrix (Fin n) (Fin n) R)ᵀ * ((a : Matrix (Fin n) (Fin n) R)ᵀ * J *
              (a : Matrix (Fin n) (Fin n) R).map s) * (b : Matrix (Fin n) (Fin n) R).map s := by
            simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * (a : Matrix (Fin n) (Fin n) R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h2 : (a : Matrix (Fin n) (Fin n) R).map s * ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s
        = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv]; simp
    conv_lhs => rw [← ha]
    calc _ = (((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * (a : Matrix (Fin n) (Fin n) R)ᵀ) * J *
          ((a : Matrix (Fin n) (Fin n) R).map s *
            ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2]; simp
def unitaryMap {R R' : Type} [CommRing R] [CommRing R'] (s : R →+* R) (s' : R' →+* R') (φ : R →+* R')
    (hφ : ∀ x, φ (s x) = s' (φ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) :
    unitaryOf s J →* unitaryOf s' (J.map φ) :=
  ((Matrix.GeneralLinearGroup.map φ).comp (unitaryOf s J).subtype).codRestrict _ fun g => by
    have h : ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * J *
        ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s = J := g.2
    have h' := congrArg (fun M : Matrix (Fin n) (Fin n) R => M.map φ) h
    simp only [Matrix.map_mul] at h'
    have e : (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s).map φ =
        (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map φ).map s' := by
      ext a b; simp [hφ]
    rw [e, Matrix.transpose_map] at h'
    exact h'
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
def AfE : Type := GlobalTheory.AdLat.RA (maximalRealSubfield E) E
abbrev AfF : Type := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
instance : CommRing (AfE E) := inferInstanceAs (CommRing (AfF E ⊗[maximalRealSubfield E] E))
instance : Algebra (AfF E) (AfE E) := inferInstanceAs (Algebra (AfF E) (AfF E ⊗[maximalRealSubfield E] E))
instance : Module.Finite (AfF E) (AfE E) :=
  inferInstanceAs (Module.Finite (AfF E) (AfF E ⊗[maximalRealSubfield E] E))
instance : TopologicalSpace (AfE E) := moduleTopology (AfF E) (AfE E)
instance : IsModuleTopology (AfF E) (AfE E) := ⟨rfl⟩
instance : IsTopologicalRing (AfE E) := IsModuleTopology.isTopologicalRing (AfF E) (AfE E)
def toAf : E →+* AfE E :=
  (Algebra.TensorProduct.includeRight :
    E →ₐ[maximalRealSubfield E] AfF E ⊗[maximalRealSubfield E] E).toRingHom
def cj : E →+* E := (IsCMField.complexConj E : E →+* E)
def cjAf : AfE E →+* AfE E := (GlobalTheory.AdLat.sg (AfF E) (IsCMField.complexConj E)).toRingHom
theorem toAf_cj (x : E) : toAf E (cj E x) = cjAf E (toAf E x) := by
  change (1 : AfF E) ⊗ₜ[maximalRealSubfield E] (IsCMField.complexConj E x) =
    GlobalTheory.AdLat.sg (AfF E) (IsCMField.complexConj E) ((1 : AfF E) ⊗ₜ[maximalRealSubfield E] x)
  simp [GlobalTheory.AdLat.sg]
theorem emb_cj (τ : E →+* ℂ) (x : E) : τ (cj E x) = starRingEnd ℂ (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x
variable {E} {n : ℕ}
def IsHermGram (G : Matrix (Fin n) (Fin n) E) : Prop := (∀ a b, G b a = cj E (G a b)) ∧ G.det ≠ 0
example : IsHermGram (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a b => by by_cases h : a = b <;> simp [Matrix.one_apply, h, eq_comm], by simp⟩
variable (G : Matrix (Fin n) (Fin n) E)
abbrev URat : Type := unitaryOf (cj E) G
abbrev UReal (w : InfinitePlace E) : Type := unitaryOf (starRingEnd ℂ) (G.map w.embedding)
abbrev UFin : Type := unitaryOf (cjAf E) (G.map (toAf E))
def UAd : Type := (∀ w : InfinitePlace E, UReal G w) × UFin G
instance : Group (UAd G) := inferInstanceAs (Group ((∀ w : InfinitePlace E, UReal G w) × UFin G))
instance : TopologicalSpace (UAd G) :=
  inferInstanceAs (TopologicalSpace ((∀ w : InfinitePlace E, UReal G w) × UFin G))
instance : IsTopologicalGroup (UAd G) :=
  inferInstanceAs (IsTopologicalGroup ((∀ w : InfinitePlace E, UReal G w) × UFin G))
instance : MeasurableSpace (UAd G) := borel (UAd G)
instance : BorelSpace (UAd G) := ⟨rfl⟩
def diag : URat G →* UAd G :=
  MonoidHom.prod
    (Pi.monoidHom fun w : InfinitePlace E =>
      unitaryMap (cj E) (starRingEnd ℂ) w.embedding (emb_cj E w.embedding) G)
    (unitaryMap (cj E) (cjAf E) (toAf E) (toAf_cj E) G)
def ratPts : Subgroup (UAd G) := (diag G).range
abbrev AutQuot : Type := LQuot (ratPts G)
def autCls (g : UAd G) : AutQuot G := cls (ratPts G) g
def sgnMat (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if (i : ℕ) < p then 1 else -1
def lieCube (n p : ℕ) (r : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | Xᵀ * sgnMat n p + sgnMat n p * X.map (starRingEnd ℂ) = 0 ∧ (∀ i, |(X i i).im| ≤ r) ∧
    ∀ i j, i < j → |(X i j).re| ≤ r ∧ |(X i j).im| ≤ r}
def IsOrthoFrame (w : InfinitePlace E) (p : ℕ) (b : GL (Fin n) ℂ) : Prop :=
  p ≤ n ∧ (b : Matrix (Fin n) (Fin n) ℂ)ᵀ * G.map w.embedding *
    (b : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = sgnMat n p
def cubeNhd (K : Subgroup (UFin G)) (p : InfinitePlace E → ℕ) (b : InfinitePlace E → GL (Fin n) ℂ) (r : ℝ) :
    Set (UAd G) :=
  {g | g.2 ∈ K ∧ ∀ w, ∃ X ∈ lieCube n (p w) r,
    (((b w)⁻¹ * (g.1 w : GL (Fin n) ℂ) * b w : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X}
def IsNormalised (K : Subgroup (UFin G)) (μ : Measure (UAd G)) : Prop :=
  IsOpen (K : Set (UFin G)) ∧ IsCompact (K : Set (UFin G)) ∧ μ.IsHaarMeasure ∧
    ∃ (p : InfinitePlace E → ℕ) (b : InfinitePlace E → GL (Fin n) ℂ), (∀ w, IsOrthoFrame G w (p w) (b w)) ∧
      Tendsto (fun r : ℝ => μ (cubeNhd G K p b r) /
        ENNReal.ofReal ((2 * r) ^ (n ^ 2 * Fintype.card (InfinitePlace E)))) (𝓝[>] 0) (𝓝 1)
def autMeasure (μ : Measure (UAd G)) (D : Set (UAd G)) (hD : IsFundamentalDomain (ratPts G) D μ) :
    Measure (AutQuot G) := quotMeasure (ratPts G) μ D hD
instance : Countable (ratPts G) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  exact (diag G).rangeRestrict_surjective.countable
theorem vol_ne_zero (μ : Measure (UAd G)) [μ.IsHaarMeasure] (D : Set (UAd G))
    (hD : IsFundamentalDomain (ratPts G) D μ) : μ D ≠ 0 :=
  hD.measure_ne_zero (NeZero.ne μ)
def autProb (μ : Measure (UAd G)) [μ.IsHaarMeasure] (D : Set (UAd G))
    (hD : IsFundamentalDomain (ratPts G) D μ) (hfin : μ D ≠ ∞) : ProbabilityMeasure (AutQuot G) :=
  probMeasure (ratPts G) μ D hD (vol_ne_zero G μ D hD) hfin
def IsVolDatum (K : Subgroup (UFin G)) (μ : Measure (UAd G)) (D : Set (UAd G)) : Prop :=
  IsNormalised G K μ ∧ IsFundamentalDomain (ratPts G) D μ
def normMeasure {K : Subgroup (UFin G)} {μ : Measure (UAd G)} {D : Set (UAd G)} (h : IsVolDatum G K μ D) :
    Measure (AutQuot G) := autMeasure G μ D h.2
def normProb {K : Subgroup (UFin G)} {μ : Measure (UAd G)} {D : Set (UAd G)} (h : IsVolDatum G K μ D)
    (hfin : μ D ≠ ∞) : ProbabilityMeasure (AutQuot G) :=
  haveI : μ.IsHaarMeasure := h.1.2.2.1
  autProb G μ D h.2 hfin
def NormMeasureCanonical : Prop :=
  IsHermGram G → ∀ (K : Subgroup (UFin G)) (μ μ' : Measure (UAd G)) (D D' : Set (UAd G))
    (h : IsVolDatum G K μ D) (h' : IsVolDatum G K μ' D'), normMeasure G h = normMeasure G h'
def NormalisedExists : Prop :=
  IsHermGram G → ∀ K : Subgroup (UFin G), IsOpen (K : Set (UFin G)) → IsCompact (K : Set (UFin G)) →
    (∃! μ : Measure (UAd G), IsNormalised G K μ) ∧
      ∀ μ : Measure (UAd G), IsNormalised G K μ →
        ∃ D : Set (UAd G), MeasurableSet D ∧ IsFundamentalDomain (ratPts G) D μ
def FiniteVolume : Prop :=
  IsHermGram G → ∀ (μ : Measure (UAd G)) [μ.IsHaarMeasure] (D : Set (UAd G)),
    IsFundamentalDomain (ratPts G) D μ → μ D ≠ ∞
def ProbOpenPos : Prop :=
  IsHermGram G → ∀ (μ : Measure (UAd G)) [μ.IsHaarMeasure] (D : Set (UAd G))
    (hD : IsFundamentalDomain (ratPts G) D μ) (hfin : μ D ≠ ∞),
      (autProb G μ D hD hfin : Measure (AutQuot G)).IsOpenPosMeasure
def ProbCanonical : Prop :=
  IsHermGram G → ∀ (μ μ' : Measure (UAd G)) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (D D' : Set (UAd G))
    (hD : IsFundamentalDomain (ratPts G) D μ) (hD' : IsFundamentalDomain (ratPts G) D' μ')
    (hfin : μ D ≠ ∞) (hfin' : μ' D' ≠ ∞),
      autProb G μ D hD hfin = autProb G μ' D' hD' hfin' ∧
        ∀ k : UAd G, (autProb G μ D hD hfin : Measure (AutQuot G)).map (rightMul (ratPts G) k) =
          autProb G μ D hD hfin
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses


