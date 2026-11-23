-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:15.751286+00:00
-- url     : https://prove2.me/theorems/b937c132-fff0-4111-9d08-20fb5e42c201
-- title:
--   Hilbert Ninety Quotient Hom Eq Iff
-- statement:
--   Definitions and structural lemmas for Hilbert Ninety Quotient Hom Eq Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
namespace GlobalTheory.WeilM
def SB (X : Type) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨hf.1.comp (fun z => c • z), hf.2.comp_left (g := fun z => c • z) (smul_zero c)⟩
structure TestClass (R : Type) [CommRing R] where

  sp : ∀ (κ : Type) [Fintype κ], Submodule ℂ ((κ → R) → ℂ)

  adm : ∀ (κ : Type) [Fintype κ], Set (((κ → R) → ℂ) →ₗ[ℂ] ℂ)

  modu : Rˣ →* ℝ≥0
def sbClass (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] : TestClass R where
  sp κ _ := SB (κ → R)
  adm _ _ := Set.univ
  modu := distribHaarChar R
def schFun (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Submodule ℂ (V → ℂ) :=
  Submodule.span ℂ (Set.range fun f : SchwartzMap V ℂ => (f : V → ℂ))
def realClass : TestClass ℝ where
  sp κ _ := schFun (κ → ℝ)
  adm κ _ := {l | ∃ T : SchwartzMap (κ → ℝ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → ℝ) ℂ, l (f : (κ → ℝ) → ℂ) = T f}
  modu := distribHaarChar ℝ
def complexClass : TestClass ℂ where
  sp κ _ := schFun (κ → ℂ)
  adm κ _ := {l | ∃ T : SchwartzMap (κ → ℂ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → ℂ) ℂ, l (f : (κ → ℂ) → ℂ) = T f}
  modu := distribHaarChar ℂ
section Unitary
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]
def IsUnitaryOn [TopologicalSpace R] (C : TestClass R) (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  ∀ μ : @Measure (κ → R) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ g, ∀ φ ∈ C.sp κ, ∫⁻ x, ‖om g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ
def IsContOn [TopologicalSpace G] (C : TestClass R) (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  ∀ l ∈ C.adm κ, ∀ φ ∈ C.sp κ, Continuous fun g => l (om g φ)
theorem IsUnitaryOn.comp [TopologicalSpace R] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUnitaryOn C om) {H : Type} [Group H] (f : H →* G) : IsUnitaryOn C (om.comp f) :=
  fun μ hμ g φ hφ => h μ hμ (f g) φ hφ
theorem IsContOn.comp [TopologicalSpace G] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsContOn C om) {H : Type} [Group H] [TopologicalSpace H] {f : H →* G} (hf : Continuous f) :
    IsContOn C (om.comp f) :=
  fun l hl φ hφ => (h l hl φ hφ).comp hf
end Unitary
section Adelic
variable (F : Type) [Field F] [NumberField F]
def pureA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun x => f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g (fun i => (x i).2)
def schA (κ : Type) [Fintype κ] : Submodule ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g}
def adeleClass [LocallyCompactSpace (AdeleRing (𝓞 F) F)] : TestClass (AdeleRing (𝓞 F) F) where
  sp κ _ := schA F κ
  adm κ _ := {l | ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = T f}
  modu := distribHaarChar (AdeleRing (𝓞 F) F)
def thetaSum {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℂ :=
  ∑' ξ : κ → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
end Adelic
section Heis
variable {R : Type} [CommRing R] [Invertible (2 : R)]
def schr (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) : (κ → R) → ℂ :=
  fun x => ψ (x ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1)
structure Darboux {W : Type} [AddCommGroup W] [Module R W] (B : W → W → R) (κ : Type) [Fintype κ] where

  e : W ≃ₗ[R] (κ → R) × (κ → R)
  form : ∀ w w', B w w' = (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2
variable {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]
def Darboux.rho (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) : ((κ → R) → ℂ) → ((κ → R) → ℂ) := schr ψ (d.e w)
structure IsSplitting (C : TestClass R) (ψ : AddChar R ℂ) (d : Darboux B κ) {G : Type} [Group G] (act : G → W → W)
    (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop where
  pres : ∀ g, ∀ φ ∈ C.sp κ, om g φ ∈ C.sp κ
  impl : ∀ g w, ∀ φ ∈ C.sp κ, om g (d.rho ψ w φ) = d.rho ψ (act g w) (om g φ)
  adm : ∀ g, ∀ l ∈ C.adm κ, l ∘ₗ om g ∈ C.adm κ
structure IsUSplitting [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (d : Darboux B κ) {G : Type} [Group G]
    [TopologicalSpace G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop
    extends IsSplitting C ψ d act om where
  unit : IsUnitaryOn C om
  cont : IsContOn C om
end Heis
section Pair
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
def UG {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : Subgroup (GL ι E) where
  carrier := {g | (g : Matrix ι ι E)ᵀ * J * (g : Matrix ι ι E).map c = J}
  one_mem' := by simp [Matrix.map_one _ (map_zero c) (map_one c)]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul] at *
    rw [show ((a : Matrix ι ι E) * (b : Matrix ι ι E)).map c = (a : Matrix ι ι E).map c * (b : Matrix ι ι E).map c from
      Matrix.map_mul (f := c.toRingHom)]
    calc _ = (b : Matrix ι ι E)ᵀ * ((a : Matrix ι ι E)ᵀ * J * (a : Matrix ι ι E).map c) * (b : Matrix ι ι E).map c := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : (a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c = 1 := by
      rw [← show ((a : Matrix ι ι E) * ((a⁻¹ : GL ι E) : Matrix ι ι E)).map c =
        (a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c from Matrix.map_mul (f := c.toRingHom),
        Units.mul_inv]
      exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2 : ((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * (a : Matrix ι ι E)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc _ = ((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * ((a : Matrix ι ι E)ᵀ * J * (a : Matrix ι ι E).map c) *
            ((a⁻¹ : GL ι E) : Matrix ι ι E).map c := by rw [ha]
      _ = (((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * (a : Matrix ι ι E)ᵀ) * J *
            ((a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
def IsHerm {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : Prop := (∀ i j, c (J j i) = J i j) ∧ IsUnit J.det
structure IsQuad (ξ : E) : Prop where
  unit : IsUnit ξ
  anti : c ξ = -ξ
  basis : ∃ b : Module.Basis (Fin 2) R E, b 0 = 1 ∧ b 1 = ξ
def h90 : Eˣ →* Eˣ := MonoidHom.id Eˣ / Units.map (c : E →* E)
def normOne : Subgroup Eˣ := (MonoidHom.id Eˣ * Units.map (c : E →* E)).ker
def IsTilde (χ : Eˣ →* Circle) (u : Eˣ) (t : Circle) : Prop := ∃ z : Eˣ, (u : E) * c z = z ∧ t = χ z
def tilde (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) : (h90 c).range →* Circle :=
  (h90 c).rangeRestrict.liftOfSurjective (h90 c).rangeRestrict_surjective ⟨χ, fun z hz => hχ z (by
    rw [MonoidHom.ker_rangeRestrict] at hz
    exact (congrArg Units.val (div_eq_one.mp hz)).symm)⟩
variable {c}
namespace IsQuad
variable {ξ : E} (h : IsQuad c ξ)
include h
variable [Invertible (2 : R)]
end IsQuad
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
def hTens (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) : E :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
def symp (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) : R :=
  Algebra.trace R E (ξ * hTens c JA JB x y)
def actB {JB : Matrix β β E} (h : UG c JB) (x : Matrix α β E) : Matrix α β E := x * ((h : GL β E) : Matrix β β E)ᵀ
def actAB {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB) (x : Matrix α β E) : Matrix α β E :=
  ((p.1 : GL α E) : Matrix α α E) * x * ((p.2 : GL β E) : Matrix β β E)ᵀ
def dbl (JB : Matrix β β E) : Matrix (β ⊕ β) (β ⊕ β) E := Matrix.fromBlocks JB 0 0 (-JB)
def diagCols (β : Type) [DecidableEq β] : Matrix (β ⊕ β) β E := Matrix.fromRows 1 1
def IsLagr (J : Matrix β β E) {ν : Type} [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E) : Prop :=
  Cyᵀ * J * Cy.map c = 0 ∧ ∃ (Cx : Matrix β ν E) (M : Matrix (ν ⊕ ν) β E), Cxᵀ * J * Cx.map c = 0 ∧
    Matrix.fromCols Cy Cx * M = 1 ∧ M * Matrix.fromCols Cy Cx = 1
variable [Invertible (2 : R)]
def SiegelRule (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) {ν : Type} [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E)
    (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  ∀ l ∈ C.adm κ, (∀ z : Matrix α ν E, ∀ φ ∈ C.sp κ, l (d.rho ψ (z * Cyᵀ) φ) = l φ) →
    ∀ (p : UG c JB) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) →
      ∀ φ ∈ C.sp κ, l (om p φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
          ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) * l φ
def boxFun {κ κ' : Type} (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) : (κ ⊕ κ' → R) → ℂ :=
  fun x => φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr)
def IsDblCoord (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ)
    (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) : Prop :=
  ∀ w₁ w₂ : Matrix α β E, dd.e (Matrix.fromCols w₁ w₂) =
    (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2))
def IsWeilB (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsSplitting C ψ d (actB c) om ∧
  ∃ (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (omd : UG c (dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)),
    IsDblCoord c ξ JA JB d dd ∧ IsSplitting C ψ dd (actB c) omd ∧
    SiegelRule c C ψ ξ JA (dbl JB) dd χ (diagCols β) omd ∧
    ∀ (g : UG c JB) (gd : UG c (dbl JB)),
      ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 →
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂
def IsWeilPair (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (χA χB : Eˣ →* Circle)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsWeilB c C ψ ξ JA JB d χA (om.comp (MonoidHom.inr _ _)) ∧
  ∃ d' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) ∧
    IsWeilB c C ψ ξ JB JA d' χB (om.comp (MonoidHom.inl _ _))
def ResEtaPow (K : Subgroup Rˣ) (χ : Eˣ →* Circle) (n : ℕ) : Prop :=
  ∀ a : Rˣ, (χ (Units.map (algebraMap R E : R →* E) a) : ℂ) =
    if a ∈ K ⊔ (Units.map (Algebra.norm R : E →* R)).range then 1 else (-1) ^ n
section Top
variable [TopologicalSpace R] [TopologicalSpace E]
def IsUWeilSplit [IsModuleTopology R E] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E)
    (JB : Matrix β β E) {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) {ν : Type} [Fintype ν]
    [DecidableEq ν] (Cy : Matrix β ν E) (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsLagr c JB Cy ∧ IsUSplitting C ψ d (actB c) om ∧ SiegelRule c C ψ ξ JA JB d χ Cy om
def IsUWeilB [IsModuleTopology R E] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle)
    (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsUSplitting C ψ d (actB c) om ∧
  ∃ (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (omd : UG c (dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)),
    IsDblCoord c ξ JA JB d dd ∧ IsUWeilSplit c C ψ ξ JA (dbl JB) dd χ (diagCols β) omd ∧
    ∀ (g : UG c JB) (gd : UG c (dbl JB)),
      ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 →
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂
def IsUWeilPair [IsModuleTopology R E] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E)
    (JB : Matrix β β E) {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (χA χB : Eˣ →* Circle)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsUWeilB c C ψ ξ JA JB d χA (om.comp (MonoidHom.inr _ _)) ∧
  (∃ d' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) ∧
    IsUWeilB c C ψ ξ JB JA d' χB (om.comp (MonoidHom.inl _ _))) ∧
  IsContOn C om
variable {c} [IsModuleTopology R E] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
variable {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
end Top
end Pair
example {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (x x₁ y : Unit → R) (φ : (Unit → R) → ℂ) :
    schr ψ (x₁, 0) φ x = φ (x + x₁) ∧ schr ψ (0, y) φ x = ψ (x () * y ()) * φ x := by
  simp [schr, dotProduct]
example (χ : ℂˣ →* Circle) : IsTilde (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) χ (Units.mk0 Complex.I Complex.I_ne_zero)
    (χ (Units.mk0 (1 + Complex.I) (by simp [Complex.ext_iff]))) :=
  ⟨_, by simp [Complex.ext_iff], rfl⟩
example (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsModuleTopology ℝ ℂ ∧ IsModuleTopology R (R × R) :=
  ⟨isModuleTopologyOfFiniteDimensional, inferInstance⟩
end GlobalTheory.WeilM
end


