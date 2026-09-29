-- Prove2me | Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
-- name    : AutomorphicForm_BoundedGenuineCuspRealization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/99f36a7e-110c-5155-bcc0-bb423f392715
-- title:
--   Bounded genuine cusp realisations of Hecke eigensystems
-- statement:
--   Throughout, $F$ is a number field, and a bundle `pins : CarrierPins F` supplies in particular a measurable structure `pins.nS` and measure `pins.ν` on the adele ring of $F$, together with a measurable structure and measure on $\mathrm{GL}_2$ of the adeles; $\psi$ is an additive character of the adele ring with values in $\mathbb{C}$.
--
--   `IsBoundedOnSiegelWindows F φ` says of $φ : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ that for all reals $c,u,d_1,d_2$ with $c>0$, $d_1>0$ and every finite set $T$ of adelic matrices there is a real $C$ with $\|φ(g)\| \le C$ for all $g$ in $\bigcup_{x\in T}\,\{hx : h \in \mathtt{centreCutSiegelSet } F\,c\,u\,d_1\,d_2\}$, i.e. $φ$ is bounded on each finite union of right translates of a centre-cut Siegel set. `IsBoundedGenuineFn F pins ψ φ` is the conjunction of four conditions: $φ$ is continuous; $φ$ is bounded on the Siegel windows; for every $α \in F$ and every $g$ the function $x \mapsto φ(n(x)g)\,ψ(-αx)$, with $n(x)$ the upper unipotent matrix, is integrable for `pins.ν`; and for every $g$ the family of Whittaker coefficients $α \mapsto \int φ(n(x)g)ψ(-αx)\,d\nu$, indexed by $α \in F$, is summable.
--
--   Relative to a Hecke eigensystem $Φ$ over $\mathbb{C}$ and a term `R : SmoothCuspRealizationAt F pins Φ`, the predicate `IsBoundedGenuineCuspRealizationAt` asserts `IsBoundedGenuineFn` for `R.toFun`; `IsBoundedGenuineCuspRealizable` asks for some such $R$; `IsArithBoundedGenuineCuspRealizable` applies this to the eigensystem `Φ.toRawCentral` attached to $Φ$, and `IsArithBoundedGenuineCuspRealizableVia ι` to the image `Φ.map ι` of an eigensystem over a commutative ring along a ring homomorphism $ι$ to $\mathbb{C}$. From a choice of pins for every number field, `boundedGenuineCuspNotionOf` assembles a `CuspidalityNotion ℂ` whose cusp predicate is the arithmetic version taken with the standard additive character [`NumberField.StandardAddChar.stdAddChar F`](../def/NumberField_AdelicTraceFin.html#L198).
--
--   The accompanying lemmas record the four projections of the conjunction; stability of the predicate under multiplication by $g \mapsto c(\det g)$ for a continuous such function with $\|c\| \le 1$ on units (the Whittaker integral simply acquires the factor $c(\det g)$, since unipotent matrices have determinant $1$); transport along an equality of underlying functions, also between realisations of different eigensystems and for pins of `productionPinsOf` type with differing window, level and generator data but the same conditioning set; and the implication from this notion to the corresponding genuine (continuity-only) cusp notion, at the level of single realisations, of realisability, of the arithmetic and `Via` variants, and of the assembled cuspidality notions.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, Haar measures, integrability and `Summable` used here, but has no notion of adelic Siegel sets, Whittaker coefficients for $\mathrm{GL}_2$ over a number field, or cuspidality notions for Hecke eigensystems; those are the project's own.
--
--   **Where it is used.** These predicates sit in the automorphic half of the argument, refining mere continuity of a realisation of a Hecke eigensystem to growth on Siegel windows together with convergence of its adelic Fourier–Whittaker expansion, and packaging the result as a cuspidality notion over $\mathbb{C}$ that can be fed into the modularity statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_BoundedGenuineCuspRealization.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm.WindowedSiegel

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsBoundedOnSiegelWindows (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C

def IsBoundedGenuineFn (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  Continuous φ ∧
    IsBoundedOnSiegelWindows F φ ∧
    (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun α : F => whittakerCoefficient F pins ψ φ α g)

def IsBoundedGenuineCuspRealizationAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ) : Prop :=
  IsBoundedGenuineFn F pins ψ R.toFun

def IsBoundedGenuineCuspRealizable (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ R : SmoothCuspRealizationAt F pins Φ, IsBoundedGenuineCuspRealizationAt F pins ψ Φ R

def IsArithBoundedGenuineCuspRealizable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsBoundedGenuineCuspRealizable F pins ψ Φ.toRawCentral

def IsArithBoundedGenuineCuspRealizableVia (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {R : Type*} [CommRing R] (ι : R →+* ℂ)
    (Φ : HeckeEigensystem F R) : Prop :=
  IsArithBoundedGenuineCuspRealizable F pins ψ (Φ.map ι)

def boundedGenuineCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ =>
    @IsArithBoundedGenuineCuspRealizable F _i1 _i2 (pins F)
      (@NumberField.StandardAddChar.stdAddChar F _i1 _i2) Φ

variable {F}

theorem boundedGenuineCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (boundedGenuineCuspNotionOf pins).IsCusp F Φ ↔
      IsArithBoundedGenuineCuspRealizable F (pins F) (NumberField.StandardAddChar.stdAddChar F) Φ :=
  Iff.rfl

theorem isBoundedGenuineFn_iff (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsBoundedGenuineFn F pins ψ φ ↔
      Continuous φ ∧
        (∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
          ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C) ∧
        (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun α : F => whittakerCoefficient F pins ψ φ α g) :=
  Iff.rfl

theorem isBoundedGenuineCuspRealizable_iff (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ) :
    IsBoundedGenuineCuspRealizable F pins ψ Φ ↔
      ∃ R : SmoothCuspRealizationAt F pins Φ,
        Continuous R.toFun ∧
          (∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
            ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
              ‖R.toFun g‖ ≤ C) ∧
          (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ R.toFun α g) ∧
          ∀ g : AdelicGL2 (𝓞 F) F,
            Summable (fun α : F => whittakerCoefficient F pins ψ R.toFun α g) :=
  Iff.rfl

theorem isBoundedGenuineFn_productionPinsOf_iff
    (D D' : Set (AdelicGL2 (𝓞 F) F))
    (U U' : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen gen' : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsBoundedGenuineFn F (productionPinsOf F D U gen B) ψ φ ↔
      IsBoundedGenuineFn F (productionPinsOf F D' U' gen' B) ψ φ :=
  Iff.rfl

namespace IsBoundedGenuineFn

variable {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}

theorem continuous (h : IsBoundedGenuineFn F pins ψ φ) : Continuous φ :=
  h.1

theorem isBoundedOnSiegelWindows (h : IsBoundedGenuineFn F pins ψ φ) :
    IsBoundedOnSiegelWindows F φ :=
  h.2.1

theorem exists_bound_on_window (h : IsBoundedGenuineFn F pins ψ φ) (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C :=
  h.2.1 c u d₁ d₂ T hc hd₁

theorem whittakerCoefficientIntegrable (h : IsBoundedGenuineFn F pins ψ φ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : WhittakerCoefficientIntegrable F pins ψ φ α g :=
  h.2.2.1 α g

theorem summable_whittakerCoefficient (h : IsBoundedGenuineFn F pins ψ φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun α : F => whittakerCoefficient F pins ψ φ α g) :=
  h.2.2.2 g

end IsBoundedGenuineFn

private theorem det_unipotentGL2 {A : Type*} [CommRing A] (x : A) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

theorem whittakerCoefficient_detTwist (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) α g
      = c (Matrix.GeneralLinearGroup.det g) * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, map_mul, det_unipotentGL2, one_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem IsBoundedGenuineFn.detTwist {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsBoundedGenuineFn F pins ψ φ)
    (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hc : Continuous fun g : AdelicGL2 (𝓞 F) F => c (Matrix.GeneralLinearGroup.det g))
    (hc₁ : ∀ u : (AdeleRing (𝓞 F) F)ˣ, ‖c u‖ ≤ 1) :
    IsBoundedGenuineFn F pins ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) := by
  obtain ⟨hφ, hb, hint, hsum⟩ := h
  refine ⟨hc.mul hφ, fun c' u d₁ d₂ T hc' hd₁ => ?_, fun α g => ?_, fun g => ?_⟩
  · obtain ⟨C, hC⟩ := hb c' u d₁ d₂ T hc' hd₁
    refine ⟨C, fun g hg => ?_⟩
    calc ‖c (Matrix.GeneralLinearGroup.det g) * φ g‖
          = ‖c (Matrix.GeneralLinearGroup.det g)‖ * ‖φ g‖ := norm_mul _ _
      _ ≤ ‖φ g‖ := mul_le_of_le_one_left (norm_nonneg _) (hc₁ _)
      _ ≤ C := hC g hg
  · have hi := hint α g
    letI := pins.nS
    change MeasureTheory.Integrable _ _ at hi ⊢
    simp only [map_mul, det_unipotentGL2, one_mul, mul_assoc]
    exact hi.const_mul _
  · have key : (fun α : F => whittakerCoefficient F pins ψ
        (fun g => c (Matrix.GeneralLinearGroup.det g) * φ g) α g)
        = fun α : F => c (Matrix.GeneralLinearGroup.det g) * whittakerCoefficient F pins ψ φ α g :=
      funext fun α => whittakerCoefficient_detTwist pins ψ c φ α g
    rw [key]
    exact (hsum g).mul_left _

namespace IsBoundedGenuineCuspRealizationAt

variable {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
  {R : SmoothCuspRealizationAt F pins Φ}

theorem isBoundedGenuineFn (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsBoundedGenuineFn F pins ψ R.toFun :=
  h

theorem isGenuineCuspRealizationAt (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsGenuineCuspRealizationAt F pins Φ R :=
  h.1

theorem isBoundedOnSiegelWindows (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) :
    IsBoundedOnSiegelWindows F R.toFun :=
  h.2.1

theorem exists_bound_on_window (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖R.toFun g‖ ≤ C :=
  h.2.1 c u d₁ d₂ T hc hd₁

theorem whittakerCoefficientIntegrable (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : WhittakerCoefficientIntegrable F pins ψ R.toFun α g :=
  h.2.2.1 α g

theorem summable_whittakerCoefficient (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun α : F => whittakerCoefficient F pins ψ R.toFun α g) :=
  h.2.2.2 g

theorem of_toFun_eq {Φ' : HeckeEigensystem F ℂ} {R' : SmoothCuspRealizationAt F pins Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (he : R'.toFun = R.toFun) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact h

theorem detTwist {Φ' : HeckeEigensystem F ℂ} {R' : SmoothCuspRealizationAt F pins Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F pins ψ Φ R) (c : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hc : Continuous fun g : AdelicGL2 (𝓞 F) F => c (Matrix.GeneralLinearGroup.det g))
    (hc₁ : ∀ u : (AdeleRing (𝓞 F) F)ˣ, ‖c u‖ ≤ 1)
    (he : R'.toFun = fun g => c (Matrix.GeneralLinearGroup.det g) * R.toFun g) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact IsBoundedGenuineFn.detTwist h c hc hc₁

end IsBoundedGenuineCuspRealizationAt

theorem isBoundedGenuineCuspRealizationAt_of_isBoundedGenuineFn {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Φ) (h : IsBoundedGenuineFn F pins ψ R.toFun) :
    IsBoundedGenuineCuspRealizationAt F pins ψ Φ R :=
  h

theorem IsBoundedGenuineCuspRealizationAt.of_toFun_eq_productionPinsOf
    {D D' : Set (AdelicGL2 (𝓞 F) F)} {U U' : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen gen' : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
    {B : Set (AdeleRing (𝓞 F) F)} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {Φ Φ' : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F (productionPinsOf F D U gen B) Φ}
    {R' : SmoothCuspRealizationAt F (productionPinsOf F D' U' gen' B) Φ'}
    (h : IsBoundedGenuineCuspRealizationAt F (productionPinsOf F D U gen B) ψ Φ R)
    (he : R'.toFun = R.toFun) :
    IsBoundedGenuineCuspRealizationAt F (productionPinsOf F D' U' gen' B) ψ Φ' R' := by
  unfold IsBoundedGenuineCuspRealizationAt
  rw [he]
  exact (isBoundedGenuineFn_productionPinsOf_iff D D' U U' gen gen' B ψ R.toFun).mp h

theorem IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (h : IsBoundedGenuineCuspRealizable F pins ψ Φ) : IsGenuineCuspRealizable F pins Φ :=
  h.imp fun _ hR => hR.isGenuineCuspRealizationAt

theorem IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable {pins : CarrierPins F}
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {Φ : HeckeEigensystem F ℂ}
    (h : IsArithBoundedGenuineCuspRealizable F pins ψ Φ) :
    IsArithGenuineCuspRealizable F pins Φ :=
  IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable h

theorem IsArithBoundedGenuineCuspRealizableVia.isArithGenuineCuspRealizableVia
    {pins : CarrierPins F} {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {R : Type*} [CommRing R]
    {ι : R →+* ℂ} {Φ : HeckeEigensystem F R}
    (h : IsArithBoundedGenuineCuspRealizableVia F pins ψ ι Φ) :
    IsArithGenuineCuspRealizableVia F pins ι Φ :=
  IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable h

theorem boundedGenuineCuspNotionOf_isCusp_imp
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (h : (boundedGenuineCuspNotionOf pins).IsCusp F Φ) :
    (genuineCuspNotionOf pins).IsCusp F Φ :=
  IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable h

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @IsBoundedOnSiegelWindows
#check @IsBoundedGenuineFn
#check @IsBoundedGenuineCuspRealizationAt
#check @IsBoundedGenuineCuspRealizable
#check @IsArithBoundedGenuineCuspRealizable
#check @IsArithBoundedGenuineCuspRealizableVia
#check @boundedGenuineCuspNotionOf
#check @boundedGenuineCuspNotionOf_isCusp_iff
#check @isBoundedGenuineFn_iff
#check @isBoundedGenuineCuspRealizable_iff
#check @isBoundedGenuineFn_productionPinsOf_iff
#check @IsBoundedGenuineFn.continuous
#check @IsBoundedGenuineFn.isBoundedOnSiegelWindows
#check @IsBoundedGenuineFn.exists_bound_on_window
#check @IsBoundedGenuineFn.whittakerCoefficientIntegrable
#check @IsBoundedGenuineFn.summable_whittakerCoefficient
#check @whittakerCoefficient_detTwist
#check @IsBoundedGenuineFn.detTwist
#check @IsBoundedGenuineCuspRealizationAt.isBoundedGenuineFn
#check @IsBoundedGenuineCuspRealizationAt.isGenuineCuspRealizationAt
#check @IsBoundedGenuineCuspRealizationAt.isBoundedOnSiegelWindows
#check @IsBoundedGenuineCuspRealizationAt.exists_bound_on_window
#check @IsBoundedGenuineCuspRealizationAt.whittakerCoefficientIntegrable
#check @IsBoundedGenuineCuspRealizationAt.summable_whittakerCoefficient
#check @IsBoundedGenuineCuspRealizationAt.of_toFun_eq
#check @IsBoundedGenuineCuspRealizationAt.detTwist
#check @isBoundedGenuineCuspRealizationAt_of_isBoundedGenuineFn
#check @IsBoundedGenuineCuspRealizationAt.of_toFun_eq_productionPinsOf
#check @IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable
#check @IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable
#check @IsArithBoundedGenuineCuspRealizableVia.isArithGenuineCuspRealizableVia
#check @boundedGenuineCuspNotionOf_isCusp_imp
#print axioms AutomorphicForm.boundedGenuineCuspNotionOf_isCusp_iff
#print axioms AutomorphicForm.isBoundedGenuineFn_iff
#print axioms AutomorphicForm.isBoundedGenuineCuspRealizable_iff
#print axioms AutomorphicForm.isBoundedGenuineFn_productionPinsOf_iff
#print axioms AutomorphicForm.IsBoundedGenuineFn.continuous
#print axioms AutomorphicForm.IsBoundedGenuineFn.isBoundedOnSiegelWindows
#print axioms AutomorphicForm.IsBoundedGenuineFn.exists_bound_on_window
#print axioms AutomorphicForm.IsBoundedGenuineFn.whittakerCoefficientIntegrable
#print axioms AutomorphicForm.IsBoundedGenuineFn.summable_whittakerCoefficient
#print axioms AutomorphicForm.whittakerCoefficient_detTwist
#print axioms AutomorphicForm.IsBoundedGenuineFn.detTwist
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.isBoundedGenuineFn
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.isGenuineCuspRealizationAt
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.isBoundedOnSiegelWindows
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.exists_bound_on_window
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.whittakerCoefficientIntegrable
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.summable_whittakerCoefficient
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.of_toFun_eq
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.detTwist
#print axioms AutomorphicForm.isBoundedGenuineCuspRealizationAt_of_isBoundedGenuineFn
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizationAt.of_toFun_eq_productionPinsOf
#print axioms AutomorphicForm.IsBoundedGenuineCuspRealizable.isGenuineCuspRealizable
#print axioms AutomorphicForm.IsArithBoundedGenuineCuspRealizable.isArithGenuineCuspRealizable
#print axioms AutomorphicForm.IsArithBoundedGenuineCuspRealizableVia.isArithGenuineCuspRealizableVia
#print axioms AutomorphicForm.boundedGenuineCuspNotionOf_isCusp_imp
end Battery


