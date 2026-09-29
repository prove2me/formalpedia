-- Prove2me | Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
-- name    : AutomorphicForm_TranslateSpanOccurrence
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a4206f40-31a8-5590-ad55-b3b8894429a0
-- title:
--   Mean-square translate span; archimedean occurrence for eigensystems
-- statement:
--   Over a number field $F$ three predicates are introduced, all phrased for functions on $\mathrm{GL}_2$ of the adeles of $F$ and for complex Hecke eigensystems over $F$.
--
--   First, `IsInTranslateSpanOn F D φ φ'`, for a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ and $φ, φ' : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$: for every $\varepsilon > 0$ in $[0,\infty]$ there are a finite set $s$ of group elements and a coefficient function $l$ on the group with $\int_D \lVert φ'(y) - \sum_{h \in s} l(h)\,φ(yh)\rVert^2 \, dy < \varepsilon$, the integral being a lower Lebesgue integral against the adelic Haar measure on $\mathrm{GL}_2$. Thus $φ'$ lies in the mean-square closure on $D$ of the span of the right translates of $φ$. The accompanying lemmas record that $φ$ lies in its own translate span and that equal functions are so related.
--
--   Second, writing $\mathrm{pins}(D)$ for the production pins with domain $D$, level groups $\mathrm{levelOne}(N)$ intersected with the finite adelic subgroup, Hecke generators $\mathrm{heckeGen}(v)$ and the adelic box, `ArchOccursInClassOf F D Θ P` asserts the existence of an eigensystem $Θ'$ with $Θ'$ and $Θ$ agreeing away from a finite set of finite places — equality of both the $a$- and the $b$-tables off that set — together with a smooth cuspidal realisation $R'$ at $\mathrm{pins}(D)$ of the raw central rescaling of $Θ'$ (the $b$-table divided by the ideal norms) which is continuous and whose underlying function satisfies $P$. Third, `ArchOccursInSpanOf F D Θ R P` strengthens this by requiring in addition that the function of $R'$ lie in the mean-square translate span on $D$ of the function of a given realisation $R$ attached to $Θ$ itself.
--
--   The remaining declarations are the bookkeeping of these notions: reflexivity, symmetry and transitivity of agreement away from a finite set; monotonicity in $P$ and splitting of conjunctions; invariance of `ArchOccursInClassOf` under agreement away from a finite set; extraction of a continuous function, or of mere continuous cuspidal realisability, from an occurrence statement; and the passage from `ArchOccursInSpanOf` to `ArchOccursInClassOf`.
--
--   **Relation to Mathlib.** Mathlib has no adelic automorphic forms on $\mathrm{GL}_2$ or Hecke eigensystems; these predicates are the project's own, built on its adelic Haar measure, Siegel-type domains and realisation structures. Only the measure-theoretic integral and the norm notation are taken from Mathlib.
--
--   **Where it is used.** These predicates are the form in which archimedean conditions — a prescribed $\mathrm{SO}(2)$-type at a real place, or holomorphy of the normalised archimedean descent — are attached to a Hecke eigensystem up to agreement away from finitely many finite places, so that such conditions can be transported along base change and compared without a theory of local components. The mean-square translate span is the quantitative shape in which strong multiplicity one is used on the Siegel domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TranslateSpanOccurrence.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsInTranslateSpanOn (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
      ∫⁻ y in D, (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε

variable {F}

theorem isInTranslateSpanOn_iff (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) :
    IsInTranslateSpanOn F D φ φ' ↔
      ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
          ∫⁻ y in D, (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε := Iff.rfl

theorem isInTranslateSpanOn_self (D : Set (AdelicGL2 (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsInTranslateSpanOn F D φ φ := by
  intro ε hε
  refine ⟨{1}, fun _ => 1, ?_⟩
  have h0 : (fun y : AdelicGL2 (𝓞 F) F =>
      ((‖φ y - ∑ h ∈ ({1} : Finset (AdelicGL2 (𝓞 F) F)), (1 : ℂ) * φ (y * h)‖₊ : ℝ≥0∞) ^ 2))
        = fun _ => 0 := by
    funext y
    simp
  rw [h0, lintegral_zero]
  exact hε

theorem IsInTranslateSpanOn.of_eq {D : Set (AdelicGL2 (𝓞 F) F)} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (h : φ = φ') : IsInTranslateSpanOn F D φ φ' := by
  subst h; exact isInTranslateSpanOn_self D φ

namespace TranslateSpanOccurrence

theorem agrees_refl (Θ : HeckeEigensystem F ℂ) : Θ.AgreesAwayFromFinite Θ :=
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩

theorem agrees_symm {Θ Θ' : HeckeEigensystem F ℂ} (h : Θ.AgreesAwayFromFinite Θ') :
    Θ'.AgreesAwayFromFinite Θ := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1.symm, (hS v hv).2.symm⟩⟩

theorem agrees_trans {Θ Θ' Θ'' : HeckeEigensystem F ℂ} (h : Θ.AgreesAwayFromFinite Θ')
    (h' : Θ'.AgreesAwayFromFinite Θ'') : Θ.AgreesAwayFromFinite Θ'' := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨S', hS'⟩ := h'
  refine ⟨S ∪ S', fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact ⟨(hS v hv.1).1.trans (hS' v hv.2).1, (hS v hv.1).2.trans (hS' v hv.2).2⟩

end TranslateSpanOccurrence

open TranslateSpanOccurrence

variable (F)

def ArchOccursInClassOf (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) : Prop :=
  ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
    ∃ R' : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral,
      IsGenuineCuspRealizationAt F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Θ'.toRawCentral R' ∧
      P R'.toFun

variable {F}

theorem archOccursInClassOf_of_realization {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral R)
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (hP : P R.toFun) :
    ArchOccursInClassOf F D Θ P :=
  ⟨Θ, agrees_refl Θ, R, hR, hP⟩

theorem archOccursInClassOf_of_realization_of_agrees {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ Θ' : HeckeEigensystem F ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral R')
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (hP : P R'.toFun) :
    ArchOccursInClassOf F D Θ P :=
  ⟨Θ', hΘ', R', hR', hP⟩

theorem ArchOccursInClassOf.mono {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ P)
    (hPQ : ∀ φ, P φ → Q φ) : ArchOccursInClassOf F D Θ Q := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hPQ _ hP⟩

theorem ArchOccursInClassOf.and_left {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ (fun φ => P φ ∧ Q φ)) :
    ArchOccursInClassOf F D Θ P :=
  h.mono fun _ hφ => hφ.1

theorem ArchOccursInClassOf.and_right {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ (fun φ => P φ ∧ Q φ)) :
    ArchOccursInClassOf F D Θ Q :=
  h.mono fun _ hφ => hφ.2

theorem ArchOccursInClassOf.of_agrees {D : Set (AdelicGL2 (𝓞 F) F)} {Θ₁ Θ₂ : HeckeEigensystem F ℂ}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ₁ P)
    (h₁₂ : Θ₁.AgreesAwayFromFinite Θ₂) : ArchOccursInClassOf F D Θ₂ P := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', agrees_trans hΘ' h₁₂, R', hR', hP⟩

theorem archOccursInClassOf_iff_of_agrees {D : Set (AdelicGL2 (𝓞 F) F)} {Θ₁ Θ₂ : HeckeEigensystem F ℂ}
    (h₁₂ : Θ₁.AgreesAwayFromFinite Θ₂) (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) :
    ArchOccursInClassOf F D Θ₁ P ↔ ArchOccursInClassOf F D Θ₂ P :=
  ⟨fun h => h.of_agrees h₁₂, fun h => h.of_agrees (agrees_symm h₁₂)⟩

theorem ArchOccursInClassOf.exists_continuous {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInClassOf F D Θ P) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
      ∃ φ' : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ' ∧ P φ' := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', hΘ', R'.toFun, hR', hP⟩

theorem ArchOccursInClassOf.isArithGenuineCuspRealizable {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ : HeckeEigensystem F ℂ} {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop}
    (h : ArchOccursInClassOf F D Θ P) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ' := by
  obtain ⟨Θ', hΘ', R', hR', -⟩ := h
  exact ⟨Θ', hΘ', R', hR'⟩

theorem archOccursInClassOf_true_of_isArithGenuineCuspRealizable {D : Set (AdelicGL2 (𝓞 F) F)}
    {Θ Θ' : HeckeEigensystem F ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (h : IsArithGenuineCuspRealizable F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ') :
    ArchOccursInClassOf F D Θ (fun _ => True) := by
  obtain ⟨R', hR'⟩ := h
  exact ⟨Θ', hΘ', R', hR', trivial⟩

variable (F)

def ArchOccursInSpanOf (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) : Prop :=
  ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
    ∃ R' : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral,
      IsGenuineCuspRealizationAt F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Θ'.toRawCentral R' ∧
      IsInTranslateSpanOn F D R.toFun R'.toFun ∧ P R'.toFun

variable {F}

theorem archOccursInSpanOf_self {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral R)
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (hP : P R.toFun) :
    ArchOccursInSpanOf F D Θ R P :=
  ⟨Θ, agrees_refl Θ, R, hR, isInTranslateSpanOn_self D R.toFun, hP⟩

theorem ArchOccursInSpanOf.mono {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral}
    {P Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInSpanOf F D Θ R P)
    (hPQ : ∀ φ, P φ → Q φ) : ArchOccursInSpanOf F D Θ R Q := by
  obtain ⟨Θ', hΘ', R', hR', hspan, hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hspan, hPQ _ hP⟩

theorem ArchOccursInSpanOf.agrees {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInSpanOf F D Θ R P) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
      ∃ φ' : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ' ∧ IsInTranslateSpanOn F D R.toFun φ' ∧ P φ' := by
  obtain ⟨Θ', hΘ', R', hR', hspan, hP⟩ := h
  exact ⟨Θ', hΘ', R'.toFun, hR', hspan, hP⟩

theorem ArchOccursInSpanOf.archOccursInClassOf {D : Set (AdelicGL2 (𝓞 F) F)} {Θ : HeckeEigensystem F ℂ}
    {R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral}
    {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop} (h : ArchOccursInSpanOf F D Θ R P) :
    ArchOccursInClassOf F D Θ P := by
  obtain ⟨Θ', hΘ', R', hR', -, hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hP⟩

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @IsInTranslateSpanOn
#check @ArchOccursInClassOf
#check @ArchOccursInSpanOf
#print axioms AutomorphicForm.isInTranslateSpanOn_self
#print axioms AutomorphicForm.TranslateSpanOccurrence.agrees_trans
#print axioms AutomorphicForm.archOccursInClassOf_of_realization
#print axioms AutomorphicForm.archOccursInClassOf_iff_of_agrees
#print axioms AutomorphicForm.ArchOccursInClassOf.isArithGenuineCuspRealizable
#print axioms AutomorphicForm.archOccursInSpanOf_self
#print axioms AutomorphicForm.ArchOccursInSpanOf.archOccursInClassOf
end Battery


