-- Prove2me | Definitions.Def_NumberField_AdelicFourier
-- name    : NumberField_AdelicFourier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/304ac17c-395d-548f-919b-926770c9109e
-- title:
--   Adelic Fourier integral and the Schwartz–Bruhat space
-- statement:
--   Two things are set up. First, for a commutative ring $A$ with a measurable-space structure, an additive character $\psi : A \to \mathbb{C}$ (a homomorphism from the additive group of $A$ to the multiplicative monoid of $\mathbb{C}$, no unitarity imposed), a measure $\mu$ on $A$ and $f : A \to \mathbb{C}$, the Fourier integral is defined by $\mathcal{F}_{\psi,\mu}f(w) = \int_A \psi(-(vw))\,f(v)\,d\mu(v)$, a Bochner integral, hence $0$ at any $w$ where the integrand fails to be integrable. The accompanying lemmas record: the defining formula; agreement with Mathlib's `Fourier.fourierIntegral` when $\psi$ is obtained from a circle-valued character by composing with the inclusion of the circle in $\mathbb{C}$; vanishing on $f = 0$; homogeneity in $f$; additivity at a point $w$ under integrability of the two kernel-weighted integrands there; the bound $\|\mathcal{F}_{\psi,\mu}f(w)\| \le \int \|\psi(-(vw))f(v)\|\,d\mu$; and, for a right-invariant $\mu$ on a ring with measurable addition, the translation rule $\mathcal{F}_{\psi,\mu}(f(\cdot + v_0))(w) = \psi(v_0 w)\,\mathcal{F}_{\psi,\mu}f(w)$, which pins down the sign convention.
--
--   Second, for a number field $F$, writing the adele ring `AdeleRing (𝓞 F) F` as a product of its infinite and finite parts, `pureTensorSet F` is the set of functions $x \mapsto g(x_\infty)h(x_f)$ in which $g$ is a Schwartz function on the mixed space $\prod_{\text{real}}\mathbb{R} \times \prod_{\text{complex}}\mathbb{C}$ of $F$ (the infinite component being transported there along the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace`) and $h$ is a locally constant, compactly supported function on the finite adeles. The Schwartz–Bruhat space `schwartzBruhat F` is the $\mathbb{C}$-submodule of all functions $\mathbb{A}_F \to \mathbb{C}$ spanned by this set. Helper statements give membership of pure tensors and of $0$, the inclusion of pure tensors in the span, and an induction principle over the span (pure tensors, zero, sums, scalar multiples).
--
--   **Relation to Mathlib.** `fourierIntegral` is a variant of Mathlib's `Fourier.fourierIntegral` with the circle-valued additive character replaced by a complex-valued one, the two agreeing under `Circle.coeHom.compAddChar`; the Schwartz–Bruhat space of an adele ring is the project's own notion, built from Mathlib's `SchwartzMap`, `IsLocallyConstant` and `HasCompactSupport`.
--
--   **Where it is used.** This module provides the adelic Fourier-analytic vocabulary — characters, Fourier integrals and the space of test functions on $\mathbb{A}_F$ — on which the automorphic side of the argument is built.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_AdelicFourier.lean

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace NumberField.AdelicFourier

section Fourier

variable {A : Type*} [CommRing A] [MeasurableSpace A]

def fourierIntegral (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) : ℂ :=
  ∫ v, ψ (-(v * w)) * f v ∂μ

theorem fourierIntegral_def (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) :
    fourierIntegral ψ μ f w = ∫ v, ψ (-(v * w)) * f v ∂μ :=
  rfl

theorem fourierIntegral_compAddChar (e : AddChar A Circle) (μ : Measure A) (f : A → ℂ) :
    fourierIntegral (Circle.coeHom.compAddChar e) μ f = Fourier.fourierIntegral e μ f := by
  funext w
  simp only [fourierIntegral, Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul]
  rfl

theorem fourierIntegral_zero (ψ : AddChar A ℂ) (μ : Measure A) :
    fourierIntegral ψ μ 0 = 0 := by
  funext w
  simp only [fourierIntegral, Pi.zero_apply, mul_zero, integral_zero]

theorem fourierIntegral_smul (ψ : AddChar A ℂ) (μ : Measure A) (c : ℂ) (f : A → ℂ) :
    fourierIntegral ψ μ (c • f) = c • fourierIntegral ψ μ f := by
  funext w
  simp only [fourierIntegral, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1 with v
  ring

theorem fourierIntegral_add (ψ : AddChar A ℂ) (μ : Measure A) {f g : A → ℂ} (w : A)
    (hf : Integrable (fun v => ψ (-(v * w)) * f v) μ)
    (hg : Integrable (fun v => ψ (-(v * w)) * g v) μ) :
    fourierIntegral ψ μ (f + g) w = fourierIntegral ψ μ f w + fourierIntegral ψ μ g w := by
  simp only [fourierIntegral, Pi.add_apply, mul_add]
  exact integral_add hf hg

theorem norm_fourierIntegral_le_integral_norm (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ)
    (w : A) : ‖fourierIntegral ψ μ f w‖ ≤ ∫ v, ‖ψ (-(v * w)) * f v‖ ∂μ :=
  norm_integral_le_integral_norm _

theorem fourierIntegral_comp_add_right [MeasurableAdd A] (ψ : AddChar A ℂ) (μ : Measure A)
    [μ.IsAddRightInvariant] (f : A → ℂ) (v₀ : A) :
    fourierIntegral ψ μ (f ∘ fun v => v + v₀) = fun w => ψ (v₀ * w) * fourierIntegral ψ μ f w := by
  funext w
  simp only [fourierIntegral, Function.comp_apply]
  have h : (fun v => ψ (-(v * w)) * f (v + v₀))
      = fun v => (fun u => ψ (-((u - v₀) * w)) * f u) (v + v₀) := by
    funext v
    simp only [add_sub_cancel_right]
  rw [h, integral_add_right_eq_self (fun u => ψ (-((u - v₀) * w)) * f u) v₀, ← integral_const_mul]
  congr 1 with u
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end Fourier

section SchwartzBruhat

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in

def pureTensorSet : Set (AdeleRing (𝓞 F) F → ℂ) :=
  {f | ∃ (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ),
      IsLocallyConstant h ∧ HasCompactSupport h ∧
      f = fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2}

def schwartzBruhat : Submodule ℂ (AdeleRing (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (pureTensorSet F)

variable {F}

open scoped Classical in
theorem tensor_mem_pureTensorSet (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : AdeleRing (𝓞 F) F => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2)
      ∈ pureTensorSet F :=
  ⟨g, h, hlc, hcs, rfl⟩

theorem mem_schwartzBruhat_of_mem_pureTensorSet {f : AdeleRing (𝓞 F) F → ℂ}
    (hf : f ∈ pureTensorSet F) : f ∈ schwartzBruhat F :=
  Submodule.subset_span hf

theorem zero_mem_pureTensorSet : (0 : AdeleRing (𝓞 F) F → ℂ) ∈ pureTensorSet F :=
  ⟨0, 0, IsLocallyConstant.const 0, HasCompactSupport.zero, by funext x; simp⟩

theorem zero_mem_schwartzBruhat : (0 : AdeleRing (𝓞 F) F → ℂ) ∈ schwartzBruhat F :=
  Submodule.zero_mem _

theorem schwartzBruhat_induction {p : (f : AdeleRing (𝓞 F) F → ℂ) → f ∈ schwartzBruhat F → Prop}
    (tensor : ∀ (f) (hf : f ∈ pureTensorSet F), p f (mem_schwartzBruhat_of_mem_pureTensorSet hf))
    (zero : p 0 zero_mem_schwartzBruhat)
    (add : ∀ f g (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F),
      p f hf → p g hg → p (f + g) (Submodule.add_mem _ hf hg))
    (smul : ∀ (c : ℂ) f (hf : f ∈ schwartzBruhat F), p f hf → p (c • f) (Submodule.smul_mem _ c hf))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) : p f hf :=
  Submodule.span_induction tensor zero add smul hf

end SchwartzBruhat

end NumberField.AdelicFourier

end


