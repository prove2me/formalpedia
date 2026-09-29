-- Prove2me | Definitions.Def_AutomorphicForm_GodementSection
-- name    : AutomorphicForm_GodementSection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/454e6e82-1fb3-5c7f-a304-6c7de95b5606
-- title:
--   Two-variable adelic Schwartz–Bruhat space and Godement sections
-- statement:
--   For a number field $F$, `pureTensorSet2` is the set of functions $\Phi$ on $\mathbb{A}_F^2$ (modelled as `Fin 2 → AdeleRing (𝓞 F) F`) of the form $\Phi(x)=g(x_\infty)\,h(x_f)$, where $g$ is a Schwartz function on the pair of archimedean components, transported to the mixed space of $F$ by `InfiniteAdeleRing.ringEquiv_mixedSpace`, and $h$ is a locally constant, compactly supported function of the pair of finite-adelic components; `schwartzBruhat2` is the $\mathbb{C}$-span of this set, and `schwartzBruhat2_induction` records the resulting induction principle (pure tensors, zero, sums, scalar multiples), with `tensor_mem_pureTensorSet2`, `mem_schwartzBruhat2_of_mem_pureTensorSet2` and `zero_mem_schwartzBruhat2` as the elementary membership lemmas. Given a measure $\mu_1$ on $\mathbb{A}_F$, `pairHaar` is the product measure $\mu_1\times\mu_1$; given an additive character $\psi$ of $\mathbb{A}_F$ with values in $\mathbb{C}$, `pairChar` is $v\mapsto\psi(v_0+v_1)$ (`pairChar_apply`). Then `fourierTransform2` is the project's ring-theoretic Fourier integral of $\Phi$ against `pairChar` $\psi$ and `pairHaar`, i.e. $\widehat\Phi(w)=\int_{\mathbb{A}_F^2}\psi(-(v_0w_0+v_1w_1))\,\Phi(v)\,d(\mu_1\times\mu_1)(v)$, and `reflectPair` is $x\mapsto\widehat\Phi(x_1,-x_0)$, the composite of $\widehat\Phi$ with the Weyl element $\begin{pmatrix}0&-1\\1&0\end{pmatrix}$.
--
--   On the group side, `bottomRowVec` sends $g\in\mathrm{GL}_2(\mathbb{A}_F)$ and $t\in\mathbb{A}_F$ to the vector $j\mapsto t\,g_{1j}$, i.e. $(0,t)g$. For characters $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$, a homomorphism $\alpha:\mathbb{A}_F^\times\to\mathbb{R}^\times$ with $\alpha(x)>0$ for all $x$, a measure $\nu_0$ on the ideles and $s\in\mathbb{C}$, `godementSection` is the function
--   $$g\mapsto \mu(\det g)\,\alpha(\det g)^{s+1/2}\,\int_{\mathbb{A}_F^\times}\Phi\big((0,t)g\big)\,(\mu\nu^{-1})(t)\,\|t\|^{2s+1}\,d\nu_0(t),$$
--   where the power of $\alpha$ is the complex power `cpowChar` and the integral is the project's Tate zeta integral [`NumberField.TateGlobal.zetaIntegral`](../def/NumberField_TateGlobalZeta.html#L27) with $\|\cdot\|$ the idele norm given by the module of the adelic Haar measure. No integrability or convergence hypothesis is imposed: $\Phi$ is an arbitrary function on $\mathbb{A}_F^2$, and the Bochner integral returns $0$ where its integrand fails to be integrable.
--
--   **Relation to Mathlib.** Mathlib has no adelic Schwartz–Bruhat space, Tate zeta integral or Godement section; these are the project's own, the two-variable analogues of its one-variable `pureTensorSet` and `schwartzBruhat`. The archimedean factor is Mathlib's `SchwartzMap` on the mixed space, and the Fourier integral used is the project's variant of `Fourier.fourierIntegral` for a commutative ring with a $\mathbb{C}$-valued additive character.
--
--   **Where it is used.** These definitions set up the adelic input for the $\mathrm{GL}_2$ Eisenstein/zeta-integral theory: the Godement section attached to a Schwartz–Bruhat function on $\mathbb{A}_F^2$ is the building block of the adelic Eisenstein series, and the two-variable Fourier transform together with its Weyl reflection `reflectPair` is what the functional equation of such a series compares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GodementSection.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_EtaFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace NumberField.AdelicFourier

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in

def pureTensorSet2 : Set ((Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :=
  {Φ | ∃ (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      IsLocallyConstant h ∧ HasCompactSupport h ∧
      Φ = fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2)}

def schwartzBruhat2 : Submodule ℂ ((Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :=
  Submodule.span ℂ (pureTensorSet2 F)

variable {F}

def pairHaar [MeasurableSpace (AdeleRing (𝓞 F) F)] (μ₁ : Measure (AdeleRing (𝓞 F) F)) :
    Measure (Fin 2 → AdeleRing (𝓞 F) F) :=
  Measure.pi fun _ : Fin 2 => μ₁

def pairChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : AddChar (Fin 2 → AdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom
    (Pi.evalAddMonoidHom (fun _ : Fin 2 => AdeleRing (𝓞 F) F) 0
      + Pi.evalAddMonoidHom (fun _ : Fin 2 => AdeleRing (𝓞 F) F) 1)

theorem pairChar_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : Fin 2 → AdeleRing (𝓞 F) F) :
    pairChar ψ v = ψ (v 0 + v 1) := rfl

def fourierTransform2 [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :
    (Fin 2 → AdeleRing (𝓞 F) F) → ℂ :=
  fourierIntegral (pairChar ψ) (pairHaar μ₁) Φ

def reflectPair [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (x : Fin 2 → AdeleRing (𝓞 F) F) : ℂ :=
  fourierTransform2 ψ μ₁ Φ ![x 1, -x 0]

open scoped Classical in
theorem tensor_mem_pureTensorSet2 (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
    (h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2))
      ∈ pureTensorSet2 F :=
  ⟨g, h, hlc, hcs, rfl⟩

theorem mem_schwartzBruhat2_of_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) : Φ ∈ schwartzBruhat2 F :=
  Submodule.subset_span hΦ

theorem zero_mem_schwartzBruhat2 : (0 : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) ∈ schwartzBruhat2 F :=
  Submodule.zero_mem _

theorem schwartzBruhat2_induction
    {p : (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) → Φ ∈ schwartzBruhat2 F → Prop}
    (tensor : ∀ (Φ) (hΦ : Φ ∈ pureTensorSet2 F), p Φ (mem_schwartzBruhat2_of_mem_pureTensorSet2 hΦ))
    (zero : p 0 zero_mem_schwartzBruhat2)
    (add : ∀ Φ Ψ (hΦ : Φ ∈ schwartzBruhat2 F) (hΨ : Ψ ∈ schwartzBruhat2 F),
      p Φ hΦ → p Ψ hΨ → p (Φ + Ψ) (Submodule.add_mem _ hΦ hΨ))
    (smul : ∀ (c : ℂ) Φ (hΦ : Φ ∈ schwartzBruhat2 F), p Φ hΦ → p (c • Φ) (Submodule.smul_mem _ c hΦ))
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) : p Φ hΦ :=
  Submodule.span_induction tensor zero add smul hΦ

end NumberField.AdelicFourier

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def bottomRowVec (g : AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) : Fin 2 → AdeleRing (𝓞 F) F :=
  fun j => t * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 j

def godementSection {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    * NumberField.TateGlobal.zetaIntegral ν₀ (fun t => Φ (bottomRowVec F g t)) (μ * ν⁻¹) (2 * s + 1)

end AutomorphicForm

end


