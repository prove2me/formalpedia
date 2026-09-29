-- Prove2me | Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
-- name    : AutomorphicForm_WeightedOrbitalRelation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c721e655-c14a-55e6-b1ce-700fedd129de
-- title:
--   Weighted and twisted weighted orbital integrals on GL(2)
-- statement:
--   For a normed field $F$ the local weight of $x \in \mathrm{GL}_2(F)$ is defined by [`AutomorphicForm.LocalWeight.weight`](../def/AutomorphicForm_WeightedOrbitalRelation.html#L17) as
--   $$\mathrm{weight}(x) = 2\log\frac{\max(\|x_{00}\|,\|x_{01}\|)\cdot\max(\|x_{10}\|,\|x_{11}\|)}{\|\det x\|},$$
--   the second factor in the numerator being [`NumberField.AdelicHeight.rowMaxNorm`](../def/NumberField_AdelicHeight.html#L18) of the underlying matrix, i.e. the maximum of the norms of the entries of the second row. At the identity matrix the value is $0$ (`weight_one`).
--
--   For a commutative topological ring $A$, a measure $\mu$ on $\mathrm{GL}_2(A)$ for the Borel $\sigma$-algebra, an arbitrary real-valued function $\mathrm{wt}$ on $\mathrm{GL}_2(A)$, an element $\gamma$, a measure $\tau$ on the centraliser of $\{\gamma\}$, a function $f \colon \mathrm{GL}_2(A) \to \mathbb{C}$ and a scalar $J \in \mathbb{C}$, the predicate `IsWeightedOrbitalIntegralOn` asserts that there is $s \colon \mathrm{GL}_2(A) \to \mathbb{R}$ satisfying `IsSectionFnOn` for $f$ at $\gamma$ with respect to $\tau$ — that is, $s \ge 0$, $s$ measurable with compact support, and $\int_{Z(\gamma)} s(tx)\,d\tau(t) = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$ — such that $J = \int f(x^{-1}\gamma x)\,\mathrm{wt}(x)\,s(x)\,d\mu(x)$. Thus the weighted integral over $Z(\gamma)\backslash \mathrm{GL}_2(A)$ is presented as a relation between $f$, $\mathrm{wt}$ and a value, using a cut-off function instead of a quotient measure. `IsTwistedWeightedOrbitalIntegralOn` is the $\sigma$-twisted analogue over $L \otimes_K A$ for a finite extension $L/K$ and $\sigma \in \mathrm{Aut}_K(L)$: the integrand is $\varphi(x^{-1}\delta\,\sigma(x))\,\mathrm{wt}(x)\,s(x)$, with $s$ a twisted section function relative to a measure $\tau'$ on the $\sigma$-twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$ of $\delta$.
--
--   Over a finite place $v$ of a number field $K$ and a finite extension $L/K$ of number fields, `semiLocalPlaceComponent` is the homomorphism $\mathrm{GL}_2(L \otimes_K K_v) \to \mathrm{GL}_2(L_w)$ obtained entrywise from the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ followed by evaluation at an extension $w$ of $v$, and `semiLocalWeight` is the finite sum $\sum_{w \mid v} \mathrm{weight}(x_w)$ of local weights of the components. The relations `IsWeightedOrbitalIntegral` and `IsTwistedWeightedOrbitalIntegral` instantiate the two general predicates at the normalised local Haar measure on $\mathrm{GL}_2(K_v)$ with weight $\mathrm{weight}$, respectively at the semi-local Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ with weight `semiLocalWeight`. Four lemmas record that the zero function has weighted orbital integral $0$, in the untwisted and twisted settings both in general and at a finite place.
--
--   **Relation to Mathlib.** Mathlib has no notion of (twisted) orbital integral or of weights on $\mathrm{GL}_2$; these predicates are the project's own, formulated with Mathlib's Borel $\sigma$-algebras, `MeasureTheory.Measure`, Haar measures and `Subgroup.centralizer`.
--
--   **Where it is used.** These are the non-invariant terms needed when comparing the trace formula for $\mathrm{GL}(2)$ over $K$ with its $\sigma$-twisted form over $L$, the local and semi-local weights being the place-by-place constituents of the global weight attached to the adelic height. They belong to the automorphic input of the modularity argument, where base change for $\mathrm{GL}(2)$ is used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WeightedOrbitalRelation.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm

namespace LocalWeight

variable {F : Type*} [NormedField F]

def weight (x : GL (Fin 2) F) : ℝ :=
  2 * Real.log
    (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) /
      ‖(x : Matrix (Fin 2) (Fin 2) F).det‖)

theorem weight_one : weight (1 : GL (Fin 2) F) = 0 := by
  simp [weight, AdelicHeight.rowMaxNorm]

end LocalWeight

section Untwisted

variable (A : Type) [CommRing A] [TopologicalSpace A]

def IsWeightedOrbitalIntegralOn (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (wt : GL (Fin 2) A → ℝ)
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (J : ℂ) : Prop :=
  letI := glBorelOf A
  ∃ s : GL (Fin 2) A → ℝ, IsSectionFnOn A γ τ f s ∧
    J = ∫ x, f (x⁻¹ * γ * x) * (wt x : ℂ) * (s x : ℂ) ∂μ

theorem isWeightedOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (wt : GL (Fin 2) A → ℝ)
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsWeightedOrbitalIntegralOn A μ wt γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFnOn_zero A γ τ, by simp⟩

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

def IsTwistedWeightedOrbitalIntegralOn (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (J' : ℂ) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  ∃ s : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ s ∧
    J' = ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (wt x : ℂ) * (s x : ℂ) ∂μ

theorem isTwistedWeightedOrbitalIntegralOn_zero
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (wt : GL (Fin 2) (L ⊗[K] A) → ℝ)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' (fun _ => 0) 0 :=
  ⟨fun _ => 0, isTwistedSectionFnOn_zero K L A σ δ τ', by simp⟩

end Twisted

section FinitePlaces

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

def semiLocalPlaceComponent (w : v.Extension (𝓞 L)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
      (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)

def semiLocalWeight (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : ℝ :=
  ∑ᶠ w : v.Extension (𝓞 L), LocalWeight.weight (semiLocalPlaceComponent K L v w x)

def IsWeightedOrbitalIntegral (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (J : ℂ) : Prop :=
  IsWeightedOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) LocalWeight.weight γ τ fv J

def IsTwistedWeightedOrbitalIntegral (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (J' : ℂ) : Prop :=
  IsTwistedWeightedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) (semiLocalWeight K L v)
    δ τ' φv J'

theorem isWeightedOrbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsWeightedOrbitalIntegral K v γ τ (fun _ => 0) 0 :=
  isWeightedOrbitalIntegralOn_zero _ _ _ γ τ

theorem isTwistedWeightedOrbitalIntegral_zero (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    IsTwistedWeightedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 0 :=
  isTwistedWeightedOrbitalIntegralOn_zero K L _ σ _ _ δ τ'

end FinitePlaces

end AutomorphicForm

end


