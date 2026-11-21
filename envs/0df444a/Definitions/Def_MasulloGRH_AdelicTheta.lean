-- Prove2me | Definitions.Def_MasulloGRH_AdelicTheta
-- name    : MasulloGRH_AdelicTheta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:26:54.035484+00:00
-- url     : https://prove2.me/theorems/1e9a7fa4-fb2f-4183-9945-8df3269afb8d
-- title:
--   $\mathcal S(\mathbb A_F)$, the adelic Fourier transform and the global adelic $\theta$-function $\Phi_F(f)$
-- statement:
--   This file defines the objects of Tate's thesis on the adele ring of a number field $F$.
--
--   1. $\mathcal S(\mathbb A_F)$ is the **Schwartz–Bruhat space** of the additive group of the adele ring $\mathbb A_F$.
--   2. An adele is **integral** if its coordinate at every finite place $v$ lies in $\mathcal O_{F_v}$; the integral adeles are $\mathbb A_{F,S_\infty}\times\widehat{\mathcal O}_F$.
--   3. The **standard additive character** $\psi_{F,\mathrm{std}}=\psi_{\mathbb Q,\mathrm{std}}\circ\operatorname{Tr}_{F/\mathbb Q}$ of $\mathbb A_F$ is the continuous character that is trivial on $F$ and whose value on an integral adele $y$ is
--   $$\psi_{F,\mathrm{std}}(y)=\exp\Big(-2\pi i\sum_{w\mid\infty}\operatorname{Tr}_{F_w/\mathbb R}(y_w)\Big).$$
--   Every adele is the sum of an integral adele and an element of $F$, so this determines the character.
--   4. The **additive Tamagawa measure** $\nu$ is the Haar measure on $\mathbb A_F$ with $\nu(\mathbb A_F/F)=1$: a measurable fundamental domain for $F$ in $\mathbb A_F$ has measure $1$.
--   5. The **adelic Fourier transform** of a function $f$ on $\mathbb A_F$ is
--   $$\widehat f(y)=\int_{\mathbb A_F}f(x)\,\psi_{F,\mathrm{std}}(xy)\,d\nu(x).$$
--   6. The **global adelic $\theta$-function** of $f\in\mathcal S(\mathbb A_F)$ is
--   $$\Phi_F(f)(g)=\sum_{\xi\in F^\times}f(\xi g),\qquad g\in\mathrm{GL}_1(\mathbb A_F).$$
--   It is invariant under $F^\times$, hence a function on the idele class group $C_F$.
--   7. $\mathcal S_0(\mathbb A_F)=\ker\delta_0\cap\ker\widehat\delta_0$ is the subspace of the $f\in\mathcal S(\mathbb A_F)$ with $f(0)=0$ and $\widehat f(0)=0$.
--
--   The $\theta$-functions $\Phi_F(f)$ are the functions on $C_F$ whose Mellin transforms are Tate's global zeta integrals.
--
--   **Formalization Note** The character of item 3 is $\psi_{\mathbb Q,\mathrm{std}}(x)=e^{-2\pi i x_\infty}\prod_pe^{2\pi i\{x_p\}_p}$ composed with the trace; with it the Fourier transform at a real place is $\int f(x)e^{-2\pi ixy}dx$ and at $\mathbb Q_p$ it is $\int f(x)e^{2\pi i\{xy\}_p}dx$, as in Examples A.3.1.5–A.3.1.7. The character and the measure are selected by their characterizing properties. $\Phi_F(f)$ is defined as a function of the idele $g$; the sum is an unconditional sum.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Definition A.3.1.1 (p. 555); Examples A.3.1.5–A.3.1.9 (pp. 557–558); Definition 2.2.3.1 (pp. 81–82); Definition 2.2.4.4 (p. 91)

import Definitions.Def_MasulloGRH_SAdeles
import Definitions.Def_MasulloGRH_SchwartzBruhat

/-!
# Schwartz–Bruhat functions on the adeles, the adelic Fourier transform, global θ-functions

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026): Definition A.3.1.1
(p. 555), Examples A.3.1.5–A.3.1.9 (pp. 557–558), Definition 2.2.3.1 (pp. 81–82),
Definition 2.2.4.4 (p. 91).
-/

namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The Borel σ-algebra of the adele ring. -/
scoped instance adeleMeasurableSpace : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _

scoped instance adeleBorelSpace : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩

/-- The Schwartz–Bruhat space `S(𝔸_F)` of the additive group of the adele ring. -/
abbrev AdelicSchwartz : Type _ := SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))

variable {F}

/-- The value `f(x)` of `f ∈ S(𝔸_F)` at an adele `x`. -/
def AdelicSchwartz.eval (f : AdelicSchwartz F) (x : AdeleRing (𝓞 F) F) : ℂ :=
  f.toFun (Multiplicative.ofAdd x)

/-- An adele is integral if all its finite coordinates lie in the rings of integers `𝒪_{F_v}`;
the integral adeles are `𝔸_{F,S_∞} × \hat{𝒪}_F`. -/
def IsIntegralAdele (x : AdeleRing (𝓞 F) F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), x.2 v ∈ v.adicCompletionIntegers F

open Classical in
/-- The standard additive character `ψ_{F,std} = ψ_{ℚ,std} ∘ Tr_{F/ℚ}` of `𝔸_F` (Examples
A.3.1.8–A.3.1.9), with `ψ_{ℚ,std}(x) = e^{-2πi x_∞} ∏_p e^{2πi {x_p}_p}`.  It is trivial on `F`,
and on an integral adele `y` its value is `exp(-2πi ∑_{w | ∞} Tr_{F_w/ℝ}(y_w))`.  Every adele is
`y + ξ` with `y` integral and `ξ ∈ F`, and the value does not depend on the decomposition. -/
def stdAdelicCharacter (x : AdeleRing (𝓞 F) F) : ℂ :=
  if h : ∃ y : AdeleRing (𝓞 F) F, IsIntegralAdele y ∧
      ∃ ξ : F, x = y + algebraMap F (AdeleRing (𝓞 F) F) ξ then
    Complex.exp (-(2 * Real.pi * Complex.I) *
      ∑ w : InfinitePlace F,
        (w.mult : ℂ) * ((InfinitePlace.Completion.extensionEmbedding w (h.choose.1 w)).re : ℂ))
  else 1

open Classical in
/-- The additive Tamagawa measure `ν` on `𝔸_F` (Definition A.3.1.1): the Haar measure for which
`𝔸_F / F` has volume `1`, i.e. a measurable fundamental domain for `F` has measure `1`. -/
def tamagawaAdelic : Measure (AdeleRing (𝓞 F) F) :=
  if h : ∃ ν : Measure (AdeleRing (𝓞 F) F), ν.IsAddHaarMeasure ∧
      ∃ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D ∧
        (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) ∧
        ν D = 1 then
    h.choose
  else 0

/-- The adelic Fourier transform `\hat f(y) = ∫_{𝔸_F} f(x) ψ_{F,std}(x y) dν(x)` of a function on
the adeles, with respect to the standard additive character and the Tamagawa measure. -/
def adelicFourierFun (φ : AdeleRing (𝓞 F) F → ℂ) (y : AdeleRing (𝓞 F) F) : ℂ :=
  ∫ x, φ x * stdAdelicCharacter (x * y) ∂tamagawaAdelic

/-- The adelic Fourier transform `\hat f` of `f ∈ S(𝔸_F)`, as a function on the adeles. -/
def adelicFourier (f : AdelicSchwartz F) : AdeleRing (𝓞 F) F → ℂ :=
  adelicFourierFun f.eval

/-- The sum `∑_{ξ ∈ Fˣ} φ(ξ g)` of a function `φ` on the adeles over the `Fˣ`-orbit of an
idele `g`. -/
def adelicThetaFun (φ : AdeleRing (𝓞 F) F → ℂ) (g : IdeleGroup F) : ℂ :=
  ∑' ξ : Fˣ, φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))

/-- Definition 2.2.3.1: the global adelic θ-function `Φ_F(f)(g) = ∑_{ξ ∈ Fˣ} f(ξ g)` of
`f ∈ S(𝔸_F)`, as an `Fˣ`-invariant function of the idele `g`; it is a function on the idele class
group `C_F`. -/
def adelicTheta (f : AdelicSchwartz F) (g : IdeleGroup F) : ℂ := adelicThetaFun f.eval g

/-- Definition 2.2.4.4: `f ∈ S₀(𝔸_F) = ker δ₀ ∩ ker \hat δ₀`, i.e. `f(0) = 0` and `\hat f(0) = 0`. -/
def AdelicSchwartz.IsPolarFree (f : AdelicSchwartz F) : Prop :=
  f.eval 0 = 0 ∧ adelicFourier f 0 = 0

end

end MasulloGRH


