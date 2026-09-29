-- Prove2me | Definitions.Def_LanglandsTunnell_HeckeTate
-- name    : LanglandsTunnell_HeckeTate
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/94dc6029-616c-5bc8-a672-7e99f78e7920
-- title:
--   Hecke L-datum, root number and conductor of an idelic character
-- statement:
--   Fix a number field $F$ and a homomorphism $\chi\colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ on the units of the adele ring of $\mathcal{O}_F$ in $F$, together with archimedean parameters: complex numbers $u_R(w)$ and classes $a_R(w) \in \mathbb{Z}/2$ for each real place $w$, and complex numbers $u_C(w)$ and integers $k_C(w)$ for each complex place.
--
--   `heckeDatum` packages the degree-one L-datum of $\chi$ as a term of the project structure `LDatum` indexed by the height-one primes $v$ of $\mathcal{O}_F$: the norm attached to $v$ is the absolute norm of $v$; the Euler polynomial is $1 - \chi_v(\varpi_v)X$ when `IsUnramifiedCharAt χ v` holds, that is when the local component `localChar χ v` is trivial on those units of the completion at $v$ whose inverse is also integral, and is the constant $1$ otherwise, so that the ramified places contribute trivially; the dual polynomial is the same with $\chi_v(\varpi_v)^{-1}$. Here $\varpi_v$ is the idele `uniformizerIdele F v`, a chosen uniformiser at $v$ and $1$ elsewhere. The gamma multisets are $\{u_R(w) + \mathrm{signShift}(a_R(w))\}$ summed over the real places and $\{u_C(w) + |k_C(w)|/2\}$ over the complex places, with the dual multisets obtained by replacing $u$ by $-u$ and $k_C$ by $-k_C$. The abscissa is $1$, the centre $1/2$ and the degree $1$. No compatibility between $\chi$ at the infinite places and the parameters $u_R,a_R,u_C,k_C$ is imposed in the definition.
--
--   `heckeRootNumber` is the product of `signEpsilon (aR w)` (equal to $1$ if $a_R(w)=0$ and to $i$ otherwise) over the real places, of $i^{|k_C(w)|}$ over the complex places, and of the multipliable-product over all finite places of the standard local root numbers `stdRootNumberAt F v (localChar χ v)`, i.e. the local epsilon factors at $s = 1/2$ formed from the self-dual Haar measure, the standard local additive character and the standard local test function. `heckeConductor` is the real number given by the product over the finite places of $N(v)^{e_v}$ with the integer exponent $e_v = \mathrm{pinnedExp}$, the sum of the conductor exponent of $\chi_v$ and the level of the standard local additive character at $v$.
--
--   **Relation to Mathlib.** Mathlib has no notion of an L-datum, of local epsilon factors, or of the L-function of an idele class character; these are the project's own definitions, built over Mathlib's adele ring, height-one spectrum, `finprod` and (through `LDatum.archFactor`) the Gamma factors `Gammaℝ` and `Gammaℂ`.
--
--   **Where it is used.** These are the three ingredients of the GL(1) input to the converse-theorem route: the assertion that the datum of an idele class character is nice, with the stated root number and conductor, is Tate's analytic continuation and functional equation for Hecke L-functions in the shape required by the converse theorem used for the Langlands–Tunnell theorem, which in turn supplies the modularity of the mod-$3$ representation in the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_HeckeTate.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain LanglandsTunnell Polynomial
open NumberField.TateGlobal LanglandsTunnell.TateLocal LanglandsTunnell.Converse

namespace LanglandsTunnell.HeckeTate

variable (F : Type) [Field F] [NumberField F]

open Classical in

def heckeDatum (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) :
    LDatum (HeightOneSpectrum (𝓞 F)) where
  norm := fun v => Ideal.absNorm v.asIdeal
  euler := fun v =>
    if IsUnramifiedCharAt χ v then C 1 - C ((χ (uniformizerIdele F v) : ℂˣ) : ℂ) * X else C 1
  dual := fun v =>
    if IsUnramifiedCharAt χ v then C 1 - C (((χ (uniformizerIdele F v))⁻¹ : ℂˣ) : ℂ) * X else C 1
  gammaR := (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).sum
    fun w => ({uR w.1 w.2 + signShift (aR w.1 w.2)} : Multiset ℂ)
  gammaC := (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).sum
    fun w => ({uC w.1 w.2 + ((kC w.1 w.2).natAbs : ℂ) / 2} : Multiset ℂ)
  gammaRDual := (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).sum
    fun w => ({-uR w.1 w.2 + signShift (aR w.1 w.2)} : Multiset ℂ)
  gammaCDual := (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).sum
    fun w => ({-uC w.1 w.2 + ((-kC w.1 w.2).natAbs : ℂ) / 2} : Multiset ℂ)
  abscissa := 1
  center := 1 / 2
  degree := 1

open Classical in

def heckeRootNumber (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) : ℂ :=
  ((Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).prod fun w => signEpsilon (aR w.1 w.2)) *
    ((Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).prod
      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), stdRootNumberAt F v (localChar χ v)

def heckeConductor (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ) ^ (pinnedExp F χ v)

end LanglandsTunnell.HeckeTate

end


