-- Prove2me | Definitions.Def_LanglandsTunnell_CubicLambda
-- name    : LanglandsTunnell_CubicLambda
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/d8951805-0b4a-5267-a737-54007d705d32
-- title:
--   Resolvent data for cubic fields and their lambda constants
-- statement:
--   Fix a number field $K$ with the structure of an extension of $\mathbb{Q}$ at the level of rings of integers ($\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K$ integral). Two helpers set the notation: `eulerCoeff F η v` is the value $\eta(\varpi_v)$ of an idele-class character $\eta$ on the idele `uniformizerIdele F v` concentrated at the finite place $v$ when $\eta$ is unramified at $v$ (in the sense of `IsUnramifiedCharAt`), and $0$ otherwise; `zetaEulerPoly F p` is the Dedekind Euler factor of $F$ at a rational prime $p$, namely the `inducedEulerPoly` of the constant function $1$, i.e. $\prod_{\mathfrak{P}\mid p}\bigl(1-X^{f(\mathfrak{P}/p)}\bigr)$ as a polynomial in $X$ (to be read as $X=p^{-s}$). Also `resolventSignBit L` is $0\in\mathbb{Z}/2$ when $L$ is totally real and $1$ otherwise.
--
--   The inductive type `ResolventDatum K` packages a factorisation of $\zeta_K$ into abelian pieces, in two shapes, each constructor carrying its defining identities as fields. The `s3` constructor supplies a field $L$ with $[L:\mathbb{Q}]=2$, finite-order Hecke characters $\omega$ of $\mathbb{Q}$ and $\theta$ of $L$ (idele-class, continuous, of finite order), together with: $\mathrm{zetaEulerPoly}\,L\,p=(1-X)(1-\mathrm{eulerCoeff}(\omega,p)X)$ and $\mathrm{zetaEulerPoly}\,K\,p=(1-X)\cdot\mathrm{inducedEulerPoly}$ of $\mathrm{eulerCoeff}(\theta,\cdot)$ at $p$, for every finite prime $p$; archimedean normalisations, via `IsArchCompAt`, pinning $\omega$ at each infinite place of $\mathbb{Q}$ to exponent $0$ and sign exponent $(\mathrm{resolventSignBit}\ L)$, and $\theta$ to the trivial component at each real and each complex place of $L$; and the signature relations $r_K=r_L+1$, $c_K=c_L$. The `cyclic` constructor supplies one finite-order Hecke character $\chi$ of $\mathbb{Q}$ with $\mathrm{zetaEulerPoly}\,K\,p=(1-X)(1-\mathrm{eulerCoeff}(\chi,p)X)(1-\mathrm{eulerCoeff}(\chi^2,p)X)$, trivial archimedean components, and $c_K=0$.
--
--   Attached to a datum, `lambdaAt` is the local constant at a rational prime $p$: in the `s3` case $\varepsilon_p(\omega)\cdot\prod_{u\mid p}\varepsilon_u(\theta)$, the product over the fibre `primeFibre ℚ L p` of standard local root numbers `stdRootNumberAt` of the local components of $\omega$ and $\theta$; in the `cyclic` case $\varepsilon_p(\chi)\,\varepsilon_p(\chi^2)$. Then `lambdaFin` redistributes these over the finite places $w$ of $K$: it is $1$ when $e(w/p)=f(w/p)=1$ for $p$ the prime below $w$, and `lambdaAt` at that $p$ otherwise. Finally `lambdaArch` is $1$ at real places of $K$ and $\mathrm{signEpsilon}\,1=i$ at complex places.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient objects used here (adele rings, `HeightOneSpectrum`, `InfinitePlace`, `ramificationIdx'` and `inertiaDeg'`), but has no notion of Hecke character of finite order, local root number or resolvent datum; those are the project's own.
--
--   **Where it is used.** These data encode the factorisation of the Dedekind zeta function of a cubic field into abelian $L$-functions, in the two shapes arising from a non-Galois cubic field with quadratic resolvent and from a cyclic cubic field, together with the local epsilon constants of the abelian pieces. The constants `lambdaFin` and `lambdaArch` are the pinned root-number and local data fed into the converse-theorem and Rankin–Selberg machinery for the Langlands–Tunnell step, which provides the modularity input for the mod-$3$ representation attached to a Frey curve. The existence of a resolvent datum for every cubic field is asserted as a separate statement and is not established here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicLambda.lean

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg
open LanglandsTunnell.Converse AutomorphicForm HeckeCharacter

namespace LanglandsTunnell.CubicLambda

open scoped Classical in

noncomputable def eulerCoeff (F : Type) [Field F] [NumberField F] (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if IsUnramifiedCharAt η v then ((η (uniformizerIdele F v) : ℂˣ) : ℂ) else 0

noncomputable def zetaEulerPoly (F : Type) [Field F] [NumberField F] [Algebra (𝓞 ℚ) (𝓞 F)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 F)] (p : HeightOneSpectrum (𝓞 ℚ)) : Polynomial ℂ :=
  inducedEulerPoly ℚ (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) p

noncomputable def resolventSignBit (L : Type) [Field L] [NumberField L] : ZMod 2 :=
  if nrComplexPlaces L = 0 then 0 else 1

inductive ResolventDatum (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] : Type 1

  | s3 (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
      (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (hL : Module.finrank ℚ L = 2)
      (hω : IsFiniteOrderHeckeChar ℚ ω) (hθ : IsFiniteOrderHeckeChar L θ)
      (eulerω : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly L p =
        (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ ω p) * Polynomial.X))
      (eulerθ : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly K p =
        (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ (eulerCoeff L θ) p)
      (archω : ∀ w : InfinitePlace ℚ, IsArchCompAt ℚ ω w 0 ((resolventSignBit L).val : ℤ))
      (archθR : ∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ))
      (archθC : ∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0)
      (sig : nrRealPlaces K = nrRealPlaces L + 1 ∧ nrComplexPlaces K = nrComplexPlaces L) :
      ResolventDatum K

  | cyclic (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsFiniteOrderHeckeChar ℚ χ)
      (eulerχ : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly K p =
        (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ χ p) * Polynomial.X) *
          (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ (χ ^ 2) p) * Polynomial.X))
      (archχ : ∀ w : InfinitePlace ℚ, IsArchCompAt ℚ χ w 0 (((0 : ZMod 2)).val : ℤ))
      (sig : nrComplexPlaces K = 0) :
      ResolventDatum K

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

noncomputable def lambdaAt : ResolventDatum K → HeightOneSpectrum (𝓞 ℚ) → ℂ
  | @ResolventDatum.s3 _ _ _ _ _ L iF iN iA iI ω θ _ _ _ _ _ _ _ _ _, p => by
      letI := iF
      letI := iN
      letI := iA
      letI := iI
      exact stdRootNumberAt ℚ p (localChar ω p) *
        ∏ᶠ u ∈ primeFibre ℚ L p, stdRootNumberAt L u (localChar θ u)
  | .cyclic χ _ _ _ _, p =>
      stdRootNumberAt ℚ p (localChar χ p) * stdRootNumberAt ℚ p (localChar (χ ^ 2) p)

noncomputable def lambdaFin (Λd : ResolventDatum K) (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal = 1 ∧
      (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = 1 then 1
  else lambdaAt K Λd (w.under (𝓞 ℚ))

open scoped Classical in

noncomputable def lambdaArch (w : InfinitePlace K) : ℂ :=
  if w.IsReal then 1 else signEpsilon 1

end LanglandsTunnell.CubicLambda


