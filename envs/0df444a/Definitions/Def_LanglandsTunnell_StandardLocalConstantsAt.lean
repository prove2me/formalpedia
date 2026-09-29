-- Prove2me | Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
-- name    : LanglandsTunnell_StandardLocalConstantsAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/fc3a2bc5-f926-5d6c-a227-2c9e06ee5322
-- title:
--   Standard local additive character, self-dual measure, local epsilon factors
-- statement:
--   Throughout, $K$ is a number field and $v$ a height-one prime of $\mathcal{O}_K$, with completion $K_v$. The first group of declarations embeds $K_v$ into the adeles: `finAdeleSingleAt` is the additive homomorphism sending $x$ to the finite adele with component $x$ at $v$ and $0$ at every other place, with lemmas computing its components at $v$ and away from $v$ and proving continuity; `adeleSingleAt` composes it with the inclusion $y \mapsto (0,y)$ of the finite adeles into the full adele ring. The local standard character `psiLocal` is the global character `stdAddChar K` (built from the adelic trace data of $K$) pulled back along `adeleSingleAt`, and is continuous. For an additive character $\psi$ of $K_v$, `addCharLevel` is $\sup\{n \in \mathbb{Z} : \psi(x)=1 \text{ whenever } \mathrm{v}(x) \le \exp(n)\}$, a supremum taken in $\mathbb{Z}$. Measure-theoretically, `localBorel` is the Borel $\sigma$-algebra of $K_v$ (a reducible definition, not an instance), `borelSpace_localBorel` records that it is a Borel structure, and `integersPositiveCompacts` presents $\mathcal{O}_v$ as a compact set with nonempty interior (it is compact and open). The measure `selfDualHaarAt` is the additive Haar measure normalised by $\mu(\mathcal{O}_v)=1$, scaled by $(N\mathfrak{p}_v)^{-n(\psi)/2}$ where $n(\psi)$ is the level of `psiLocal`. For a character $\chi : K_v^\times \to \mathbb{C}^\times$, `stdTestFunAt` is the indicator of $\mathcal{O}_v$ when $\chi$ satisfies `HasConductorExponentAt` at $0$ (i.e. $\chi$ is trivial on all units of valuation $1$), and otherwise the indicator of the image in $K_v$ of the higher unit set at the conductor exponent $a(\chi)$, namely the units $u$ with $\mathrm{v}(u)=1$ and $\mathrm{v}(u-1) \le \exp(-a)$. Finally `stdEpsilonAt` is the project's $\varepsilon$-factor $\gamma(\mu_v,\psi_{K,v},f_\chi,\chi,s)\,L(\chi,s)/L(\chi^{-1},1-s)$ evaluated at this measure, character and test function, and `stdRootNumberAt` is its value at $s=1/2$.
--
--   **Relation to Mathlib.** Mathlib supplies the restricted-product adele rings, additive Haar measure and `AddChar`; the level of a local additive character, the self-dual normalisation, Tate's standard test function and the local $\varepsilon$-factor and root number are the project's own notions, built on its local zeta, gamma and $L$-factor definitions.
--
--   **Where it is used.** These local constants provide the normalisations for the functional equations of Hecke $L$-functions of idele class characters, as needed on the automorphic side of the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_StandardLocalConstantsAt.lean

import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal

namespace NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open scoped Classical in

def finAdeleSingleAt : v.adicCompletion K →+ FiniteAdeleRing (𝓞 K) K where
  toFun x := (RestrictedProduct.single
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x : FiniteAdeleRing (𝓞 K) K)
  map_zero' := RestrictedProduct.single_zero _ v
  map_add' x y := RestrictedProduct.single_add _ v x y

open scoped Classical in
theorem finAdeleSingleAt_apply_self (x : v.adicCompletion K) : finAdeleSingleAt K v x v = x :=
  RestrictedProduct.single_eq_same _ v x

open scoped Classical in
theorem finAdeleSingleAt_apply_of_ne (x : v.adicCompletion K) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : finAdeleSingleAt K v x w = 0 :=
  RestrictedProduct.single_eq_of_ne _ x h

open scoped Classical in

theorem continuous_finAdeleSingleAt : Continuous (finAdeleSingleAt K v) := by
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ Filter.principal ({v}ᶜ) :=
    Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite
  let e : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal ({v}ᶜ)) :=
    fun x => ⟨Pi.single v x, by
      rw [Filter.eventually_principal]
      intro w hw
      rw [Pi.single_eq_of_ne (by simpa using hw)]
      exact zero_mem _⟩
  have he : Continuous e := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_single v
  have hfun : (fun x => finAdeleSingleAt K v x)
      = fun x => (RestrictedProduct.inclusion _ _ hle (e x) : FiniteAdeleRing (𝓞 K) K) := by
    funext x
    exact FiniteAdeleRing.ext K fun w => rfl
  change Continuous (fun x => finAdeleSingleAt K v x)
  rw [hfun]
  exact (RestrictedProduct.continuous_inclusion hle).comp he

def adeleSingleAt : v.adicCompletion K →+ AdeleRing (𝓞 K) K :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (finAdeleSingleAt K v)

theorem adeleSingleAt_apply (x : v.adicCompletion K) :
    adeleSingleAt K v x = ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x) := rfl

theorem continuous_adeleSingleAt : Continuous (adeleSingleAt K v) :=
  continuous_const.prodMk (continuous_finAdeleSingleAt K v)

def psiLocal : AddChar (v.adicCompletion K) ℂ :=
  (stdAddChar K).compAddMonoidHom (adeleSingleAt K v)

theorem psiLocal_apply (x : v.adicCompletion K) :
    psiLocal K v x = stdAddChar K ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x) := rfl

theorem continuous_psiLocal : Continuous (psiLocal K v) :=
  (adelicTraceData K).continuous_psiK.comp (continuous_adeleSingleAt K v)

end NumberField.StandardAddChar

namespace LanglandsTunnell.TateLocal

open NumberField.StandardAddChar

section Level

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def addCharLevel (ψ : AddChar (v.adicCompletion K) ℂ) : ℤ :=
  sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1}

theorem addCharLevel_def (ψ : AddChar (v.adicCompletion K) ℂ) :
    addCharLevel ψ
      = sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1} := rfl

end Level

section Std

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[reducible] def localBorel : MeasurableSpace (v.adicCompletion K) := borel _

theorem borelSpace_localBorel : @BorelSpace (v.adicCompletion K) _ (localBorel K v) :=
  @BorelSpace.mk _ _ (localBorel K v) rfl

def integersPositiveCompacts : TopologicalSpace.PositiveCompacts (v.adicCompletion K) where
  carrier := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  isCompact' := isCompact_iff_compactSpace.mpr
    (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  interior_nonempty' := by
    have h : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    rw [h.interior_eq]
    exact ⟨0, (v.adicCompletionIntegers K).zero_mem⟩

theorem coe_integersPositiveCompacts :
    (integersPositiveCompacts K v : Set (v.adicCompletion K)) = v.adicCompletionIntegers K := rfl

def selfDualHaarAt : @Measure (v.adicCompletion K) (localBorel K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  exact ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2))
    • Measure.addHaarMeasure (integersPositiveCompacts K v)

open Classical in

def stdTestFunAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : v.adicCompletion K → ℂ :=
  if HasConductorExponentAt K v χ 0 then
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator fun _ => (1 : ℂ)
  else
    (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) ''
        higherUnitsAt K v (conductorExponentAt K v χ)).indicator fun _ => (1 : ℂ)

def stdEpsilonAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ := by
  letI := localBorel K v
  exact localEpsilonAt K v (selfDualHaarAt K v) (psiLocal K v) (stdTestFunAt K v χ) χ s

def stdRootNumberAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℂ :=
  stdEpsilonAt K v χ (1 / 2)

theorem stdRootNumberAt_def (χ : (v.adicCompletion K)ˣ →* ℂˣ) :
    stdRootNumberAt K v χ = stdEpsilonAt K v χ (1 / 2) := rfl

end Std

end LanglandsTunnell.TateLocal

end


