-- Prove2me | Definitions.Def_LanglandsTunnell_ConverseData
-- name    : LanglandsTunnell_ConverseData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/e3d4b9d3-2327-5d22-ad33-08e587d1e05b
-- title:
--   Converse-theorem data: twisted L-data and pinned root numbers
-- statement:
--   Throughout, $K$ is a number field, $\Pi$ a `HeckeEigensystem` over $K$ with values in $\mathbb{C}$ (a level ideal $\ne 0$ together with families $a_v,b_v$ indexed by the finite places), $\mu:\mathbb{A}_K^\times\to\mathbb{C}^\times$ a multiplicative character of the ideles, and $S$ a finite set of finite places. For a finite place $v$, `pinnedExp` is the integer $a(\mu_v)+n(\psi_v)$, where $\mu_v$ is the local component `localChar` of $\mu$, $a(\mu_v)$ is given by the predicate-based `conductorExponentAt`, and $n(\psi_v)=\mathrm{addCharLevel}$ is the supremum of the integers $n$ with $\psi_v$ trivial on $\{x:\,|x|_v\le \exp n\}$ for the standard additive character $\psi_v=$ `psiLocal` of $K_v$. Then `goodPlaceRootNumber` is $b_v^{\,a(\mu_v)+n(\psi_v)}\cdot\varepsilon_v^2$ with $\varepsilon_v=$ `stdRootNumberAt`, the local Tate $\varepsilon$-factor of $\mu_v$ at $s=1/2$ for the self-dual Haar measure and the standard test function; `finiteRootNumber` and `finiteConductor` are the `finprod`s over all finite places of these quantities, resp. of $(N\mathfrak{p}_v)^{2(a(\mu_v)+n(\psi_v))}$, with the factors at $v\in S$ replaced by $1$ (a `finprod` being $1$ unless all but finitely many factors are $1$). `archRootNumber` multiplies the `epsilonFactor`s of real archimedean parameters twisted by data $(u_w,a_w)\in\mathbb{C}\times\mathbb{Z}/2$ over the real places with those of complex parameters twisted by $(u_w,k_w)\in\mathbb{C}\times\mathbb{Z}$ over the complex places; `pinnedRootNumber` is its product with `finiteRootNumber`.
--
--   `IsAdmissibleTwist` asserts that $\mu$ is trivial on the principal ideles of $K^\times$, continuous, and of absolute value $1$ everywhere. `IsArchCompAt K μ w u a` asserts that the component of $\mu$ at the infinite place $w$, viewed on $(K_w)^\times$ through the embedding sending $x$ to the idele equal to $x$ at $w$ and $1$ elsewhere, is $x\mapsto \|x\|^{m_w u}\,(e_w(x)/\|x\|)^{a}$, where $m_w$ is the multiplicity of $w$ and $e_w$ the canonical embedding of $K_w$. `twistedGammaR` and `twistedGammaC` collect, as multisets, the $\Gamma_\mathbb{R}$- and $\Gamma_\mathbb{C}$-shifts of the twisted archimedean parameters at the real and complex places.
--
--   `twistedDatum` assembles an `LDatum` indexed by the finite places outside $S$: norms $N\mathfrak{p}_v$; Euler polynomial $1-\mu(\varpi_v)a_v X+\mu(\varpi_v)^2 b_v X^2$ when $\mu$ is unramified at $v$ in the sense of `IsUnramifiedCharAt`, and $1$ otherwise; dual Euler polynomial $1-\mu(\varpi_v)^{-1}(a_v/b_v)X+\mu(\varpi_v)^{-2}b_v^{-1}X^2$ under the same alternative; the four $\Gamma$-multisets, the dual ones obtained from the dualised archimedean parameters with $u$'s and $k$'s negated; abscissa $1$, centre $1/2$, degree $2$. `eisensteinTableOf` produces, from a non-zero ideal $N$ and two idele characters $\mu_1,\mu_2$, the Hecke eigensystem of level $N$ with $a_v=\mu_1(\varpi_v)+\mu_2(\varpi_v)$ and $b_v=\mu_1(\varpi_v)\mu_2(\varpi_v)$. `IsNicePinned D ΛS ΛSd ε N` says that $D$ is well formed and convergent, $N>0$, and there are entire functions $\Lambda,\Lambda^\vee$, bounded on vertical strips, with $\Lambda(s)=\Lambda_S(s)\,\gamma(s)L(s)$ and $\Lambda^\vee(s)=\Lambda_S^\vee(s)\,\gamma^\vee(s)L^\vee(s)$ to the right of the abscissa, and $\Lambda(s)=\varepsilon N^{1/2-s}\Lambda^\vee(1-s)$ in terms of the centre of $D$; unlike `LDatum.IsNice`, the $\varepsilon$, the conductor and the two correction factors are prescribed rather than existentially quantified, and the corrections multiply the completed $L$-function instead of appearing as bad Euler factors. Finally `sPart` and `sPartDual` are the series $\sum_{n:S\to\mathbb{Z}}A(n)\prod_{v\in S}\bigl(\mu(\varpi_v)^{\pm1}(N\mathfrak{p}_v)^{1/2-s}\bigr)^{n_v}$, with two elementary lemmas: scaling the coefficient family commutes with multiplying `sPartDual` by a constant, and for $S=\emptyset$ the series `sPart` equals its single coefficient.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient objects (adele ring, height-one spectrum, infinite places and their completions, Haar measure, and Deligne's $\Gamma_\mathbb{R}$, $\Gamma_\mathbb{C}$ entering the archimedean factors of an `LDatum`); Hecke eigensystems, $L$-data, local $\varepsilon$- and root numbers and archimedean parameters are the project's own notions.
--
--   **Where it is used.** These are the data entering the functional equations required by the converse theorem for $\mathrm{GL}(2)$: a Hecke eigensystem twisted by an admissible idele class character, its $L$-datum away from a finite set $S$, and the prescribed root number and conductor against which the twisted completed $L$-function is to be tested. They are used in the route to the Langlands–Tunnell theorem, which provides the modularity of the residual mod $3$ representation at the start of the Frey curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ConverseData.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_ArchEpsilon
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.Converse

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal NumberField.StandardAddChar LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K]

def pinnedExp (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  (conductorExponentAt K v (localChar μ v) : ℤ) + addCharLevel (psiLocal K v)

def goodPlaceRootNumber (Pi : HeckeEigensystem K ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Pi.b v : ℂ) ^ (pinnedExp K μ v) * (stdRootNumberAt K v (localChar μ v)) ^ 2

open Classical in

def finiteRootNumber (Pi : HeckeEigensystem K ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), if v ∈ S then 1 else goodPlaceRootNumber K Pi μ v

open Classical in

def finiteConductor (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    if v ∈ S then 1 else (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * pinnedExp K μ v)

open Classical in

def archRootNumber (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : ℂ :=
  ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
      fun w => ((archR w.1 w.2).twist (uR w.1 w.2) (aR w.1 w.2)).epsilonFactor) *
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
      fun w => ((archC w.1 w.2).twist (uC w.1 w.2) (kC w.1 w.2)).epsilonFactor)

def pinnedRootNumber (Pi : HeckeEigensystem K ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : ℂ :=
  archRootNumber K archR archC uR aR uC kC * finiteRootNumber K Pi μ S

end LanglandsTunnell.Converse

end

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain LanglandsTunnell Polynomial
open NumberField.TateGlobal NumberField.InfinitePlace.Completion

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K] (Pi : HeckeEigensystem K ℂ)

def IsAdmissibleTwist (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  IsIdeleClassChar (𝓞 K) K μ ∧ Continuous μ ∧ IsUnitaryChar (𝓞 K) K μ

def IsArchCompAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (u : ℂ) (a : ℤ) : Prop :=
  ∀ x : (w.Completion)ˣ,
    ((archLocalChar μ w x : ℂˣ) : ℂ) =
      ((‖(x : w.Completion)‖ : ℂ) ^ ((w.mult : ℂ) * u)) *
        (extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)) ^ a

open Classical in

def twistedGammaR (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) :
    Multiset ℂ :=
  (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).sum
    fun w => ((archR w.1 w.2).twist (uR w.1 w.2) (aR w.1 w.2)).gammaR

open Classical in

def twistedGammaC (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    Multiset ℂ :=
  ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).sum
      fun w => ((archR w.1 w.2).twist (uR w.1 w.2) (aR w.1 w.2)).gammaC) +
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).sum
      fun w => ((archC w.1 w.2).twist (uC w.1 w.2) (kC w.1 w.2)).gammaC)

def twistedDatum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    LDatum {v : HeightOneSpectrum (𝓞 K) // v ∉ S} where
  norm := fun v => Ideal.absNorm v.1.asIdeal
  euler := open scoped Classical in fun v =>
    if IsUnramifiedCharAt μ v.1
    then C 1 - C (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
      + C ((((μ (uniformizerIdele K v.1))^2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
    else C 1
  dual := open scoped Classical in fun v =>
    if IsUnramifiedCharAt μ v.1
    then C 1 - C ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) * (Pi.a v.1 / Pi.b v.1)) * X
      + C ((((μ (uniformizerIdele K v.1))^(-2 : ℤ) : ℂˣ) : ℂ) * (Pi.b v.1)⁻¹) * X ^ 2
    else C 1
  gammaR := twistedGammaR K archR uR aR
  gammaC := twistedGammaC K archR archC uR aR uC kC
  gammaRDual := twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR
  gammaCDual := twistedGammaC K (fun w hw => (archR w hw).dual)
    (fun w hw => (archC w hw).dual) (fun w hw => -uR w hw) aR
    (fun w hw => -uC w hw) (fun w hw => -kC w hw)
  abscissa := 1
  center := 1 / 2
  degree := 2

def eisensteinTableOf (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : HeckeEigensystem K ℂ where
  level := N
  level_ne_bot := hN
  a := fun v => ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ) + ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)
  b := fun v => ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)

def IsNicePinned {ι : Type*} (D : LDatum ι) (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ) : Prop :=
  D.WellFormed ∧ D.Converges ∧ 0 < N ∧
  ∃ Λ Λd : ℂ → ℂ,
    Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
    LDatum.BoundedOnStrips Λ ∧ LDatum.BoundedOnStrips Λd ∧
    (∀ s : ℂ, D.abscissa < s.re → Λ s = ΛS s * D.archFactor s * D.LFun s) ∧
    (∀ s : ℂ, D.abscissa < s.re → Λd s = ΛSd s * D.archFactorDual s * D.LFunDual s) ∧
    (∀ s : ℂ, Λ s = ε * (N : ℂ) ^ ((D.center : ℂ) - s) * Λd (2 * (D.center : ℂ) - s))

def sPart (S : Finset (HeightOneSpectrum (𝓞 K))) (A : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, A n * ∏ v : ↥S,
    (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)

def sPartDual (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, Ad n * ∏ v : ↥S,
    ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)

end LanglandsTunnell.Converse

end

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain LanglandsTunnell
open NumberField.TateGlobal

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K]

theorem sPartDual_const_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ad : (↥S → ℤ) → ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s c : ℂ) :
    c * sPartDual K S Ad μ s = sPartDual K S (fun n => c * Ad n) μ s := by
  unfold sPartDual
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem sPart_empty (A : (↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (n₀ : ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) → ℤ) :
    sPart K ∅ A μ s = A n₀ := by
  haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) := ⟨fun v => Finset.notMem_empty v.1 v.2⟩
  have hsub : ∀ n : ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) → ℤ, n = n₀ :=
    fun n => funext fun v => isEmptyElim v
  unfold sPart
  rw [tsum_eq_single n₀ (fun n hn => (hn (hsub n)).elim), Fintype.prod_empty, mul_one]

end LanglandsTunnell.Converse

end


