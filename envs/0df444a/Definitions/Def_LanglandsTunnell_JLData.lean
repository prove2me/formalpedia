-- Prove2me | Definitions.Def_LanglandsTunnell_JLData
-- name    : LanglandsTunnell_JLData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a49b2583-e1a4-52f7-a9a9-b358d08ee519
-- title:
--   Converse-theorem data: S-weights, twists and JLData
-- statement:
--   Throughout, $K$ is a number field, $S$ a finite set of finite places of $K$, $\varepsilon = (\varepsilon_v)$ a family of characters of the local unit groups $K_v^\times$, and $\omega$ a character of the idele group. Several helpers set up the local bookkeeping: `localOf` sends $\alpha \in K^\times$ to its image in $K_v^\times$; `IsOneMod K v n u` asserts $v(u-1) \le \exp(-n)$, i.e. $u \equiv 1$ modulo $\mathfrak p_v^{\,n}$ in the normalisation where a uniformiser has valuation $\exp(-1)$; `IsSUnit K S \beta` asserts $|\beta|_v = 1$ for all $v \in S$ (a unit at the places of $S$, not the classical notion of $S$-unit); and `sWeight` is given by $\mathrm{sWeight}\,K\,S\,\chi\,\alpha\,s = \prod_{v \in S} \chi_v(\alpha)\, N(v)^{-\operatorname{ord}_v(\alpha)(s-1/2)}$, the $S$-part of a Tate weight. `IsJLTwist` selects the admissible (continuous, unitary, idele-class) characters $\mu$ with $\mu_v\varepsilon_v = 1$ on all $u$ with $|u|_v=1$, $v \in S$.
--
--   The structure `JLData K S \varepsilon \omega` packages: level exponents $m_v \ge 1$ ($v \in S$) such that $\varepsilon_v$ and $\omega_v$ are trivial on units congruent to $1$ mod $\mathfrak p_v^{m_v}$; an element $A \in K^\times$ with $\operatorname{ord}_v A = m_v$ for $v \in S$; bounded functions $a, \widehat a : K^\times \to \mathbb C$ (one constant bounding both) obeying $a(\alpha\beta) = \big(\prod_{v\in S}\varepsilon_v(\beta)\big)a(\alpha)$ and $\widehat a(\alpha\beta) = \big(\prod_{v\in S}\omega_v(\beta)\varepsilon_v(\beta)^{-1}\big)\widehat a(\alpha)$ for $\beta$ a unit at $S$; a support condition forcing $a(\alpha)=\widehat a(\alpha)=0$ unless $|\alpha|_v \le \exp(n(\psi_v))$ at every $v \in S$, where $n(\psi_v)$ is the level of the standard local additive character; and non-vanishing of $a$. `SOrderReps K S` is a choice of representatives $\alpha_n \in K^\times$, one for each $n \in \mathbb Z^S$, with $\operatorname{ord}_v \alpha_n = n_v$.
--
--   For such data, `sSum` and `sSumDual` are the unconditional sums $\sum_n a(\alpha_n)\,\mathrm{sWeight}(\mu,\alpha_n,s)$ and $\sum_n \widehat a(\alpha_n)\,\mathrm{sWeight}((\omega\mu)^{-1},\alpha_n,s)$, and `sFactor` is $\prod_{v\in S}\mu_v(-A)\,N(v)^{-m_v(s-1/2)}$.
--
--   Finally `IsJLNice` is the predicate, for a Hecke eigensystem $\Pi$ and archimedean parameters, that some choice of representatives works uniformly: for every twist $\mu$ as above and every realisation of its archimedean components by $(u_w,a_w)$ at real places and $(u_w,k_w)$ at complex places, the twisted $L$-datum $D$ built from $\Pi$ outside $S$ is well formed and convergent, and there are $\sigma_0$ and entire $\Lambda,\Lambda^\vee$, bounded on vertical strips, with the two sums summable and $\Lambda(s) = \mathrm{sSum}(s)\,D.\mathrm{archFactor}(s)\,D.L(s)$, $\Lambda^\vee(s) = \mathrm{sSumDual}(s)\,D.\mathrm{archFactorDual}(s)\,D.L^\vee(s)$ for $\operatorname{Re} s > \sigma_0$, together with the functional equation $\Lambda(s) = \mathrm{sFactor}(\mu,s)\,\epsilon\,N^{1/2-s}\,\Lambda^\vee(1-s)$, where $\epsilon$ is the pinned root number and $N$ the finite conductor attached to $\Pi$, $\mu$, $S$ and the archimedean data.
--
--   **Relation to Mathlib.** Mathlib contains no adelic automorphic forms, $L$-data or converse-theorem machinery; all the notions here are the project's own, built on Mathlib's adele ring, height-one spectrum and the Gamma factors $\Gamma_{\mathbb R}$, $\Gamma_{\mathbb C}$.
--
--   **Where it is used.** These definitions provide the analytic input for a Weil-type converse theorem in the Langlands–Tunnell step: the coefficient families $a$, $\widehat a$ with their $S$-unit transformation laws and support conditions, together with the uniform analytic continuation and functional equation for all admissible twists, are what one verifies for the $L$-function of an Artin representation in order to recognise it as coming from an automorphic form on $\mathrm{GL}_2$. That step supplies the modularity of the mod-$3$ representation which starts the Frey–Serre–Ribet–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_JLData.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.TateGlobal LanglandsTunnell.TateLocal NumberField.StandardAddChar
noncomputable section

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K]

def localOf (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) : (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom α

def IsOneMod (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (u : (v.adicCompletion K)ˣ) : Prop :=
  Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))

def IsSUnit (S : Finset (HeightOneSpectrum (𝓞 K))) (β : Kˣ) : Prop :=
  ∀ v : ↥S, Valued.v ((localOf K v.1 β : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = 1

def sWeight (S : Finset (HeightOneSpectrum (𝓞 K))) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : Kˣ) (s : ℂ) : ℂ :=
  ∏ v : ↥S,
    ((localChar χ v.1 (localOf K v.1 α) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
        (((WithZero.log (Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)) : ℤ) : ℂ)
          * (s - 1 / 2))

def IsJLTwist (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  IsAdmissibleTwist K μ ∧
    ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      localChar μ v u * epsS v u = 1

structure JLData (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) where

  m : ↥S → ℕ
  m_pos : ∀ v, 1 ≤ m v

  epsS_level : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
    IsOneMod K v.1 (m v) u → epsS v.1 u = 1

  central_level : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
    IsOneMod K v.1 (m v) u → localChar ω v.1 u = 1

  A : Kˣ
  A_ord : ∀ v : ↥S, Valued.v ((localOf K v.1 A : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
    = WithZero.exp (-(m v : ℤ))

  a : Kˣ → ℂ
  ad : Kˣ → ℂ

  bounded : ∃ C : ℝ, ∀ α, ‖a α‖ ≤ C ∧ ‖ad α‖ ≤ C

  a_mul : ∀ α β : Kˣ, IsSUnit K S β →
    a (α * β) = (∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ)) * a α

  ad_mul : ∀ α β : Kˣ, IsSUnit K S β →
    ad (α * β) =
      (∏ v : ↥S, ((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) * (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ))
        * ad α

  floor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → a α = 0 ∧ ad α = 0

  a_ne_zero : ∃ α, a α ≠ 0

structure SOrderReps (S : Finset (HeightOneSpectrum (𝓞 K))) where
  rep : (↥S → ℤ) → Kˣ
  rep_ord : ∀ (n : ↥S → ℤ) (v : ↥S),
    Valued.v ((localOf K v.1 (rep n) : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = WithZero.exp (-(n v))

variable {K}

namespace JLData

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
  {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

def sSum (d : JLData K S epsS ω) (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, d.a (R.rep n) * sWeight K S μ (R.rep n) s

def sSumDual (d : JLData K S epsS ω) (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, d.ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s

def sFactor (d : JLData K S epsS ω) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∏ v : ↥S,
    ((localChar μ v.1 (localOf K v.1 (-d.A)) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((d.m v : ℕ) : ℂ) * (s - 1 / 2))

end JLData

variable (K)

def IsJLNice (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (d : JLData K S epsS ω)
    (Pi : HeckeEigensystem K ℂ)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam) : Prop :=
  ∃ R : SOrderReps K S, ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsJLTwist K S epsS μ →
    ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
      (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
      (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
      (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
      let D := twistedDatum K Pi S archR archC μ uR aR uC kC
      D.WellFormed ∧ D.Converges ∧
      ∃ σ₀ : ℝ, ∃ Λ Λd : ℂ → ℂ,
        Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
        LDatum.BoundedOnStrips Λ ∧ LDatum.BoundedOnStrips Λd ∧
        (∀ s : ℂ, σ₀ < s.re →
          Summable (fun n : ↥S → ℤ => d.a (R.rep n) * sWeight K S μ (R.rep n) s) ∧
          Summable (fun n : ↥S → ℤ => d.ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s) ∧
          Λ s = d.sSum R μ s * D.archFactor s * D.LFun s ∧
          Λd s = d.sSumDual R μ s * D.archFactorDual s * D.LFunDual s) ∧
        (∀ s : ℂ,
          Λ s = d.sFactor μ s * pinnedRootNumber K Pi μ S archR archC uR aR uC kC *
            ((finiteConductor K μ S : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * Λd (1 - s))

example {v : HeightOneSpectrum (𝓞 K)} (ψ : AddChar (v.adicCompletion K) ℂ) :
    addCharLevel ψ = sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1} :=
  addCharLevel_def ψ

end LanglandsTunnell.Converse

end


