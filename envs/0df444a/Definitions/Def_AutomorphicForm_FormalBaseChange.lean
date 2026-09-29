-- Prove2me | Definitions.Def_AutomorphicForm_FormalBaseChange
-- name    : AutomorphicForm_FormalBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4ce12d42-5728-5012-aa8d-69e4cd92f82d
-- title:
--   Formal base change of Hecke eigensystems; cubic lift package
-- statement:
--   A `HeckeEigensystem F R` is the project's bookkeeping device for an automorphic form: a nonzero level ideal of $\mathcal{O}_F$ together with two functions $a, b$ on the height-one spectrum of $\mathcal{O}_F$, recording the trace and the determinant of the Satake parameter at each finite place. For an extension $K/F$ of number fields with $\mathcal{O}_K$ integral over $\mathcal{O}_F$, `formalBaseChange` transports such data from $F$ to $K$ purely formally: the level of the result is $\top$ (the unit ideal), and for a prime $\mathfrak{P}$ of $K$ lying under $\mathfrak{p} = \mathfrak{P}\cap\mathcal{O}_F$ with residue degree $f = f(\mathfrak{P}/\mathfrak{p})$ one sets $a_{\mathfrak{P}} = V_f(a_{\mathfrak{p}}, b_{\mathfrak{p}})$ and $b_{\mathfrak{P}} = b_{\mathfrak{p}}^{f}$, where `satakePow` is the power-sum recursion $V_0 = 2$, $V_1 = s$, $V_{n+2} = sV_{n+1} - eV_n$ (the $n$-th power sum of the roots of $X^2 - sX + e$). Two `rfl` lemmas record these values. Thus `formalBaseChange` realises, on the level of Satake data, the local restriction rule of base change; it carries no analytic information.
--
--   Two predicates express residue-degree hypotheses away from a finite set of primes of $K$: `CubicResidueDegOutside S` asserts $f(\mathfrak{P}/\mathfrak{P}\cap\mathcal{O}_F) \in \{1,3\}$ for all $\mathfrak{P} \notin S$, and `IsDegreeThreeOutside S` asserts $f \le 3$ there.
--
--   `JPSSCubicLiftPackage` bundles, as structure fields: a `CuspidalityNotion` over $R$ (an abstract predicate `IsCusp` on eigensystems over each number field); the existence of a finite $S$ with `IsDegreeThreeOutside F K S`; and the assertion that every $\pi$ over $F$ with `IsCusp F π` admits $\Phi$ over $K$ satisfying `IsBaseChangeOf π Φ` (the Satake relations above hold at all $\mathfrak{P}$ outside a finite set) together with `IsCusp K Φ` **or** `Φ.IsConstantOnFibers F`. The second disjunct is satisfied by `formalBaseChange F K π` itself, so this field is strictly weaker than the classical cubic lifting theorem: it does not force the lift to be cuspidal.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic form or of Hecke eigensystem; `HeckeEigensystem`, `satakePow`, `IsBaseChangeOf`, `CuspidalityNotion` and the notions defined here are the project's own. Only the arithmetic substrate is Mathlib's: `IsDedekindDomain.HeightOneSpectrum (𝓞 F)`, the pullback `𝔓.under (𝓞 F)` of a prime along an integral extension of rings of integers, and the residue degree `Ideal.inertiaDeg'`.
--
--   **Where it is used.** This vocabulary serves the base-change step of the Langlands–Tunnell theorem, where a form over a field $F$ must be lifted along a non-normal cubic extension $K/F$; the resulting weight-two statement feeds the modularity of the residual representation attached to a Frey curve at the prime $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_FormalBaseChange.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace AutomorphicForm

section FormalLift

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

def formalBaseChange (π : HeckeEigensystem F R) : HeckeEigensystem K R where
  level := ⊤
  level_ne_bot := by simp
  a := fun 𝔓 => satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
    (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F)))
  b := fun 𝔓 => (π.b (𝔓.under (𝓞 F))) ^
    ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)

@[simp] theorem formalBaseChange_a (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).a 𝔓 =
      satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
        (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F))) := rfl

@[simp] theorem formalBaseChange_b (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).b 𝔓 =
      (π.b (𝔓.under (𝓞 F))) ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) := rfl

end FormalLift

section CubicHypothesis

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

def CubicResidueDegOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∉ S →
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1 ∨
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 3

def IsDegreeThreeOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∉ S →
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ 3

end CubicHypothesis

section Package

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

structure JPSSCubicLiftPackage where

  notion : CuspidalityNotion R

  cubicDeg : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S

  lift_automorphic : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ∃ Φ : HeckeEigensystem K R, IsBaseChangeOf π Φ ∧
      (notion.IsCusp K Φ ∨ Φ.IsConstantOnFibers F)

end Package

end AutomorphicForm

end


