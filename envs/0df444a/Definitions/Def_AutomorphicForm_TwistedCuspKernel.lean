-- Prove2me | Definitions.Def_AutomorphicForm_TwistedCuspKernel
-- name    : AutomorphicForm_TwistedCuspKernel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/534827c9-1ca4-5e35-9371-3e673f539bc3
-- title:
--   Twisted norm cells, cusp kernel and cusp truncation for GL(2)
-- statement:
--   Throughout, $L/K$ is an extension of number fields with $\sigma$ an automorphism of $L$ over $K$ whose integral powers exhaust $\mathrm{Gal}(L/K)$ (the hypothesis `hgen`), so that the extension is cyclic with generator $\sigma$.
--
--   Four set- or function-level notions are introduced. `normUnipotentSet` is the set of $\delta \in \mathrm{GL}_2(L)$ whose $\sigma$-twisted conjugacy class — the class of $\delta$ under $\delta \mapsto h^{-1}\delta\,\sigma(h)$ — is carried by [`LT.TwistedNorm.normClassMap`](../def/TwistedNormClasses.html#L766) to the $\mathrm{GL}_2(K)$-conjugacy class of some $\gamma$ in [`AutomorphicForm.unipotentCell K`](../def/AutomorphicForm_GL2ConjugacyCells.html#L29), i.e. some $\gamma$ whose matrix is not a scalar multiple of the identity and whose characteristic polynomial is $(X-a)^2$ for some $a \in K$. Here `normClassMap` is the map sending the twisted class of $\delta$ to the conjugacy class of a descent to $\mathrm{GL}_2(K)$ of the $\sigma$-norm $\delta\,\sigma(\delta)\cdots\sigma^{[L:K]-1}(\delta)$. `borelNormOneSet` is the set of $\gamma \in \mathrm{GL}_2(L)$ with lower-left entry $0$ and $N_{L/K}(\gamma_{00}/\gamma_{11}) = 1$. `IsCuspTransversal L reps` asserts that every $g \in \mathrm{GL}_2(L)$ admits exactly one $\rho \in \mathrm{reps}$ with $g\rho^{-1}$ in the upper-triangular subgroup `borelSubgroup L`; it is a property of a chosen set of representatives, not of a quotient.
--
--   Given a descent datum $D$ for the adeles of $L$ over $K$, a function $\varphi$ on $\mathrm{GL}_2$ of the adeles of $L$, a central idele $z$ and $g$, `cuspKernel` is the (possibly infinite, unordered) sum over $\beta$ in the intersection of `normUnipotentSet` with the upper-triangular subgroup of $\varphi\bigl(g^{-1}\,\beta\,\sigma(zg)\bigr)$, where $\beta$ enters through its adelic image and $\sigma$ acts on adelic matrices via `sigmaAdelicAct`. `cuspTruncation` is, at the point $zg$, the indicator of the set where the adelic height exceeds $e^R$ applied to the constant term — taken along the unipotent family $t \mapsto n(t)$ and with respect to the adelic additive Haar measure conditioned on the adelic box — of the function $y \mapsto \sum_{\delta \in \mathrm{borelNormOneSet}} \varphi\bigl(g^{-1}\,\delta\,\sigma(y)\bigr)$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient objects ($\mathrm{GL}_n$ over a ring, `ConjClasses`, `Algebra.norm`, adele and finite adele rings, unconditioned sums `∑ᶠ` and Haar measure), but has no $\sigma$-twisted conjugacy classes, no $\sigma$-norm map on $\mathrm{GL}_2$ and no adelic automorphic-form machinery; the notions here, together with the twisted norm classes, conjugacy cells, constant terms and adelic heights they are built from, are the project's own.
--
--   **Where it is used.** These are the geometric-side ingredients of the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension: `cuspKernel` collects the unipotent twisted classes and `cuspTruncation` the truncation of the associated constant term, both of which occur in the comparison of twisted and ordinary orbital data underlying cyclic base change for $\mathrm{GL}_2$. That base change is what supports the Langlands–Tunnell theorem, which provides the residual modularity input at the prime $3$ in the Frey–Serre–Ribet–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TwistedCuspKernel.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

namespace AutomorphicForm.TwistedBruhat

def normUnipotentSet (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
    γ ∈ AutomorphicForm.unipotentCell K ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}

def borelNormOneSet (K L : Type) [Field K] [Field L] [Algebra K L] : Set (GL (Fin 2) L) :=
  {γ : GL (Fin 2) L |
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1}

def IsCuspTransversal (L : Type) [Field L] (reps : Set (GL (Fin 2) L)) : Prop :=
  ∀ g : GL (Fin 2) L, ∃! ρ : GL (Fin 2) L, ρ ∈ reps ∧ g * ρ⁻¹ ∈ AutomorphicForm.borelSubgroup L

noncomputable def cuspKernel (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ β ∈ normUnipotentSet K L σ hgen ∩ (AutomorphicForm.borelSubgroup L : Set (GL (Fin 2) L)),
    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L β *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * g))

noncomputable def cuspTruncation (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => AutomorphicForm.unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ borelNormOneSet K L,
        φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
    (AutomorphicForm.centralScalar (𝓞 L) L z * g)

end AutomorphicForm.TwistedBruhat


