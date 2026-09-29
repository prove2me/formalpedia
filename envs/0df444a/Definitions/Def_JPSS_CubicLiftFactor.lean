-- Prove2me | Definitions.Def_JPSS_CubicLiftFactor
-- name    : JPSS_CubicLiftFactor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/67c5e4be-0744-5832-9464-ab40b01d5ae0
-- title:
--   Factored JPSS cubic base-change packages and GL(3) Euler factors
-- statement:
--   Over a commutative ring $R$, `gl3LFactorPoly e1 e2 e3` is the cubic polynomial $1 - e_1X + e_2X^2 - e_3X^3$; helper lemmas compute its coefficients in degrees $0,1,2,3$ as $1,-e_1,e_2,-e_3$, deduce that the triple $(e_1,e_2,e_3)$ is determined by the polynomial, and record the factorisation $\prod_{i}(1-\gamma_iX)$ when $(e_1,e_2,e_3)$ are the elementary symmetric functions of $\gamma_1,\gamma_2,\gamma_3$, together with the collapsed shape $1-cX^3$ in the case $(0,0,c)$. Four further identities treat the substitution $X\mapsto X^3$ in the degree-two factor `heckeLFactorPoly s e` $=1-sX+eX^2$, where `satakePow n s e` is the Chebyshev-type recursion with $\mathrm{sp}_0=2$, $\mathrm{sp}_1=s$, $\mathrm{sp}_{n+2}=s\,\mathrm{sp}_{n+1}-e\,\mathrm{sp}_n$: for $s=\alpha+\beta$, $e=\alpha\beta$ one gets $(1-\alpha^3X^3)(1-\beta^3X^3)$, in general $1-\mathrm{sp}_3(s,e)X^3+e^3X^6$, and likewise after scaling $(s,e)$ by $(c,c^2)$; `rankinFactor_inert` expands $(1-c\alpha^3X^3)(1-c\beta^3X^3)$.
--
--   The two structures refine `JPSSCubicLiftPackage`. `JPSSConverseFactored R F K`, for number fields $F,K$ with $\mathcal{O}_K$ integral over $\mathcal{O}_F$, carries a cuspidality notion (a family of predicates on Hecke eigensystems), the assertion that outside some finite set of primes of $K$ all residue degrees are $\le 3$, a predicate `ConverseHyp` on Hecke eigensystems over $K$, a field saying that any $\Phi$ satisfying `ConverseHyp` is cuspidal or constant on fibres over $F$, and a field saying that `formalBaseChange F K π` satisfies `ConverseHyp` for cuspidal $\pi$. The bridge `toJPSSCubicLiftPackage` supplies the package's lifting field with `formalBaseChange`, citing `isBaseChangeOf_formalBaseChange`. `JPSSGL3Factored` extends this by predicates `IsGL3Automorphic` on systems of Satake triples over $F$, `RankinNice` pairing an eigensystem with such a system, and `IsIrreducibleInduced` on functions on the primes of $K$, plus fields producing a GL(3)-automorphic $\sigma$ from each irreducible induced $\chi$, Rankin-niceness of cuspidal $\pi$ against any such $\sigma$, an Euler comparison yielding `ConverseHyp (formalBaseChange F K π)`, and a coherence field identifying the inherited proof with the one assembled from these three ingredients; `converseHyp_of_ingredients` performs that assembly. Finally `trivialNotion` (always cuspidal) is used to inhabit both structures from the residue-degree hypothesis alone, with all extra predicates taken to be `True`, and the resulting package is recorded.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic forms, Hecke eigensystems or base change; the structures and predicates here are the project's own. Only Mathlib's `Polynomial` (with `comp`), Dedekind-domain height-one spectrum and inertia degree are reused.
--
--   **Where it is used.** These are the intermediate layers of the non-normal cubic base change input for $\mathrm{GL}_2$: they reduce the lifting field of `JPSSCubicLiftPackage` first to a converse-theorem hypothesis over $K$, then to GL(3) automorphic induction, $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg niceness and a local Euler-factor comparison at primes of residue degree three. Cubic base change of this kind is what the Langlands–Tunnell step of the Fermat argument rests on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_JPSS_CubicLiftFactor.lean

import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_LocalLFactor
import Theorems.Thm_AutomorphicForm_isBaseChangeOf_formalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm

variable {R : Type*} [CommRing R]

def gl3LFactorPoly (e1 e2 e3 : R) : Polynomial R :=
  1 - C e1 * X + C e2 * X ^ 2 - C e3 * X ^ 3

@[simp] theorem gl3LFactorPoly_def (e1 e2 e3 : R) :
    gl3LFactorPoly e1 e2 e3 = 1 - C e1 * X + C e2 * X ^ 2 - C e3 * X ^ 3 := rfl

@[simp] theorem coeff_zero_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 0 = 1 := by
  simp [gl3LFactorPoly, coeff_one, coeff_X_pow]

@[simp] theorem coeff_one_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 1 = -e1 := by
  simp [gl3LFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

@[simp] theorem coeff_two_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 2 = e2 := by
  simp [gl3LFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

@[simp] theorem coeff_three_gl3LFactorPoly (e1 e2 e3 : R) :
    (gl3LFactorPoly e1 e2 e3).coeff 3 = -e3 := by
  simp [gl3LFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

theorem gl3LFactorPoly_inj {e1 e2 e3 e1' e2' e3' : R}
    (h : gl3LFactorPoly e1 e2 e3 = gl3LFactorPoly e1' e2' e3') :
    e1 = e1' ∧ e2 = e2' ∧ e3 = e3' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (·.coeff 1) h
    simp only [coeff_one_gl3LFactorPoly] at this; exact neg_injective this
  · have := congrArg (·.coeff 2) h
    simpa only [coeff_two_gl3LFactorPoly] using this
  · have := congrArg (·.coeff 3) h
    simp only [coeff_three_gl3LFactorPoly] at this; exact neg_injective this

theorem gl3LFactorPoly_split (γ₁ γ₂ γ₃ : R) :
    gl3LFactorPoly (γ₁ + γ₂ + γ₃) (γ₁ * γ₂ + γ₁ * γ₃ + γ₂ * γ₃) (γ₁ * γ₂ * γ₃) =
      (1 - C γ₁ * X) * (1 - C γ₂ * X) * (1 - C γ₃ * X) := by
  simp only [gl3LFactorPoly, map_add, map_mul]; ring

theorem gl3LFactorPoly_inertInduction (c : R) :
    gl3LFactorPoly 0 0 c = 1 - C c * X ^ 3 := by
  simp [gl3LFactorPoly]

theorem gl3LFactorPoly_splitInduction (c₁ c₂ c₃ : R) :
    gl3LFactorPoly (c₁ + c₂ + c₃) (c₁ * c₂ + c₁ * c₃ + c₂ * c₃) (c₁ * c₂ * c₃) =
      (1 - C c₁ * X) * (1 - C c₂ * X) * (1 - C c₃ * X) :=
  gl3LFactorPoly_split c₁ c₂ c₃

theorem eulerCompare_inert (α β : R) :
    (heckeLFactorPoly (satakePow 3 (α + β) (α * β)) ((α * β) ^ 3)).comp (X ^ 3) =
      (1 - C (α ^ 3) * X ^ 3) * (1 - C (β ^ 3) * X ^ 3) := by
  rw [satakePow_add_pow, mul_pow, heckeLFactorPoly_split]
  simp only [mul_comp, sub_comp, one_comp, C_comp, X_comp]

theorem eulerCompare_inert_symm (s e : R) :
    (heckeLFactorPoly (satakePow 3 s e) (e ^ 3)).comp (X ^ 3) =
      1 - C (satakePow 3 s e) * X ^ 3 + C (e ^ 3) * X ^ 6 := by
  simp only [heckeLFactorPoly_def, sub_comp, add_comp, one_comp, mul_comp, C_comp,
    X_comp, pow_comp]
  ring

theorem rankinFactor_inert (α β c : R) :
    (1 - C (c * α ^ 3) * X ^ 3) * (1 - C (c * β ^ 3) * X ^ 3) =
      1 - C (c * (α ^ 3 + β ^ 3)) * X ^ 3 + C (c ^ 2 * (α * β) ^ 3) * X ^ 6 := by
  push_cast [map_mul, map_add, map_pow]; ring

theorem eulerCompare_inert_twist (s e c : R) :
    (heckeLFactorPoly (c * satakePow 3 s e) (c ^ 2 * e ^ 3)).comp (X ^ 3) =
      1 - C (c * satakePow 3 s e) * X ^ 3 + C (c ^ 2 * e ^ 3) * X ^ 6 := by
  simp only [heckeLFactorPoly_def, sub_comp, add_comp, one_comp, mul_comp, C_comp,
    X_comp, pow_comp]
  ring

section Factor

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

structure JPSSConverseFactored where

  notion : CuspidalityNotion R

  cubicDeg : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S

  ConverseHyp : HeckeEigensystem K R → Prop

  jl_converse : ∀ Φ : HeckeEigensystem K R, ConverseHyp Φ →
    notion.IsCusp K Φ ∨ Φ.IsConstantOnFibers F

  formalLift_converseHyp : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ConverseHyp (formalBaseChange F K π)

variable {R F K}

def JPSSConverseFactored.toJPSSCubicLiftPackage (I : JPSSConverseFactored R F K) :
    JPSSCubicLiftPackage R F K where
  notion := I.notion
  cubicDeg := I.cubicDeg
  lift_automorphic := fun π hπ =>
    ⟨formalBaseChange F K π, isBaseChangeOf_formalBaseChange F K π,
      I.jl_converse _ (I.formalLift_converseHyp π hπ)⟩

variable (R F K)

structure JPSSGL3Factored extends JPSSConverseFactored R F K where

  IsGL3Automorphic : (HeightOneSpectrum (𝓞 F) → R × R × R) → Prop

  RankinNice : HeckeEigensystem F R → (HeightOneSpectrum (𝓞 F) → R × R × R) → Prop

  IsIrreducibleInduced : (HeightOneSpectrum (𝓞 K) → R) → Prop

  gl3_induction : ∀ χ : HeightOneSpectrum (𝓞 K) → R, IsIrreducibleInduced χ →
    ∃ σ : HeightOneSpectrum (𝓞 F) → R × R × R, IsGL3Automorphic σ

  rankin_nice : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ∀ σ, IsGL3Automorphic σ → RankinNice π σ

  euler_compare : ∀ π : HeckeEigensystem F R,
    (∀ χ : HeightOneSpectrum (𝓞 K) → R, IsIrreducibleInduced χ →
        ∃ σ, IsGL3Automorphic σ ∧ RankinNice π σ) →
    ConverseHyp (formalBaseChange F K π)

  formalLift_converseHyp_eq : ∀ π hπ,
    formalLift_converseHyp π hπ =
      euler_compare π (fun χ hirr =>
        let ⟨σ, hσ⟩ := gl3_induction χ hirr; ⟨σ, hσ, rankin_nice π hπ σ hσ⟩)

variable {R F K}

def JPSSGL3Factored.toJPSSCubicLiftPackage (I : JPSSGL3Factored R F K) :
    JPSSCubicLiftPackage R F K :=
  I.toJPSSConverseFactored.toJPSSCubicLiftPackage

theorem JPSSGL3Factored.converseHyp_of_ingredients (I : JPSSGL3Factored R F K)
    (π : HeckeEigensystem F R) (hπ : I.notion.IsCusp F π) :
    I.ConverseHyp (formalBaseChange F K π) :=
  I.euler_compare π fun χ hirr =>
    let ⟨σ, hσ⟩ := I.gl3_induction χ hirr; ⟨σ, hσ, I.rankin_nice π hπ σ hσ⟩

end Factor

def trivialNotion (R : Type*) [CommRing R] : CuspidalityNotion R where
  IsCusp := fun _ _ _ _ => True

section SAT

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

def jpssConverseFactored_sat
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    JPSSConverseFactored R F K where
  notion := trivialNotion R
  cubicDeg := hcubic
  ConverseHyp := fun _ => True
  jl_converse := fun _ _ => Or.inl trivial
  formalLift_converseHyp := fun _ _ => trivial

def jpssGL3Factored_sat
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    JPSSGL3Factored R F K where
  notion := trivialNotion R
  cubicDeg := hcubic
  ConverseHyp := fun _ => True
  jl_converse := fun _ _ => Or.inl trivial
  formalLift_converseHyp := fun _ _ => trivial
  IsGL3Automorphic := fun _ => True
  RankinNice := fun _ _ => True
  IsIrreducibleInduced := fun _ => True
  gl3_induction := fun _ _ => ⟨fun _ => (0, 0, 0), trivial⟩
  rankin_nice := fun _ _ _ _ => trivial
  euler_compare := fun _ _ => trivial
  formalLift_converseHyp_eq := fun _ _ => rfl

theorem jpssGL3Factored_sat_toPackage_notion
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    ((jpssGL3Factored_sat R F K hcubic).toJPSSCubicLiftPackage).notion = trivialNotion R :=
  rfl

def jpssConverseFactored_sat_toPackage
    (hcubic : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S) :
    JPSSCubicLiftPackage R F K :=
  (jpssConverseFactored_sat R F K hcubic).toJPSSCubicLiftPackage

end SAT

end AutomorphicForm

end


