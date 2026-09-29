-- Prove2me | Definitions.Def_NumberField_TateGlobalZeta
-- name    : NumberField_TateGlobalZeta
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c84b2557-14f3-590b-8221-385cc7195170
-- title:
--   Idele norm, global zeta integrals, local components of characters
-- statement:
--   Throughout, $F$ is a number field, and the ambient objects are Mathlib's adele ring $\mathbb{A}_F$ of $F$ over $\mathcal{O}_F$ and its unit group, the idele group. The idelic modulus is taken to be Mathlib's `distribHaarChar` for the scaling action of the ideles on the additive group of adeles: `ideleNorm F x` is the value of that character at $x$, read as a real number, and `normOneIdeles F` is the kernel of the character, a subgroup of the idele group. The accompanying lemmas record that `ideleNorm` is strictly positive, is multiplicative, and that membership of `normOneIdeles F` is equivalent to `ideleNorm F x = 1`. Given a measurable space structure and a measure $\nu$ on the idele group, a function $f$ on the adeles, a monoid homomorphism $\chi$ from the ideles to $\mathbb{C}^\times$, and $s \in \mathbb{C}$, `zetaIntegral` is the Bochner integral $\int f(x)\,\chi(x)\,|x|^{s}\,d\nu(x)$, with $|x| =$ `ideleNorm F x`; as a Bochner integral it is $0$ when the integrand fails to be integrable.
--
--   The local components of a character $\chi$ are defined by precomposition. At a finite place $v$, `localChar χ v` is $\chi$ composed with the monoid homomorphism `localUnit (𝓞 F) F v` from $(F_v)^\times$ to the units of the finite adele ring followed by `Units.map (finIncl (𝓞 F) F)` into the idele group. At an infinite place $w$, `archUnitHom w` is the monoid homomorphism sending $a \in (F_w)^\times$ to the idele whose finite part is $1$ and whose infinite part is the constant function $1$ updated at $w$ to $a$ (this is `archCentralUnit F w`, here equipped with unitality and multiplicativity), and `archLocalChar χ w` is $\chi$ composed with it; three lemmas unfold these three definitions. `IsUnramifiedCharAt χ v` asserts that `localChar χ v` is trivial on those $t \in (F_v)^\times$ for which both $t$ and $t^{-1}$ lie in the valuation ring `v.adicCompletionIntegers F`. Finally, for a finite set $S$ of finite places, `integralOutside S` is the set of adeles whose finite component lies in `v.adicCompletionIntegers F` for every $v \notin S$, and `IsFactorizableStandardOutside f S g h` asserts pointwise that $f$ equals the indicator function of `integralOutside S` applied to $x \mapsto \big(\prod_{w} g\,w\,(x_1 w)\big)\prod_{v \in S} h\,v\,(x_2 v)$, the product over all infinite places $w$ and over the places of $S$.
--
--   **Relation to Mathlib.** The idelic modulus is not defined afresh: it is Mathlib's `distribHaarChar` of the adele ring, and `ideleNorm`/`normOneIdeles` are its real-valued avatar and its kernel. The zeta integral, the local components of an idele class character, the unramifiedness predicate and the factorisability predicate are the project's own notions; Mathlib has no global zeta integral.
--
--   **Where it is used.** This module fixes the vocabulary of Tate's global theory — idele norm, norm-one ideles, global zeta integrals, local components of characters, and adelic test functions that are standard outside a finite set of places — used on the analytic side of the adelic theory of automorphic forms on $\mathrm{GL}_2$ over $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_TateGlobalZeta.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
open AutomorphicForm IsDedekindDomain
open scoped NNReal

noncomputable section

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

def normOneIdeles : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).ker

def ideleNorm (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ)

variable {F}

theorem ideleNorm_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < ideleNorm F x :=
  NNReal.coe_pos.mpr (distribHaarChar_pos)

def zetaIntegral {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (f : AdeleRing (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν

def localChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  χ.comp ((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v))

def archUnitHom (w : InfinitePlace F) : (w.Completion)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun := archCentralUnit F w
  map_one' := by
    classical
    refine Units.ext (Prod.ext (funext fun v => ?_) rfl)
    show Function.update (1 : InfiniteAdeleRing F) w ((1 : InfiniteAdeleRing F) w) v
      = (1 : InfiniteAdeleRing F) v
    rw [Function.update_eq_self]
  map_mul' a b := by
    classical
    refine Units.ext (Prod.ext (funext fun v => ?_) (one_mul 1).symm)
    show Function.update (1 : InfiniteAdeleRing F) w (((a * b : (w.Completion)ˣ)) : w.Completion) v
      = Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion) v
          * Function.update (1 : InfiniteAdeleRing F) w (b : w.Completion) v
    by_cases hv : v = w
    · subst hv
      simp [Function.update_self]
    · rw [Function.update_of_ne hv, Function.update_of_ne hv, Function.update_of_ne hv]
      exact (mul_one _).symm

def archLocalChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) :
    (w.Completion)ˣ →* ℂˣ :=
  χ.comp (archUnitHom w)

def IsUnramifiedCharAt (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      localChar χ v t = 1

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (AdeleRing (𝓞 F) F) :=
  {x | ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

def IsFactorizableStandardOutside (f : AdeleRing (𝓞 F) F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : (w : InfinitePlace F) → w.Completion → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (integralOutside S).indicator
      (fun x => (∏ w, g w (x.1 w)) * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

theorem ideleNorm_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F (x * y) = ideleNorm F x * ideleNorm F y := by
  simp [ideleNorm, map_mul]

theorem mem_normOneIdeles_iff (x : (AdeleRing (𝓞 F) F)ˣ) : x ∈ normOneIdeles F ↔ ideleNorm F x = 1 := by
  simp [normOneIdeles, ideleNorm, MonoidHom.mem_ker]

theorem localChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ) :
    localChar χ v t = χ (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) := rfl

theorem archUnitHom_apply (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archUnitHom w a = archCentralUnit F w a := rfl

theorem archLocalChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archLocalChar χ w a = χ (archCentralUnit F w a) := rfl

end NumberField.TateGlobal

end


