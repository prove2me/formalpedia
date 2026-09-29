-- Prove2me | Definitions.Def_AutomorphicForm_HeckeEigensystem
-- name    : AutomorphicForm_HeckeEigensystem
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/35d03495-9e8d-522b-8f07-a7e68b0ad7c9
-- title:
--   Hecke eigensystem carriers, base change and descent packages
-- statement:
--   This module sets up a lightweight carrier for systems of Hecke eigenvalues and the predicates used to state solvable base change and descent on it. A `HeckeEigensystem F R`, for a number field $F$ and a commutative ring $R$, consists of four data: an ideal `level` of $\mathcal{O}_F$, a proof that it is nonzero, and two functions `a`, `b` from the height-one spectrum of $\mathcal{O}_F$ to $R$. Nothing further is imposed: there is no automorphy, holomorphy or growth condition, and no compatibility between `a`, `b` and `level`; the intended reading is that at a prime $v$ the values $a_v$ and $b_v$ are the sum and the product of the two Satake parameters. `twist Φ χ` keeps the level and replaces $a_v, b_v$ by $\chi(v) a_v$ and $\chi(v)^2 b_v$ for an arbitrary function $\chi$ on primes (not required multiplicative); `twist_a`, `twist_b` record this by `rfl`. `AgreesAwayFromFinite Φ Φ'` says that $a$ and $b$ agree outside some finite set of primes. For an integral extension $\mathcal{O}_E \to \mathcal{O}_L$, `IsConstantOnFibers Φ E` says that outside a finite set of primes of $\mathcal{O}_L$, any two primes with the same contraction to $\mathcal{O}_E$ and the same inertia degree (`inertiaDeg'`) have equal $a$- and $b$-values.
--
--   `satakePow n s e` is the Lucas-type recursion with $V_0 = 2$, $V_1 = s$, $V_{n+2} = sV_{n+1} - eV_n$, computing $\alpha^n + \beta^n$ from $s = \alpha+\beta$, $e = \alpha\beta$; the three lemmas give the base cases and the recursion, all by `rfl`. `IsBaseChangeAt π Φ 𝔓` asserts, with $f$ the inertia degree of $\mathfrak{P}$ over $\mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_E$, that $\Phi.a_{\mathfrak{P}} = V_f(\pi.a_{\mathfrak{p}}, \pi.b_{\mathfrak{p}})$ and $\Phi.b_{\mathfrak{P}} = (\pi.b_{\mathfrak{p}})^f$; `IsBaseChangeOf` requires this outside a finite set of primes, and `IsDescentOf` is the same relation with arguments swapped. Finally, `CuspidalityNotion R` is an opaque structure carrying just a predicate `IsCusp` on eigensystems over every number field, and `DescentPackage R E L Φ₀` bundles such a notion together with theorems as fields: the seed $\Phi_0$ is cuspidal and constant on fibres over $E$; every cuspidal eigensystem over $L$ that is constant on fibres is a base change of some cuspidal eigensystem over $E$; and a multiplicity-one clause, saying that two cuspidal eigensystems over $E$ agreeing away from a finite set have equal $a$-values at every prime not dividing either level.
--
--   **Relation to Mathlib.** Mathlib has no notion of Hecke eigensystem or of automorphic base change; all the objects here are the project's own, built on Mathlib's `IsDedekindDomain.HeightOneSpectrum`, prime contraction (`under`) and `inertiaDeg'`.
--
--   **Where it is used.** These carriers are the form in which the Langlands–Tunnell theorem and the solvable base-change and descent steps are stated and cited in the project: statements about automorphic representations are phrased as statements about their systems of Hecke eigenvalues, with cuspidality and cyclic descent supplied as hypotheses packaged in `CuspidalityNotion` and `DescentPackage`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_HeckeEigensystem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

structure HeckeEigensystem (F : Type*) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where

  level : Ideal (𝓞 F)

  level_ne_bot : level ≠ ⊥

  a : HeightOneSpectrum (𝓞 F) → R

  b : HeightOneSpectrum (𝓞 F) → R

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]

def twist (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R) :
    HeckeEigensystem F R where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => χ v * Φ.a v
  b := fun v => χ v ^ 2 * Φ.b v

@[simp] theorem twist_a (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.twist χ).a v = χ v * Φ.a v := rfl

@[simp] theorem twist_b (Φ : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.twist χ).b v = χ v ^ 2 * Φ.b v := rfl

def AgreesAwayFromFinite (Φ Φ' : HeckeEigensystem F R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
    ∀ v ∉ S, Φ.a v = Φ'.a v ∧ Φ.b v = Φ'.b v

def IsConstantOnFibers {L : Type*} [Field L] [NumberField L]
    {R : Type*} [CommRing R] (Φ : HeckeEigensystem L R)
    (E : Type*) [Field E] [NumberField E]
    [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)] : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ 𝔓₁ ∉ S, ∀ 𝔓₂ ∉ S,
      𝔓₁.under (𝓞 E) = 𝔓₂.under (𝓞 E) →
      (𝔓₁.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓₁.asIdeal
        = (𝔓₂.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Φ.a 𝔓₁ = Φ.a 𝔓₂ ∧ Φ.b 𝔓₁ = Φ.b 𝔓₂

end HeckeEigensystem

def satakePow {R : Type*} [CommRing R] (n : ℕ) (s e : R) : R :=
  match n with
  | 0 => 2
  | 1 => s
  | (n + 2) => s * satakePow (n + 1) s e - e * satakePow n s e

@[simp] theorem satakePow_zero {R : Type*} [CommRing R] (s e : R) : satakePow 0 s e = 2 := rfl

@[simp] theorem satakePow_one {R : Type*} [CommRing R] (s e : R) : satakePow 1 s e = s := rfl

theorem satakePow_add_two {R : Type*} [CommRing R] (n : ℕ) (s e : R) :
    satakePow (n + 2) s e = s * satakePow (n + 1) s e - e * satakePow n s e := rfl

section Transfer

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
  {R : Type*} [CommRing R]

def IsBaseChangeAt (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R)
    (𝔓 : HeightOneSpectrum (𝓞 L)) : Prop :=
  Φ.a 𝔓 = satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))) ∧
  Φ.b 𝔓 = (π.b (𝔓.under (𝓞 E))) ^ ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)

def IsBaseChangeOf (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S, IsBaseChangeAt π Φ 𝔓

def IsDescentOf (Φ : HeckeEigensystem L R) (π : HeckeEigensystem E R) : Prop :=
  IsBaseChangeOf π Φ

end Transfer

structure CuspidalityNotion (R : Type*) [CommRing R] where

  IsCusp : ∀ (F : Type) [Field F] [NumberField F], HeckeEigensystem F R → Prop

structure DescentPackage (R : Type*) [CommRing R]
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
    (Φ₀ : HeckeEigensystem L R) where

  notion : CuspidalityNotion R

  seed_isCusp : notion.IsCusp L Φ₀

  seed_constantOnFibers : Φ₀.IsConstantOnFibers E

  descent : ∀ Φ : HeckeEigensystem L R, notion.IsCusp L Φ → Φ.IsConstantOnFibers E →
    ∃ π : HeckeEigensystem E R, notion.IsCusp E π ∧ IsBaseChangeOf π Φ

  multOne : ∀ π π' : HeckeEigensystem E R, notion.IsCusp E π → notion.IsCusp E π' →
    HeckeEigensystem.AgreesAwayFromFinite π π' →
    ∀ v : HeightOneSpectrum (𝓞 E), ¬ v.asIdeal ∣ π.level → ¬ v.asIdeal ∣ π'.level →
      π.a v = π'.a v

end AutomorphicForm

end


