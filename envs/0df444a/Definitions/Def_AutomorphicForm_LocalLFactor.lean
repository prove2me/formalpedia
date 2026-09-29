-- Prove2me | Definitions.Def_AutomorphicForm_LocalLFactor
-- name    : AutomorphicForm_LocalLFactor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c57cbb18-166b-5723-b5ae-8731c138e790
-- title:
--   Local L-factor polynomials of Hecke eigensystems
-- statement:
--   Over a commutative ring $R$, `heckeLFactorPoly s e` is the quadratic $1 - sX + eX^2$ in `Polynomial R`; its coefficients in degrees $0,1,2$ are $1$, $-s$ and $e$, whence the map $(s,e) \mapsto \mathtt{heckeLFactorPoly}\,s\,e$ is injective (`heckeLFactorPoly_inj`, and the iff-form `heckeLFactorPoly_eq_iff`), it commutes with the coefficientwise image along a ring homomorphism $\varphi : R \to S$, and it splits as $1 - (\alpha+\beta)X + \alpha\beta X^2 = (1-\alpha X)(1-\beta X)$. For a `HeckeEigensystem` $\pi$ over a number field $F$ with values in $R$ — a structure carrying a nonzero level ideal of $\mathcal{O}_F$ and two functions $a, b$ on the height-one spectrum of $\mathcal{O}_F$ — `HeckeEigensystem.localLFactor π v` is $1 - \pi.a(v)X + \pi.b(v)X^2$, and equality of these polynomials at $v$ is equivalent to equality of both $\pi.a(v)$ and $\pi.b(v)$.
--
--   This dictionary is then used to restate the transfer predicates of the eigensystem module: for $\mathcal{O}_E \to \mathcal{O}_L$ an integral algebra of rings of integers of number fields, `IsBaseChangeAt π Φ 𝔓` (the pair of equations $\Phi.a(\mathfrak{P}) = \mathtt{satakePow}\,f\,(\pi.a(\mathfrak{p}))\,(\pi.b(\mathfrak{p}))$ and $\Phi.b(\mathfrak{P}) = \pi.b(\mathfrak{p})^f$, with $\mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_E$ and $f$ its `inertiaDeg'` at $\mathfrak{P}$) becomes the single polynomial identity $\Phi$'s local factor at $\mathfrak{P}$ equals $\mathtt{heckeLFactorPoly}$ of those two quantities; `IsBaseChangeOf` and `AgreesAwayFromFinite` become the corresponding identities outside a finite set of primes. Since `satakePow f` is the Newton power sum, $\mathtt{heckeLFactorPoly}(\mathtt{satakePow}\,f\,(\alpha+\beta)\,(\alpha\beta))((\alpha\beta)^f) = (1-\alpha^f X)(1-\beta^f X)$, with the cases $f = 1, 2$ recorded separately (and $\mathtt{satakePow}\,2\,s\,e = s^2 - 2e$).
--
--   Finally `HasBaseChangeLevelLaw 𝔡 π Φ` is the divisibility $\Phi.\mathrm{level} \mid \mathfrak{d} \cdot (\pi.\mathrm{level} \cdot \mathcal{O}_L)$, a level bound with an adjustable factor $\mathfrak{d}$; it holds vacuously for $\mathfrak{d} = \Phi.\mathrm{level}$, and the conjunction with `IsBaseChangeOf` is restated in local $L$-factor form.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic form, Hecke eigensystem or local $L$-factor; these are the project's own definitions, built from Mathlib's `Polynomial`, `Ideal`, `HeightOneSpectrum` and `inertiaDeg'`.
--
--   **Where it is used.** These definitions package the Satake data of a Hecke eigensystem into one local Euler factor per prime, so that the base-change and descent conditions used in the cyclic-base-change input to modularity can be stated and compared as polynomial identities away from a finite set of primes, together with a divisibility bound relating the levels of an eigensystem and of its base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_LocalLFactor.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Theorems.Thm_AutomorphicForm_satakePow_add_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm

@[simp] theorem satakePow_two {R : Type*} [CommRing R] (s e : R) :
    satakePow 2 s e = s ^ 2 - 2 * e := by
  show s * s - e * 2 = s ^ 2 - 2 * e; ring

variable {R : Type*} [CommRing R]

def heckeLFactorPoly (s e : R) : Polynomial R :=
  1 - C s * X + C e * X ^ 2

@[simp] theorem heckeLFactorPoly_def (s e : R) :
    heckeLFactorPoly s e = 1 - C s * X + C e * X ^ 2 := rfl

@[simp] theorem coeff_zero_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 0 = 1 := by
  simp [heckeLFactorPoly, coeff_one, coeff_X_pow]

@[simp] theorem coeff_one_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 1 = -s := by
  simp [heckeLFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

@[simp] theorem coeff_two_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 2 = e := by
  simp [heckeLFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

theorem heckeLFactorPoly_inj {s e s' e' : R}
    (h : heckeLFactorPoly s e = heckeLFactorPoly s' e') : s = s' ∧ e = e' := by
  refine ⟨?_, ?_⟩
  · have h1 := congrArg (fun p => p.coeff 1) h
    simp only [coeff_one_heckeLFactorPoly] at h1
    exact neg_injective h1
  · have h2 := congrArg (fun p => p.coeff 2) h
    simpa only [coeff_two_heckeLFactorPoly] using h2

theorem heckeLFactorPoly_eq_iff {s e s' e' : R} :
    heckeLFactorPoly s e = heckeLFactorPoly s' e' ↔ s = s' ∧ e = e' :=
  ⟨heckeLFactorPoly_inj, fun ⟨hs, he⟩ => by rw [hs, he]⟩

theorem heckeLFactorPoly_split (α β : R) :
    heckeLFactorPoly (α + β) (α * β) = (1 - C α * X) * (1 - C β * X) := by
  simp only [heckeLFactorPoly, map_add, map_mul]
  ring

theorem map_heckeLFactorPoly {S : Type*} [CommRing S] (φ : R →+* S) (s e : R) :
    (heckeLFactorPoly s e).map φ = heckeLFactorPoly (φ s) (φ e) := by
  simp [heckeLFactorPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_one, Polynomial.map_pow, map_C, map_X]

def HeckeEigensystem.localLFactor {F : Type*} [Field F] [NumberField F]
    (π : HeckeEigensystem F R) (v : HeightOneSpectrum (𝓞 F)) : Polynomial R :=
  heckeLFactorPoly (π.a v) (π.b v)

@[simp] theorem HeckeEigensystem.localLFactor_def {F : Type*} [Field F] [NumberField F]
    (π : HeckeEigensystem F R) (v : HeightOneSpectrum (𝓞 F)) :
    π.localLFactor v = heckeLFactorPoly (π.a v) (π.b v) := rfl

theorem HeckeEigensystem.satake_eq_of_localLFactor_eq {F : Type*} [Field F] [NumberField F]
    {π π' : HeckeEigensystem F R} {v : HeightOneSpectrum (𝓞 F)}
    (h : π.localLFactor v = π'.localLFactor v) : π.a v = π'.a v ∧ π.b v = π'.b v :=
  heckeLFactorPoly_inj h

section Factoring

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]

theorem isBaseChangeAt_iff_localLFactor (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R)
    (𝔓 : HeightOneSpectrum (𝓞 L)) :
    IsBaseChangeAt π Φ 𝔓 ↔
      Φ.localLFactor 𝔓 =
        heckeLFactorPoly
          (satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))))
          ((π.b (𝔓.under (𝓞 E))) ^ ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)) := by
  unfold IsBaseChangeAt HeckeEigensystem.localLFactor
  exact heckeLFactorPoly_eq_iff.symm

theorem isBaseChangeOf_iff_localLFactor (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) :
    IsBaseChangeOf π Φ ↔
      ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S,
        Φ.localLFactor 𝔓 =
          heckeLFactorPoly
            (satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
              (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))))
            ((π.b (𝔓.under (𝓞 E))) ^
              ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)) := by
  unfold IsBaseChangeOf
  refine exists_congr fun S => forall_congr' fun 𝔓 => forall_congr' fun _ => ?_
  exact isBaseChangeAt_iff_localLFactor π Φ 𝔓

theorem agreesAwayFromFinite_iff_localLFactor {F : Type*} [Field F] [NumberField F]
    (π π' : HeckeEigensystem F R) :
    HeckeEigensystem.AgreesAwayFromFinite π π' ↔
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        π.localLFactor v = π'.localLFactor v := by
  unfold HeckeEigensystem.AgreesAwayFromFinite
  refine exists_congr fun S => forall_congr' fun v => forall_congr' fun _ => ?_
  exact heckeLFactorPoly_eq_iff.symm

end Factoring

theorem heckeLFactorPoly_satakePow_split (f : ℕ) (α β : R) :
    heckeLFactorPoly (satakePow f (α + β) (α * β)) ((α * β) ^ f)
      = (1 - C (α ^ f) * X) * (1 - C (β ^ f) * X) := by
  rw [satakePow_add_pow, mul_pow, heckeLFactorPoly_split]

theorem heckeLFactorPoly_satakePow_one (s e : R) :
    heckeLFactorPoly (satakePow 1 s e) (e ^ 1) = heckeLFactorPoly s e := by
  rw [satakePow_one, pow_one]

theorem heckeLFactorPoly_satakePow_two (s e : R) :
    heckeLFactorPoly (satakePow 2 s e) (e ^ 2)
      = 1 - C (s ^ 2 - 2 * e) * X + C (e ^ 2) * X ^ 2 := by
  rw [satakePow_two, heckeLFactorPoly]

section ConductorCarrier

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]

def HasBaseChangeLevelLaw (𝔡 : Ideal (𝓞 L)) (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : Prop :=
  Φ.level ∣ 𝔡 * Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level

omit [Algebra.IsIntegral (𝓞 E) (𝓞 L)] in

theorem hasBaseChangeLevelLaw_sat (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : HasBaseChangeLevelLaw Φ.level π Φ :=
  dvd_mul_right Φ.level (Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level)

theorem isBaseChangeOf_and_hasBaseChangeLevelLaw_iff (𝔡 : Ideal (𝓞 L))
    (π : HeckeEigensystem E R) (Φ : HeckeEigensystem L R) :
    (IsBaseChangeOf π Φ ∧ HasBaseChangeLevelLaw 𝔡 π Φ) ↔
      ((∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S,
          Φ.localLFactor 𝔓 =
            heckeLFactorPoly
              (satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
                (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))))
              ((π.b (𝔓.under (𝓞 E))) ^
                ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal))) ∧
        Φ.level ∣ 𝔡 * Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level) :=
  and_congr (isBaseChangeOf_iff_localLFactor π Φ) Iff.rfl

end ConductorCarrier

end AutomorphicForm

end


