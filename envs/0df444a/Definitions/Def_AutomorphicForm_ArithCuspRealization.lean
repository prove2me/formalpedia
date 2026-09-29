-- Prove2me | Definitions.Def_AutomorphicForm_ArithCuspRealization
-- name    : AutomorphicForm_ArithCuspRealization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/aeb4e9ef-4a69-58b3-8d9a-f0d09bc9f93a
-- title:
--   Arithmetically normalised cuspidal realizability of Hecke eigensystems
-- statement:
--   For a number field $F$ the module first sets up a rescaling of the central (determinant) eigenvalues of a Hecke eigensystem. Here `cNorm v` is the absolute norm $N(v)=\#(\mathcal O_F/v)$ of a height-one prime $v$ of $\mathcal O_F$, viewed in $\mathbb C$; it is nonzero since $v\neq 0$. Given $\Phi=(\text{level},a,b)$ with values in $\mathbb C$, `toRawCentral` keeps the level and the eigenvalues $a_v$ and replaces $b_v$ by $N(v)^{-1}b_v$, while `ofRawCentral` replaces $b_v$ by $N(v)\,b_v$. The accompanying lemmas record the component formulas, that the two maps are mutually inverse (hence `toRawCentral` is injective), and that agreement of two eigensystems outside a finite set of primes is both preserved and reflected by `toRawCentral` (reflection uses invertibility of $N(v)$ in $\mathbb C$).
--
--   On this the arithmetic cuspidality predicate is defined: for a bundle `pins` of carrier data (measurable structure and measure on $\mathrm{GL}_2$ of the adeles, a fundamental-domain set, a central subgroup, level subgroups $U(N)$, local Hecke generators, and a measure on the adeles) one sets $\texttt{IsArithCuspRealizable}\,F\,\texttt{pins}\,\Phi:=\texttt{IsSmoothCuspRealizable}\,F\,\texttt{pins}\,\Phi.\texttt{toRawCentral}$, i.e. the nonemptiness of the project's structure `SmoothCuspRealizationAt` for the rescaled eigensystem: a nonzero function $\varphi$ on $\mathrm{GL}_2(\mathbb A_F)$ with a central character on `pins.Z`, which is cuspidal, $L^2$ on the chosen domain and smooth for the finite part, right invariant under `pins.U Φ.level`, and which outside some finite set of primes is a Hecke eigenfunction with eigenvalue $a_v$ for a system of $N(v)+1$ cosets in the double coset of `pins.gen v`, with the centre acting through $\det(\texttt{pins.gen}\,v)$ by $N(v)^{-1}b_v$. Thus realizability is a predicate on a chosen adelic model, not an intrinsic notion. The remaining declarations are formal consequences: the unfolding iff, the inverse reformulation via `ofRawCentral`, a version `IsArithCuspRealizableVia` for an eigensystem over any commutative ring together with a ring homomorphism to $\mathbb C$ (apply the predicate to the pushed-forward eigensystem), the packaging `arithCuspNotionOf` of the predicate, uniform in $F$, as a `CuspidalityNotion ℂ`, and a congruence statement `IsArithCuspRealizable.congr` which takes as an explicit hypothesis a transport principle for `IsSmoothCuspRealizable` along equality of levels and agreement away from a finite set, and deduces the corresponding transport for the arithmetic predicate.
--
--   **Relation to Mathlib.** Mathlib has no notion of adelic Hecke eigensystems or of cuspidal automorphic realizations; these are the project's own. Only `Ideal.absNorm` is taken from Mathlib, coerced to $\mathbb C$ as `cNorm`.
--
--   **Where it is used.** The predicate produced here is the cuspidality notion fed into the project's base-change and descent framework for Hecke eigensystems ($\texttt{IsBaseChangeOf}$, $\texttt{satakePow}$, $\texttt{DescentPackage}$), where the arithmetic normalisation of the central eigenvalues $b_v$ is the one for which the Satake relations are stated. That framework supports the cyclic base change and descent steps used in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArithCuspRealization.lean

import Definitions.Def_AutomorphicForm_SmoothCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F]

def cNorm (v : HeightOneSpectrum (𝓞 F)) : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem cNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : cNorm v ≠ 0 := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  rw [cNorm, Ne, Nat.cast_eq_zero]
  exact hN

def toRawCentral (Φ : HeckeEigensystem F ℂ) : HeckeEigensystem F ℂ where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := Φ.a
  b := fun v => (cNorm v)⁻¹ * Φ.b v

def ofRawCentral (Ψ : HeckeEigensystem F ℂ) : HeckeEigensystem F ℂ where
  level := Ψ.level
  level_ne_bot := Ψ.level_ne_bot
  a := Ψ.a
  b := fun v => cNorm v * Ψ.b v

@[simp] theorem toRawCentral_level (Φ : HeckeEigensystem F ℂ) : Φ.toRawCentral.level = Φ.level := rfl
@[simp] theorem toRawCentral_a (Φ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Φ.toRawCentral.a v = Φ.a v := rfl
@[simp] theorem toRawCentral_b (Φ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Φ.toRawCentral.b v = (cNorm v)⁻¹ * Φ.b v := rfl
@[simp] theorem ofRawCentral_level (Ψ : HeckeEigensystem F ℂ) : Ψ.ofRawCentral.level = Ψ.level := rfl
@[simp] theorem ofRawCentral_a (Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Ψ.ofRawCentral.a v = Ψ.a v := rfl
@[simp] theorem ofRawCentral_b (Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Ψ.ofRawCentral.b v = cNorm v * Ψ.b v := rfl

@[simp] theorem ofRawCentral_toRawCentral (Φ : HeckeEigensystem F ℂ) :
    Φ.toRawCentral.ofRawCentral = Φ := by
  cases Φ with
  | mk level hl a b =>
    simp only [toRawCentral, ofRawCentral, mk.injEq, true_and]
    funext v
    rw [← mul_assoc, mul_inv_cancel₀ (cNorm_ne_zero v), one_mul]

@[simp] theorem toRawCentral_ofRawCentral (Ψ : HeckeEigensystem F ℂ) :
    Ψ.ofRawCentral.toRawCentral = Ψ := by
  cases Ψ with
  | mk level hl a b =>
    simp only [toRawCentral, ofRawCentral, mk.injEq, true_and]
    funext v
    rw [← mul_assoc, inv_mul_cancel₀ (cNorm_ne_zero v), one_mul]

theorem toRawCentral_injective : Function.Injective (toRawCentral (F := F)) := fun Φ Φ' h => by
  rw [← ofRawCentral_toRawCentral Φ, h, ofRawCentral_toRawCentral]

theorem AgreesAwayFromFinite.toRawCentral {Φ Φ' : HeckeEigensystem F ℂ}
    (h : AgreesAwayFromFinite Φ Φ') : AgreesAwayFromFinite Φ.toRawCentral Φ'.toRawCentral := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1, congrArg ((cNorm v)⁻¹ * ·) (hS v hv).2⟩⟩

theorem AgreesAwayFromFinite.of_toRawCentral {Φ Φ' : HeckeEigensystem F ℂ}
    (h : AgreesAwayFromFinite Φ.toRawCentral Φ'.toRawCentral) : AgreesAwayFromFinite Φ Φ' := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv =>
    ⟨(hS v hv).1, mul_left_cancel₀ (inv_ne_zero (cNorm_ne_zero v)) (hS v hv).2⟩⟩

end HeckeEigensystem

variable (F : Type) [Field F] [NumberField F]

def IsArithCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsSmoothCuspRealizable F pins Φ.toRawCentral

theorem isArithCuspRealizable_iff (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsArithCuspRealizable F pins Φ ↔ Nonempty (SmoothCuspRealizationAt F pins Φ.toRawCentral) :=
  Iff.rfl

theorem isSmoothCuspRealizable_iff_isArithCuspRealizable_ofRawCentral (pins : CarrierPins F)
    (Ψ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizable F pins Ψ ↔ IsArithCuspRealizable F pins Ψ.ofRawCentral := by
  unfold IsArithCuspRealizable; rw [HeckeEigensystem.toRawCentral_ofRawCentral]

def IsArithCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsArithCuspRealizable F pins (Φ.map ι)

theorem isArithCuspRealizableVia_id (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsArithCuspRealizableVia F pins (RingHom.id ℂ) Φ ↔ IsArithCuspRealizable F pins Φ := by
  unfold IsArithCuspRealizableVia; rw [HeckeEigensystem.map_id]

def arithCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => @IsArithCuspRealizable F _i1 _i2 (pins F) Φ

theorem arithCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (arithCuspNotionOf pins).IsCusp F Φ ↔ IsArithCuspRealizable F (pins F) Φ := Iff.rfl

variable {F}

theorem IsArithCuspRealizable.congr {pins : CarrierPins F} {Φ Φ' : HeckeEigensystem F ℂ}
    (transport : ∀ Ψ Ψ' : HeckeEigensystem F ℂ, Ψ'.level = Ψ.level →
      HeckeEigensystem.AgreesAwayFromFinite Ψ Ψ' →
        IsSmoothCuspRealizable F pins Ψ → IsSmoothCuspRealizable F pins Ψ')
    (hlev : Φ'.level = Φ.level) (hagree : HeckeEigensystem.AgreesAwayFromFinite Φ Φ')
    (h : IsArithCuspRealizable F pins Φ) : IsArithCuspRealizable F pins Φ' :=
  transport Φ.toRawCentral Φ'.toRawCentral hlev hagree.toRawCentral h

end AutomorphicForm

end


