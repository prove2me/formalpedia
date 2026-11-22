-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
-- name    : Formalism_LocalToGlobal_Divisibility_Tuples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:20.935947+00:00
-- url     : https://prove2.me/theorems/1818f688-f8be-4194-9d3f-dc3df9aeaa4b
-- title:
--   Tuples
-- statement:
--   Definitions and structural lemmas for Tuples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/Tuples.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
namespace Formalism.L2.DIV
def kills {G : Type} (A : Type) [Group G] [CommGroup A] (H : Subgroup G) : Subgroup (G →* A) where
  carrier := {ξ | H ≤ ξ.ker}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {a b} ha hb x hx => by
    have h1 := ha hx
    have h2 := hb hx
    rw [MonoidHom.mem_ker] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, h1, h2, one_mul]
  inv_mem' := fun {a} ha x hx => by
    have h1 := ha hx
    rw [MonoidHom.mem_ker] at h1 ⊢
    rw [MonoidHom.inv_apply, h1, inv_one]
section Ideles
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
abbrev AfE : Type := E ⊗[F] FiniteAdeleRing (𝓞 F) F
abbrev RInt : Subring (AfE F E) := tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
def ratId : Eˣ →* (AfE F E)ˣ := Units.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
def idF : (FiniteAdeleRing (𝓞 F) F)ˣ →* (AfE F E)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] AfE F E).toRingHom.toMonoidHom
def intU : Subgroup (AfE F E)ˣ := (RInt F E).toSubmonoid.units
def congU (I : Ideal (RInt F E)) : Subgroup (AfE F E)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker.map (Units.map (RInt F E).subtype.toMonoidHom)
def congN (N : ℕ) : Subgroup (AfE F E)ˣ := congU F E (Ideal.span {(N : RInt F E)})
variable {F}
def suppAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup (AfE F E)ˣ :=
  ⨅ (v' : HeightOneSpectrum (𝓞 F)) (_ : v' ≠ v), (Units.map (prV (E := E) v').toMonoidHom).ker
def inertAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup (AfE F E)ˣ := intU F E ⊓ suppAt E v
def wildAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup (AfE F E)ˣ :=
  congU F E (Ideal.span {((plc v : ℕ) : RInt F E)}).radical ⊓ suppAt E v
def SplitAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal
variable {E} in

def DegOne (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (Ideal.absNorm v.asIdeal).Prime ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∉ v.asIdeal ^ 2
def GoodPl (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Prop := SplitAt E v ∧ DegOne v ∧ plc v ∉ S
end Ideles
theorem mem_kerRed {R : Type} [CommRing R] (I : Ideal R) (u : Rˣ) :
    u ∈ (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker ↔ (u : R) - 1 ∈ I := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  simp
section Chars
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem congU_mono {I J : Ideal (RInt F E)} (h : I ≤ J) : congU F E I ≤ congU F E J := by
  apply Subgroup.map_mono
  intro u hu
  rw [mem_kerRed] at hu ⊢
  exact h hu
theorem congN_dvd {M N : ℕ} (h : M ∣ N) : congN F E N ≤ congN F E M := by
  apply congU_mono
  rw [Ideal.span_singleton_le_span_singleton]
  exact_mod_cast (Nat.cast_dvd_cast (α := RInt F E) h)
variable (L : Type) [Field L]
abbrev Chr : Type := (AfE F E)ˣ →* Lˣ
def openChr : Subgroup (Chr F E L) where
  carrier := {ξ | ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker}
  one_mem' := ⟨1, Nat.one_pos, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    exact ⟨M * N, Nat.mul_pos hM hN,
      (kills Lˣ (congN F E (M * N))).mul_mem ((congN_dvd F E (Dvd.intro _ rfl)).trans ha)
        ((congN_dvd F E (Dvd.intro_left _ rfl)).trans hb)⟩
  inv_mem' := by
    rintro a ⟨M, hM, ha⟩
    exact ⟨M, hM, (kills Lˣ (congN F E M)).inv_mem ha⟩
def finChar : Subgroup (Chr F E L) :=
  kills Lˣ (ratId F E).range ⊓ openChr F E L ⊓ CommGroup.torsion (Chr F E L)
abbrev FinChar : Type := ↥(finChar F E L)
def tupGrp (S : Set ℕ) : Subgroup (Chr F E L) :=
  finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : ¬ GoodPl E S v), kills Lˣ (inertAt E v)
def hostS (q d g₁ g₂ : ℕ) (T : Set ℕ) : Set ℕ := {2, q, d, g₁, g₂} ∪ T
abbrev Tup (S : Set ℕ) : Type := ↥(tupGrp F E L S)
def mu0 (S : Set ℕ) : Tup F E L S := 1
end Chars
section Ram
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
def Qprime (ξ : Chr F E L) : Set (HeightOneSpectrum (𝓞 F)) := {v | ¬ inertAt E v ≤ ξ.ker}
def QprimeN (ξ : Chr F E L) : Set ℕ := plc '' Qprime ξ
def InertOrd (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Prop :=
  ∀ m : ℕ, (∀ x ∈ inertAt E v, ξ x ^ m = 1) ↔ n ∣ m
def TrivAt (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) : Prop := suppAt E v ≤ ξ.ker
def IsBaseChar (p : ℕ) (δ : Chr F E L) : Prop :=
  p.Prime ∧ ∀ v : HeightOneSpectrum (𝓞 F), (plc v = p → InertOrd δ v 15) ∧ (plc v ≠ p → v ∉ Qprime δ)
def IsTwistChar (l : ℕ) (ψ : Chr F E L) : Prop :=
  (∃ k : ℕ, ψ ^ l ^ k = 1) ∧ ∀ v : HeightOneSpectrum (𝓞 F), plc v = l → TrivAt ψ v
variable (F E) in

def toRInt : 𝓞 E →+* RInt F E :=
  ((inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap (𝓞 E) E)).codRestrict (RInt F E)
    fun b => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, rfl⟩)
def IsResChar (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
  ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
    (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
    (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
    ξ (Units.map (RInt F E).subtype.toMonoidHom u) = χ a
open Classical in

def resChar (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ :=
  if h : ∃ χ, IsResChar ξ P χ then h.choose else 1
def resDet (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) : GL (Fin n) (𝓞 E ⧸ P.asIdeal) →* Lˣ :=
  (resChar ξ P).comp Matrix.GeneralLinearGroup.det
end Ram
section Tilde
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
def conjId (σ : E →ₐ[F] E) : (AfE F E)ˣ →* (AfE F E)ˣ :=
  Units.map (sigR σ (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
def h90 (σ : E →ₐ[F] E) : (AfE F E)ˣ →* (AfE F E)ˣ := MonoidHom.id _ / conjId σ
def U1 (σ : E →ₐ[F] E) : Subgroup (AfE F E)ˣ := (MonoidHom.id _ * conjId σ).ker
open Classical in

def tilde (σ : E →ₐ[F] E) (ξ : Chr F E L) : (h90 σ).range →* Lˣ :=
  if h : (h90 σ).ker ≤ ξ.ker then
    (h90 σ).rangeRestrict.liftOfSurjective (h90 σ).rangeRestrict_surjective
      ⟨ξ, by rw [MonoidHom.ker_rangeRestrict]; exact h⟩
  else 1
open Classical in

def detTw (σ : E →ₐ[F] E) (ξ : Chr F E L) {n : ℕ} (g : GL (Fin n) (AfE F E)) : Lˣ :=
  if h : Matrix.GeneralLinearGroup.det g ∈ (h90 σ).range then tilde σ ξ ⟨_, h⟩ else 1
end Tilde
section Maps
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}
def IsTupleMap (muAt : HeightOneSpectrum (𝓞 K) → Tup F E K S) : Prop :=
  (∀ w, muAt (conjPl w) = muAt w) ∧ {w | muAt w ≠ mu0 F E K S}.Finite ∧
    ∀ w, plc w ∉ QprimeN (muAt w : Chr F E K)
def deAt (p : ℕ) (δ0 δ0' : Tup F E K S) (w : HeightOneSpectrum (𝓞 K)) : Tup F E K S :=
  if plc w = p then δ0' else δ0
def muTw (p : ℕ) (δ0 δ0' : Tup F E K S) (ψ : HeightOneSpectrum (𝓞 K) → Tup F E K S)
    (w : HeightOneSpectrum (𝓞 K)) : Tup F E K S := deAt p δ0 δ0' w * ψ w
structure IsTupleMapTW (p p' : ℕ) (δ0 δ0' : Tup F E K S) (ψ : HeightOneSpectrum (𝓞 K) → Tup F E K S)
    (avoid : HeightOneSpectrum (𝓞 K) → Set (HeightOneSpectrum (𝓞 F)))
    (muAt : HeightOneSpectrum (𝓞 K) → Tup F E K S) : Prop where
  ne : p ≠ p'
  base : IsBaseChar p (δ0 : Chr F E K)
  base' : IsBaseChar p' (δ0' : Chr F E K)
  psi_conj : ∀ w, ψ (conjPl w) = ψ w
  psi_tw : ∀ w, IsTwistChar (plc w) (ψ w : Chr F E K)
  psi_Q : ∀ w, ∀ v ∈ Qprime (ψ w : Chr F E K), plc v ≠ plc w ∧ plc v ≠ p ∧ plc v ≠ p' ∧ v ∉ avoid w
  conj : ∀ w, muAt (conjPl w) = muAt w
  fin : {w | muAt w ≠ mu0 F E K S}.Finite
  ref_or_tw : ∀ w, (muAt w = mu0 F E K S ∧ ψ w = 1) ∨ muAt w = muTw p δ0 δ0' ψ w
def PsiFromBelow {K0 : Type} [Field K0] [NumberField K0] [Algebra K0 K]
    (ψ0 : HeightOneSpectrum (𝓞 K0) → Tup F E K S) (ψ : HeightOneSpectrum (𝓞 K) → Tup F E K S) : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K0)), w'.asIdeal.under (𝓞 K0) = w.asIdeal →
    ∃ a : ℕ, a.Coprime (plc w') ∧ ψ w' = ψ0 w ^ a
end Maps
section Ref
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
structure IsMu0 (σ : E →ₐ[F] E) (Ψ : Finset (E →+* L)) (e : (E →+* L) → ℤ) (G : Set ℕ) (μ : Chr F E L) : Prop where
  isOpen : μ ∈ openChr F E L
  rat : ∀ a : Eˣ, ((μ (ratId F E a) : Lˣ) : L) = ∏ τ ∈ Ψ, (τ (a : E) / τ (σ (a : E))) ^ e τ
  trivF : (idF F E).range ≤ μ.ker
  tame : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ μ.ker
  ram : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ Qprime μ ↔ plc v ∈ G
def chiOf (μ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ := (resChar μ P)⁻¹
def TameAtG {m : ℕ} (g : ℕ) (om : (ZMod g)ˣ →* Lˣ) (rd : Set (HeightOneSpectrum (𝓞 E)))
    (μ : Fin m → Chr F E L) : Prop :=
  Function.Injective om ∧ ∀ P ∈ rd, plc P = g →
    ∀ (j : Fin m) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (u : (ZMod g)ˣ) (n : ℤ),
      (a : 𝓞 E ⧸ P.asIdeal) = (n : 𝓞 E ⧸ P.asIdeal) → (u : ZMod g) = (n : ZMod g) →
      chiOf (μ j) P a = om u ^ (2 * (j.val + 1))
def tupleOf {m : ℕ} {S : Set ℕ} (μ : Fin m → Chr F E L) (ξ : Tup F E L S) : Fin m → Chr F E L :=
  fun j => μ j * (ξ : Chr F E L)
end Ref
end Formalism.L2.DIV
end


