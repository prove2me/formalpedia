-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:31.416649+00:00
-- url     : https://prove2.me/theorems/87b53a18-73f3-4656-aa08-59923052da11
-- title:
--   Types Defs
-- statement:
--   Definitions and structural lemmas for Types Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
namespace Formalism.L2.NT
open Formalism.L2.Host
def plOver (L : Fld) (p : ℕ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {v | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}
def SplitsIn (L : Fld) (p : ℕ) : Prop :=
  (plOver L p).ncard = Module.finrank ℚ L
def IsRayPrime (K : Fld) (m p : ℕ) : Prop :=
  p.Prime ∧ ∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (m : Qb)) ∧
    ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)
def RayAdm (K : Fld) (m : ℕ) (L : Fld) : Prop :=
  K ≤ L ∧ FiniteDimensional ℚ L ∧ ∀ p, IsRayPrime K m p → SplitsIn L p
def rayField (K : Fld) (m : ℕ) : Fld := ⨆ (L : Fld) (_ : RayAdm K m L), L
def RayCFT (K : Fld) (m : ℕ) : Prop := RayAdm K m (rayField K m)
def IsTeich {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (t : Formalism.CyclotomicNorms.Fbar p →* Ω) : Prop :=
  ∀ x, ∃ h : t x ∈ A, κ (IsLocalRing.residue A ⟨t x, h⟩) = x
def redThrough {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (z : Ω) : Formalism.CyclotomicNorms.Fbar l :=
  open Classical in if h : z ∈ B then κ (IsLocalRing.residue B ⟨z, h⟩) else 0
section Red
variable {Ω : Type} [Field Ω]
variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)
end Red
def degSer {G : Type} [Group G] {g : ℕ} (f₀ : (ZMod g)[X]) (f : (ZMod g)[X]) : MonoidAlgebra ℂ G :=
  open Classical in if f = f₀ then 1 else 0
section Series
def ipG {G : Type} [Fintype G] (χ ψ : G → ℂ) : ℂ := ∑ x, χ x * star (ψ x)
def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)
def IsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  IsChar χ ∧ ipG χ χ = (Fintype.card G : ℂ)
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
def unipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}
def IsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  IsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open Classical in if u ∈ (unipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0
def offs {m : ℕ} (c : Fin m → ℕ) (i : Fin m) : ℕ := ∑ j : Fin m, if j < i then c j else 0
def IsBaseBlockVar {m : ℕ} (c : Fin m → ℕ) (i : Fin m) (x : ℕ) : Prop := offs c i ≤ x ∧ x < offs c i + c i
def IsParab {m r : ℕ} (c : Fin m → ℕ) (p : GL (Fin r) F) : Prop :=
  ∀ (x y : Fin r) (i j : Fin m), IsBaseBlockVar c i x.val → IsBaseBlockVar c j y.val → j < i →
    (p : Matrix (Fin r) (Fin r) F) x y = 0
def blkOf {m r : ℕ} (c : Fin m → ℕ) (i : Fin m) (M : Matrix (Fin r) (Fin r) F) :
    Matrix (Fin (c i)) (Fin (c i)) F :=
  fun a b => if h : offs c i + a.val < r ∧ offs c i + b.val < r then M ⟨_, h.1⟩ ⟨_, h.2⟩ else 0
def onMat {n : ℕ} (χ : GL (Fin n) F → ℂ) (M : Matrix (Fin n) (Fin n) F) : ℂ :=
  open Classical in if h : IsUnit M then χ h.unit else 0
def eOf {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun x => χ 1 / (Fintype.card G : ℂ) * χ x⁻¹)
variable {g : ℕ} [Fact g.Prime]
def GreenAt (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) {d : ℕ} (χ : GL (Fin d) (ZMod g) → ℂ) (k : ℕ) : Prop :=
  ∀ x : GL (Fin d) (ZMod g), Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g))) →
    χ x = (-1) ^ (d - 1) *
      ((Formalism.CyclotomicNorms.rootsBar (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g)))).map fun α => teich α ^ k).sum
def IsGenSys (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) : Prop :=
  ∀ d, 0 < d → orderOf (ζ d) = g ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d
def labCusp (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (d k : ℕ) : (ZMod g)[X] := minpoly (ZMod g) (ζ d ^ k)
def InSeries (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) {r : ℕ} (χ : GL (Fin r) (ZMod g) → ℂ)
    (f : (ZMod g)[X]) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℕ) (χs : ∀ i, GL (Fin (c i)) (ZMod g) → ℂ) (ks : Fin m → ℕ),
    (∀ i, 0 < c i) ∧ ∑ i, c i = r ∧
    (∀ i, IsCuspChar (χs i) ∧ GreenAt teich (χs i) (ks i) ∧ (labCusp ζ (c i) (ks i)).natDegree = c i) ∧
    ∏ i, labCusp ζ (c i) (ks i) = f ∧
    ∑ p : GL (Fin r) (ZMod g),
      (open Classical in if IsParab c p then χ p * star (∏ i, onMat (χs i) (blkOf (r := r) c i (p : Matrix (Fin r) (Fin r) (ZMod g)))) else 0) ≠ 0
def CuspGreenUnique (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) : Prop :=
  ∀ (d k : ℕ) (χ χ' : GL (Fin d) (ZMod g) → ℂ), IsCuspChar χ → IsCuspChar χ' →
    GreenAt teich χ k → GreenAt teich χ' k → χ = χ'
def eSerC (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (r : ℕ) (f : (ZMod g)[X]) :
    MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
  ∑ᶠ (χ : GL (Fin r) (ZMod g) → ℂ) (_ : IsIrrChar χ ∧ InSeries teich ζ χ f), eOf χ
end Series
section SeriesLemmas
variable {g : ℕ} [Fact g.Prime]
end SeriesLemmas
section SeriesTriv
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {g : ℕ} [Fact g.Prime]
end SeriesTriv
section TameChar
def TameCoupled {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (σ : Ω ≃ₐ[E] Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p) : Prop :=
  ∀ d, 0 < d → ∀ y : Ω, y ^ (p ^ d - 1) = (p : Ω) → redThrough A κ (σ y / y) = ζ d
end TameChar
section SeriesAut
variable {g : ℕ} [Fact g.Prime]
def toZModAlgEquiv (φ : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g) : Formalism.CyclotomicNorms.Fbar g ≃ₐ[ZMod g] Formalism.CyclotomicNorms.Fbar g :=
  { φ with
    commutes' := fun r => by
      have h := RingHom.ext_zmod ((φ : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g).comp (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))
        (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))
      exact congrArg (fun f : ZMod g →+* Formalism.CyclotomicNorms.Fbar g => f r) h }
end SeriesAut
end Formalism.L2.NT


