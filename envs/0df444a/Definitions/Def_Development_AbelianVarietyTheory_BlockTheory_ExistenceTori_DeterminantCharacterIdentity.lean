-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeterminantCharacterIdentity
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeterminantCharacterIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:08.420662+00:00
-- url     : https://prove2.me/theorems/fab137f2-9746-490c-9833-fe0a228a48ad
-- title:
--   Determinant Character Identity
-- statement:
--   Definitions and structural lemmas for Determinant Character Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/DeterminantCharacterIdentity.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight MvPolynomial
open scoped nonZeroDivisors Classical
section Minors
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (R : Type) [CommRing R]
def ColsDisjoint (col : ∀ σ : T, Fin (r σ) → Fin n) : Prop :=
  Function.Injective fun x : (Σ σ : T, Fin (r σ)) => col x.1 x.2
def leadMinor (col : ∀ σ : T, Fin (r σ) → Fin n) (σ : T) (i : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  Matrix.det (Matrix.of fun s t : Fin (i.val + 1) =>
    (X ⟨σ, Fin.castLE (Nat.succ_le_of_lt i.isLt) s, col σ (Fin.castLE (Nat.succ_le_of_lt i.isLt) t)⟩ :
      MvPolynomial (Letter T r n) R))
def RowDom (a : T × ℕ → ℕ) : Prop := ∀ (σ : T) (i j : ℕ), i ≤ j → j < r σ → a (σ, j) ≤ a (σ, i)
def gap (a : T × ℕ → ℕ) (σ : T) (i : Fin (r σ)) : ℕ :=
  a (σ, i.val) - if i.val + 1 < r σ then a (σ, i.val + 1) else 0
def minorProd (col : ∀ σ : T, Fin (r σ) → Fin n) (a : T × ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ : T, ∏ i : Fin (r σ), leadMinor r n R col σ i ^ gap r a σ i
def diagExp (col : ∀ σ : T, Fin (r σ) → Fin n) (a : T × ℕ → ℕ) : Letter T r n →₀ ℕ :=
  ∑ σ : T, ∑ i : Fin (r σ), Finsupp.single ⟨σ, i, col σ i⟩ (a (σ, i.val))
example (col : ∀ σ : T, Fin (r σ) → Fin n) : minorProd r n R col 0 = 1 := by
  simp [minorProd, gap]
end Minors
section Adelic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
def ratMat (γ : ratPts E n) : Matrix (Fin n) (Fin n) E := fun a b => Classical.choose (γ.2.1 a b)
def conjMat (g : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  fun a b => IsCMField.complexConj E (g a b)
def moveLat (g : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) : GenLat E n where
  La := Λ.La.map ((Matrix.mulVecLin g).restrictScalars (𝓞 E))
def InPlainLat (h : UA E n) (x : Fin n → E) : Prop :=
  ∃ u : Fin n → AdE E, (∀ b, u b ∈ intAd E) ∧ ∀ a, diagE E (x a) = ∑ b, h.1 a b * u b
variable (E n) in

def LatOfClass : Prop :=
  (∀ h : UA E n, (latOf h).Unimod) ∧
  (∀ (h : UA E n) (x : Fin n → E), x ∈ (latOf h).La ↔ InPlainLat h fun a => IsCMField.complexConj E (x a)) ∧
  ∀ (h : UA E n) (γ : ratPts E n), ∀ k ∈ maxCpt E n,
    (latOf (γ.1 * h * k)).La = (moveLat (conjMat (ratMat γ)) (latOf h)).La
def conjId (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)
def overId (v : Plc E) : Ideal (𝓞 E) := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
def PrimeTo (S : Finset (Plc E)) (𝔞 : Ideal (𝓞 E)) : Prop := 𝔞 ≠ ⊥ ∧ ∀ v ∈ S, 𝔞 ⊔ overId v = ⊤
def IsDetIdeal (H : Host E) (h : UA E n) (𝔠 : Ideal (𝓞 E)) : Prop :=
  𝔠 ⊔ conjId H 𝔠 = ⊤ ∧
    𝔠 • Submodule.span (𝓞 E) (detSet (latOf h).La) = conjId H 𝔠 • (1 : Submodule (𝓞 E) E)
def DetIdealExists (H : Host E) (n r : ℕ) : Prop :=
  Odd r → ∀ h : UA E n, (∃! x : Ideal (𝓞 E) × ℕ, IsDetIdeal H h x.1 ∧ x.2 ^ 2 * Ideal.absNorm x.1 = normH r h) ∧
    normH r h ≠ 0 ∧ ∀ (S : Finset (Plc E)) (𝔠 : Ideal (𝓞 E)), TrivOn S h → IsDetIdeal H h 𝔠 → PrimeTo S 𝔠
end Adelic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def HidaSetting (Dw : Datum H) (n : ℕ) : Prop := IsGalois ℚ E ∧ Even n ∧ Odd (Dw.p + Dw.q)
def push {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB c ℓ.1 ℓ.2.1 (fun k => g k ℓ.2.2)
example {n : ℕ} (g : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (j : Fin n) :
    push c g (X (⟨σ, i, j⟩ : LtN Dw n)) = ∑ k, C (embF c σ (g k j)) * X (⟨σ, i, k⟩ : LtN Dw n) := by
  simp [push, letB]
def pushRat {n : ℕ} (γ : ratPts E n) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  push c (conjMat (ratMat γ))
def harmSp (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
def topPoly {n : ℕ} (col : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n) (a : (E →+* ℂ) × ℕ → ℕ) :
    MvPolynomial (LtN Dw n) c.F := minorProd Dw.mult n c.F col a
def TopPolyHarm (Dw : Datum H) (n : ℕ) : Prop :=
  ∀ (col : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n) (a : (E →+* ℂ) × ℕ → ℕ),
    ColsDisjoint Dw.mult n col → RowDom Dw.mult a →
      topPoly c col a = map (Int.castRingHom c.F) (minorProd Dw.mult n ℤ col a) ∧
      topPoly c col a ∈ harmA c a n ∧ topPoly c col a ∈ harmL c (⟨stdLat E n⟩ : GenLat E n) a ∧
      (topPoly c col a).coeff (diagExp Dw.mult n col a) = 1
def PushHarm (Dw : Datum H) (n : ℕ) : Prop :=
  (∀ g g' : Matrix (Fin n) (Fin n) E, push (Dw := Dw) c (g * g') = (push c g).comp (push c g')) ∧
  ∀ (γ : ratPts E n) (a : (E →+* ℂ) × ℕ → ℕ),
    pushRat c γ '' harmSp c Dw a n = harmSp c Dw a n ∧
    (∀ Λ : GenLat E n, pushRat (Dw := Dw) c γ '' harmL c Λ a = harmL c (moveLat (conjMat (ratMat γ)) Λ) a) ∧
    ∀ h : UA E n, ∀ k ∈ maxCpt E n,
      pushRat (Dw := Dw) c γ '' harmL c (latOf h) a = harmL c (latOf (γ.1 * h * k)) a
def psiSet (H : Host E) : Finset (E →+* ℂ) := Finset.univ.filter (InPsi H)
def idK (τ : E →+* ℂ) (𝔞 : Ideal (𝓞 E)) : FractionalIdeal (𝓞 c.F)⁰ c.F :=
  ((𝔞.map (RingOfIntegers.mapRingHom (embF c τ)) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F)
def infType (nt : (E →+* ℂ) → ℤ) (z : 𝓞 E) : c.F :=
  ∏ τ ∈ psiSet H, embK c τ z ^ nt τ * embK c τ (H.bar z) ^ (1 - nt τ)
def IsHecke (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) : Prop :=
  B ⊤ = 1 ∧ (∀ 𝔞 𝔟, PrimeTo S 𝔞 → PrimeTo S 𝔟 → B (𝔞 * 𝔟) = B 𝔞 * B 𝔟) ∧
  (∀ 𝔞, PrimeTo S 𝔞 → ∀ s : c.F →+* ℂ, ‖s (B 𝔞)‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ)) ∧
  (∀ 𝔞, PrimeTo S 𝔞 → FractionalIdeal.spanSingleton (𝓞 c.F)⁰ (B 𝔞) =
    ∏ τ ∈ psiSet H, idK c τ 𝔞 ^ nt τ * idK c τ (conjId H 𝔞) ^ (1 - nt τ)) ∧
  (∃ m : ℕ, ∀ z : 𝓞 E, PrimeTo S (Ideal.span {z}) → z - 1 ∈ (∏ v ∈ S, overId v) ^ m →
    B (Ideal.span {z}) = infType c nt z) ∧
  ∀ v : Plc E, v ∉ S →
    B (overId v) = (if (overId v).IsPrime then -1 else 1) * (Ideal.absNorm v.asIdeal : c.F)
def Unram (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) : Prop :=
  ∀ z : 𝓞 E, PrimeTo S (Ideal.span {z}) → B (Ideal.span {z}) = infType c nt z
def UnitaryPart (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (χ : Ideal (𝓞 E) → ℂˣ) : Prop :=
  ∀ 𝔞, PrimeTo S 𝔞 → (χ 𝔞 : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔞 : ℝ) : ℝ) : ℂ) = (B 𝔞 : ℂ)
def ValueAt (Dw : Datum H) (B : Ideal (𝓞 E) → c.F) {n : ℕ} (h : UA E n) (κ : c.F) : Prop :=
  ∃ (𝔠 : Ideal (𝓞 E)) (m : ℕ), IsDetIdeal H h 𝔠 ∧ m ^ 2 * Ideal.absNorm 𝔠 = normH (Dw.p + Dw.q) h ∧
    (κ * B 𝔠 * (m : c.F) = 1 ∨ κ * B 𝔠 * (m : c.F) = -1) ∧
    (SplitSupp H (latOf h) → κ * B 𝔠 * (m : c.F) = 1)
def ValueLaw (Dw : Datum H) (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) {n : ℕ} (ep : UA E n → ℂ) : Prop :=
  ∀ h : UA E n, TrivOn S h → ∃ κ : c.F, IsScalar (Dw := Dw) c ep h κ ∧ ValueAt c Dw B h κ
def ScalarAbs (Dw : Datum H) {n : ℕ} (h : UA E n) (κ : c.F) : Prop :=
  ∀ s : c.F →+* ℂ, ‖s κ‖ ^ 2 * (normH (Dw.p + Dw.q) h : ℝ) = 1
def IsBeta (Dw : Datum H) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β
def expE (Dw : Datum H) (nt : (E →+* ℂ) → ℤ) (τ : E →+* ℂ) : ℤ := (1 + (Dw.p : ℤ) - (Dw.q : ℤ)) / 2 - nt τ
def twistId (d : (E →+* ℂ) → ℤ) (𝔠 : Ideal (𝓞 E)) : FractionalIdeal (𝓞 c.F)⁰ c.F :=
  ∏ τ ∈ psiSet H, (idK c τ 𝔠 / idK c τ (conjId H 𝔠)) ^ d τ
def detChar (d : (E →+* ℂ) → ℤ) {n : ℕ} (γ : ratPts E n) : c.F :=
  ∏ τ ∈ psiSet H, embF c τ (ratMat γ).det ^ d τ
def ScalarFacts (Dw : Datum H) (n : ℕ) : Prop :=
  Odd (Dw.p + Dw.q) → ∀ (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ), IsHecke c S B nt →
    (∀ (χ : Ideal (𝓞 E) → ℂˣ) (ep : UA E n → ℂ), UnitaryPart c S B χ → ScalarPin H S χ ep → ValueLaw c Dw S B ep) ∧
    ∀ (h : UA E n) (κ : c.F), TrivOn S h → ValueAt c Dw B h κ →
      ScalarAbs c Dw h κ ∧ (∀ ep : UA E n → ℂ, IsScalar (Dw := Dw) c ep h κ → ‖ep h‖ = 1) ∧
      ∀ β : c.F, IsBeta c Dw (latOf h) β → (∀ s : c.F →+* ℂ, ‖s (κ * β)‖ = 1) ∧
        ∀ 𝔠, IsDetIdeal H h 𝔠 → FractionalIdeal.spanSingleton (𝓞 c.F)⁰ (κ * β) = twistId c (expE Dw nt) 𝔠
section Coeff
variable {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T] [IsScalarTower (𝓞 c.F) c.F T]
def LatLaw (ρ : Representation c.F (ratPts E n) T) (L : UA E n → Submodule (𝓞 c.F) T) : Prop :=
  (∀ h, (L h).FG ∧ Submodule.span c.F (L h : Set T) = ⊤) ∧
  ∀ (h : UA E n) (γ : ratPts E n), ∀ k ∈ maxCpt E n, (L (γ.1 * h * k) : Set T) = ρ γ '' (L h : Set T)
def CoeffTie (a : (E →+* ℂ) × ℕ → ℕ) (d : (E →+* ℂ) → ℤ) (col : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n)
    (ρ : Representation c.F (ratPts E n) T) (L : UA E n → Submodule (𝓞 c.F) T) (v₀ : T)
    (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : Prop :=
  Function.Injective io ∧ Set.range io = harmSp c Dw a n ∧
  (∀ (γ : ratPts E n) (t : T), io (ρ γ t) = detChar c d γ • pushRat c γ (io t)) ∧
  (ColsDisjoint Dw.mult n col ∧ io v₀ = topPoly c col a ∧ ∀ s : c.F, s • v₀ ∈ L 1 ↔ IsIntegral ℤ s) ∧
  ∀ (h : UA E n) (𝔠 : Ideal (𝓞 E)), IsDetIdeal H h 𝔠 → ∀ s ∈ twistId c d 𝔠, ∀ P ∈ harmL c (latOf h) a,
    ∃ t ∈ L h, io t = s • P
def IsForm (J : Subgroup (UA E n)) (ty : J →* c.Fˣ) (ρ : Representation c.F (ratPts E n) T) (f : UA E n → T) : Prop :=
  ∀ (h : UA E n) (γ : ratPts E n) (k : J), f (γ.1 * h * k.1) = ((ty k : c.Fˣ) : c.F) • ρ γ (f h)
def IsIntForm (L : UA E n → Submodule (𝓞 c.F) T) (f : UA E n → T) : Prop := ∀ h, f h ∈ L h
end Coeff
def MovesDatum {n : ℕ} (J : Subgroup (UA E n)) (ψ : J →* c.Fˣ) (ph : (Fin n → ConjQ Dw l) → c.F) : Prop :=
  ∀ (k : J) (κ : Fin n → Fin n → 𝓞 E),
    (∀ a b, ∃ u ∈ intAd E, star (k.1.1 a b) - diagE E (κ a b : E) = (l.M : AdE E) * u) →
      ∀ x, ph (fun a => ∑ b, κ a b • x b) = ((ψ k : c.Fˣ) : c.F) * ph x
example {n : ℕ} (J : Subgroup (UA E n)) (ph : (Fin n → ConjQ Dw l) → c.F) :
    MovesDatum c J 1 ph ↔ FixesDatum c J ph := by
  simp [MovesDatum, FixesDatum]
def RamPart (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) {n : ℕ} (γ : ratPts E n) (w : c.F) :
    Prop :=
  ∃ z : 𝓞 E, PrimeTo S (Ideal.span {z}) ∧ (ratMat γ).det * (H.bar z : E) = (z : E) ∧
    w * infType c nt z = B (Ideal.span {z})
def IsCocycle (Dw : Datum H) (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) {n : ℕ}
    (γ : ratPts E n) (ψk cc : c.F) : Prop :=
  ∃ w, RamPart c S B nt γ w ∧ cc = detChar c (-expE Dw nt) γ * w * ψk
def TypeTie (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) {n : ℕ} (J : Subgroup (UA E n))
    (ψ ty : J →* c.Fˣ) : Prop :=
  ∀ (γ : ratPts E n) (k : J), TrivOn S (γ.1 * k.1) →
    ∃ w, RamPart c S B nt γ w ∧ ((ty k : c.Fˣ) : c.F) = w * ((ψ k : c.Fˣ) : c.F)
def SameClass (H : Host E) (q₁ M : ℕ) (S : Finset (Plc E)) {n : ℕ} (J : Subgroup (UA E n)) (h h' : UA E n) (N N' : ℕ)
    (γ : ratPts E n) (k : J) : Prop :=
  IsLevelGrp J ∧ Covers S (2 * q₁ * H.d * M) ∧ TrivOn S h ∧ TrivOn S h' ∧
    (latOf h).LevOK N M ∧ (latOf h').LevOK N' M ∧ h' = γ.1 * h * k.1
def TermIndep (nab : NabV Xo c) (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h h' : UA E n) (N N' : ℕ) (γ : ratPts E n) (k : J)
    (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) (ψ : J →* c.Fˣ) (ph : (Fin n → ConjQ Dw l) → c.F) (κ κ' cc : c.F)
    (P : MvPolynomial (LtN Dw n) c.F),
    SameClass H q₁ l.M S J h h' N N' γ k → SplitSupp H (latOf h) → SplitSupp H (latOf h') → IsHecke c S B nt →
    ValueAt c Dw B h κ → ValueAt c Dw B h' κ' → MovesDatum c J ψ ph →
    IsCocycle c Dw S B nt γ ((ψ k : c.Fˣ) : c.F) cc → P ∈ harmSp c Dw a n →
      ∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v v' : R),
        ThLaValAt Xo c nab ph (latOf h) N P y v → ThLaValAt Xo c nab ph (latOf h') N' (cc • pushRat c γ P) y v' →
          algebraMap c.F R κ' * v' = algebraMap c.F R κ * v
def ZetaRoot (Dw : Datum H) (q₁ n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h h' : UA E n) (N N' : ℕ) (γ : ratPts E n) (k : J)
    (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) (ψ : J →* c.Fˣ) (κ κ' β β' cc : c.F),
    SameClass H q₁ l.M S J h h' N N' γ k → IsHecke c S B nt → ValueAt c Dw B h κ → ValueAt c Dw B h' κ' →
    IsBeta c Dw (latOf h) β → IsBeta c Dw (latOf h') β' → IsOfFinOrder (ψ k) →
    IsCocycle c Dw S B nt γ ((ψ k : c.Fˣ) : c.F) cc →
      ∃ ζ : c.F, IsOfFinOrder ζ ∧ ζ * (κ' * β' * cc) = κ * β
def ThChange (nab : NabV Xo c) (q₁ n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h h' : UA E n) (N N' : ℕ) (γ : ratPts E n) (k : J)
    (ph : (Fin n → ConjQ Dw l) → c.F) (β β' : c.F),
    SameClass H q₁ l.M S J h h' N N' γ k → FixesDatum c J ph →
    IsBeta c Dw (latOf h) β → IsBeta c Dw (latOf h') β' →
      ∃ ζ : c.F, IsOfFinOrder ζ ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ harmSp c Dw a n,
        ∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v v' : R),
          ShortValAt Xo c nab (fourierSum c ph) (latOf h) β N P y v →
          ShortValAt Xo c nab (fourierSum c ph) (latOf h') β' N' (pushRat c γ P) y v' →
            v' = algebraMap c.F R ζ * v
def thSpan (nab : NabV Xo c) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) (h : UA E n)
    (β : c.F) (N : ℕ) : AddSubgroup (Rul Xo c) :=
  AddSubgroup.closure {g | ∃ (o : 𝓞 c.F) (f : Rul Xo c) (P : MvPolynomial (LtN Dw n) c.F),
    P ∈ harmL c (latOf h) a ∧
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), ShortValAt Xo c nab (fourierSum c ph) (latOf h) β N P y (f p y)) ∧
    ∀ (p : TRing c.F) (y : FrPt Xo c p.R), g p y = algebraMap c.F p.R (o : c.F) * f p y}
def SpanIndep (nab : NabV Xo c) (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h h' : UA E n) (N N' : ℕ) (γ : ratPts E n) (k : J)
    (ph : (Fin n → ConjQ Dw l) → c.F) (β β' : c.F),
    SameClass H q₁ l.M S J h h' N N' γ k → FixesDatum c J ph →
    IsBeta c Dw (latOf h) β → IsBeta c Dw (latOf h') β' →
      thSpan Xo c nab a ph h' β' N' = thSpan Xo c nab a ph h β N
def PolySumIndep (nab : NabV Xo c) (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (h' : ι' → UA E n) (N' : ι' → ℕ) (ep : UA E n → ℂ) (B : Ideal (𝓞 E) → c.F)
    (nt : (E →+* ℂ) → ℤ) (ψ : J →* c.Fˣ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    (P : ι → MvPolynomial (LtN Dw n) c.F) (P' : ι' → MvPolynomial (LtN Dw n) c.F),
    Admissible H q₁ l.M S J h N → Admissible H q₁ l.M S J h' N' →
    (∀ i, SplitSupp H (latOf (h i))) → (∀ i', SplitSupp H (latOf (h' i'))) →
    IsHecke c S B nt → ValueLaw c Dw S B ep → MovesDatum c J ψ ph → (∀ i, P i ∈ harmSp c Dw a n) →
    (∀ i', ∃ (i : ι) (γ : ratPts E n) (k : J) (cc : c.F), h' i' = γ.1 * h i * k.1 ∧
      IsCocycle c Dw S B nt γ ((ψ k : c.Fˣ) : c.F) cc ∧ P' i' = cc • pushRat c γ (P i)) →
      ∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v v' : R),
        PolySumValAt Xo c nab vol J h N ep cξ ph P y v → PolySumValAt Xo c nab vol J h' N' ep cξ ph P' y v' → v = v'
def ClassSumIndep (nab : NabV Xo c) (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (h' : ι' → UA E n) (N' : ι' → ℕ) (ep : UA E n → ℂ) (B : Ideal (𝓞 E) → c.F)
    (nt : (E →+* ℂ) → ℤ) (ψ ty : J →* c.Fˣ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    (T : Type) [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T] [IsScalarTower (𝓞 c.F) c.F T]
    (col : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n) (ρ : Representation c.F (ratPts E n) T)
    (L : UA E n → Submodule (𝓞 c.F) T) (v₀ : T) (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (f : UA E n → T),
    Admissible H q₁ l.M S J h N → Admissible H q₁ l.M S J h' N' →
    (∀ i, SplitSupp H (latOf (h i))) → (∀ i', SplitSupp H (latOf (h' i'))) →
    IsHecke c S B nt → ValueLaw c Dw S B ep → MovesDatum c J ψ ph → TypeTie c S B nt J ψ ty →
    CoeffTie c a (-expE Dw nt) col ρ L v₀ io → IsForm c J ty ρ f →
      ∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v v' : R),
        ClassSumValAt Xo c nab vol J h N ep cξ ph io (fun i => f (h i)) y v →
        ClassSumValAt Xo c nab vol J h' N' ep cξ ph io (fun i' => f (h' i')) y v' → v = v'
def ClassSumIndepConst (nab : NabV Xo c) (q₁ n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (h' : ι' → UA E n) (N' : ι' → ℕ) (ep : UA E n → ℂ) (B : Ideal (𝓞 E) → c.F)
    (nt : (E →+* ℂ) → ℤ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F) (f : UA E n → c.F),
    Admissible H q₁ l.M S J h N → Admissible H q₁ l.M S J h' N' →
    (∀ i, SplitSupp H (latOf (h i))) → (∀ i', SplitSupp H (latOf (h' i'))) →
    IsHecke c S B nt → Unram c S B nt → ValueLaw c Dw S B ep → FixesDatum c J ph →
    (∀ (g : UA E n) (γ : ratPts E n), ∀ k ∈ J, f (γ.1 * g * k) = detChar c (-expE Dw nt) γ * f g) →
      ∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v v' : R),
        PolySumValAt Xo c nab vol J h N ep cξ ph (fun i => C (f (h i))) y v →
        PolySumValAt Xo c nab vol J h' N' ep cξ ph (fun i' => C (f (h' i'))) y v' → v = v'
def ScalarMatrixChange (nab : NabV Xo c) (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HidaSetting Dw n → ∀ (z : 𝓞 E) (N N' : ℕ) (ph : (Fin n → ConjQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F),
    IsCoprime z (H.bar z) → IsCoprime z ((2 * q₁ * H.d * l.M : ℕ) : 𝓞 E) → (l.M : 𝓞 E) ∣ z - H.bar z →
    GenLat.LevOK (⟨stdLat E n⟩ : GenLat E n) N l.M →
    (moveLat (Matrix.scalar (Fin n) ((H.bar z : E) / (z : E))) (⟨stdLat E n⟩ : GenLat E n)).LevOK N' l.M →
    P ∈ harmSp c Dw a n →
      ∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v v' : R),
        ThLaValAt Xo c nab ph ⟨stdLat E n⟩ N P y v →
        ThLaValAt Xo c nab ph (moveLat (Matrix.scalar (Fin n) ((H.bar z : E) / (z : E))) ⟨stdLat E n⟩) N'
          (push c (Matrix.scalar (Fin n) ((H.bar z : E) / (z : E))) P) y v' →
          v' = algebraMap c.F R (∏ σ : E →+* ℂ, embK c σ z ^ (n * Dw.mult σ)) * v
end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity


