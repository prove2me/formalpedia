-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
-- name    : Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:44.739652+00:00
-- url     : https://prove2.me/theorems/2ab5d46e-c9f2-4497-a400-39df91e3c428
-- title:
--   First Coordinate Admissible
-- statement:
--   Definitions and structural lemmas for First Coordinate Admissible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/FirstCoordinateAdmissible.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def IsType (Ψ : Finset (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ
def ccT {α β : Type} (A : Matrix α β E) : Matrix β α E := (A.map cc)ᵀ
def imH {N : ℕ} (Z : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := (2 * I)⁻¹ • (Z - Zᴴ)
abbrev CM (Ψ : Finset (E →+* ℂ)) (a b : ℕ) : Type := Ψ → Matrix (Fin a) (Fin b) ℂ
def Hn (Ψ : Finset (E →+* ℂ)) (N : ℕ) : Set (CM Ψ N N) := {Z | ∀ τ, (imH (Z τ)).PosDef}
def HnGe (Ψ : Finset (E →+* ℂ)) (N : ℕ) (δ : ℝ) : Set (CM Ψ N N) :=
  {Z | ∀ τ, (imH (Z τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef}
def detIm {Ψ : Finset (E →+* ℂ)} {N : ℕ} (Z : CM Ψ N N) : ℝ := ∏ τ, (imH (Z τ)).det.re
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
def expo (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∑ τ : Ψ, ∑ k, ((fun a => τ.1 (x k a)) ⬝ᵥ Z τ *ᵥ (fun a => conj (τ.1 (x k a))) +
    (fun a => τ.1 (x k a)) ⬝ᵥ z τ k + z' τ k ⬝ᵥ fun a => conj (τ.1 (x k a)))
def thH (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∑' x : Matrix (Fin n) (Fin N) E, φ x * cexp (2 * Real.pi * I * expo Ψ x Z z z')
abbrev M2 (E : Type) (N : ℕ) : Type := Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) E
def UU (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) : Set (M2 E N) :=
  {γ | ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E}
def hDen (γ : M2 E N) (Z : CM Ψ N N) : CM Ψ N N := fun τ =>
  γ.toBlocks₂₁.map τ.1 * Z τ + γ.toBlocks₂₂.map τ.1
def hDen' (γ : M2 E N) (Z : CM Ψ N N) : CM Ψ N N := fun τ =>
  Z τ * (γ.toBlocks₂₁.map τ.1)ᴴ + (γ.toBlocks₂₂.map τ.1)ᴴ
def hAct (γ : M2 E N) (Z : CM Ψ N N) : CM Ψ N N := fun τ =>
  (γ.toBlocks₁₁.map τ.1 * Z τ + γ.toBlocks₁₂.map τ.1) * (hDen Ψ γ Z τ)⁻¹
def hFac (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∏ τ : Ψ, (hDen Ψ γ Z τ).det ^ n * cexp (2 * Real.pi * I *
    ∑ k, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k)
def TransH (γ : M2 E N) (φ ψ : Matrix (Fin n) (Fin N) E → ℂ) : Prop :=
  ∀ Z ∈ Hn Ψ N, ∀ z z' : CM Ψ n N,
    thH Ψ ψ (hAct Ψ γ Z) (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
      (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = hFac Ψ γ Z z z' * thH Ψ φ Z z z'
open Classical in

def weil (γ : M2 E N) (φ : Matrix (Fin n) (Fin N) E → ℂ) : Matrix (Fin n) (Fin N) E → ℂ :=
  if h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ then h.choose else 0
def botSpan (γ : M2 E N) : Submodule E (Fin N ⊕ Fin N → E) :=
  Submodule.span E (Set.range fun a : Fin N => γ (Sum.inr a))
def Lag (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) : Type :=
  {U : Submodule E (Fin N ⊕ Fin N → E) // ∃ γ ∈ UU E N, botSpan γ = U}
def eisTerm (γ : M2 E N) (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  weil Ψ γ φ 0 * (hFac Ψ γ Z z z')⁻¹
def eis (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∑' U : Lag E N, eisTerm Ψ U.2.choose φ Z z z'
def heisH (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Matrix (Fin n) (Fin N) E → ℂ := fun x =>
  φ (x - d) * cexp (Real.pi * I *
    ((Algebra.trace ℚ E (∑ k, ∑ a, b k a * (2 * cc (x k a) - cc (d k a))) : ℚ) : ℂ))
def chiH (β : Matrix (Fin N) (Fin N) E) (x : Matrix (Fin n) (Fin N) E) : ℂ :=
  cexp (2 * Real.pi * I * ∑ τ : Ψ, τ.1 (x * β * ccT x).trace)
def Den {α β : Type} (c : ℕ) (γ : Matrix α β E) : Prop := IntM ((c : E) • γ)
abbrev QI (E : Type) [Field E] [NumberField E] (N : ℕ) : Type := Fin N × Fin (Module.finrank ℚ E)
def ofQ (m : Matrix (Fin n) (QI E N) ℚ) : Matrix (Fin n) (Fin N) E :=
  Matrix.of fun k a => ∑ j, m k (a, j) • Module.finBasis ℚ E j
def tauOf (Z : CM Ψ N N) : Matrix (QI E N) (QI E N) ℂ := Matrix.of fun p q => ∑ τ : Ψ,
  (τ.1 (Module.finBasis ℚ E p.2) * Z τ p.1 q.1 * conj (τ.1 (Module.finBasis ℚ E q.2)) +
    τ.1 (Module.finBasis ℚ E q.2) * Z τ q.1 p.1 * conj (τ.1 (Module.finBasis ℚ E p.2)))
def zetaOf (z z' : CM Ψ n N) : Fin n → QI E N → ℂ := fun k p => ∑ τ : Ψ,
  (τ.1 (Module.finBasis ℚ E p.2) * z τ k p.1 + z' τ k p.1 * conj (τ.1 (Module.finBasis ℚ E p.2)))
abbrev Lt (E : Type) [Field E] [NumberField E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E)
def stdL (E : Type) [Field E] [NumberField E] (m : ℕ) : Lt E m :=
  Submodule.span (𝓞 E) (Set.range fun a : Fin m => (Pi.single a 1 : Fin m → E))
def Agree {m : ℕ} (M : ℕ) (Λ Λ' : Lt E m) : Prop :=
  ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧ (∀ v ∈ Λ, (s : E) • v ∈ Λ') ∧ ∀ v ∈ Λ', (s : E) • v ∈ Λ
def Vset (E : Type) [Field E] [NumberField E] [IsCMField E] (n M : ℕ) : Set (Lt E n) :=
  {Λ | Λ.FG ∧ (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧ Agree M Λ (stdL E n)}
def DH (E : Type) [Field E] [NumberField E] [IsCMField E] (n M : ℕ) :
    Set (Matrix (Fin n) (Fin n) E) :=
  {h | ccT h * h = 1 ∧ ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧
    ∃ y : Matrix (Fin n) (Fin n) E, IntM y ∧ (s : E) • (h - 1) = (M : E) • y}
def Moves {m : ℕ} (h : Matrix (Fin m) (Fin m) E) (Λ Λ' : Lt E m) : Prop := ∀ v, v ∈ Λ ↔ h *ᵥ v ∈ Λ'
def Cls (E : Type) [Field E] [NumberField E] [IsCMField E] (n M : ℕ) : Type :=
  Quot fun Λ Λ' : Vset E n M => ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1
def wt (M : ℕ) (Λ : Lt E n) : ℝ := (({h ∈ DH E n M | Moves h Λ Λ}.ncard : ℕ) : ℝ)⁻¹
def IsClassFn (M : ℕ) (f : Lt E n → ℂ) : Prop :=
  ∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ
def classSum (M : ℕ) (f : Lt E n → ℂ) : ℂ :=
  ∑ᶠ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1
def ColsIn (Λ : Lt E n) (x : Matrix (Fin n) (Fin N) E) : Prop := ∀ a, xᵀ a ∈ Λ
abbrev Fam (E : Type) [Field E] [NumberField E] (n N : ℕ) : Type :=
  Lt E n → Matrix (Fin n) (Fin N) E → ℂ
structure admitted (M R : ℕ) (φ : Fam E n N) : Prop where
  pos : 0 < M ∧ 0 < R
  equiv : ∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' →
    ∀ x, φ Λ' (h * x) = φ Λ x
  supp : ∀ Λ ∈ Vset E n M, ∀ x, φ Λ x ≠ 0 → ColsIn Λ ((R : E) • x)
  per : ∀ Λ ∈ Vset E n M, ∀ x y, ColsIn Λ y → φ Λ (x + (R : E) • y) = φ Λ x
  loc : ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Agree (R * M) Λ Λ' → ∀ x,
    ColsIn Λ ((R : E) • x) → ColsIn Λ' ((R : E) • x) → φ Λ x = φ Λ' x
def swDiff (M : ℕ) (φ : Fam E n N) (Z : CM Ψ N N) : ℂ :=
  classSum M fun Λ => thH Ψ (φ Λ) Z 0 0 - eis Ψ (φ Λ) Z 0 0
def swd (M : ℕ) (φ : Fam E n N) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  classSum M fun Λ => thH Ψ (φ Λ) Z z z' - eis Ψ (φ Λ) Z z z'
open Classical in

def twist (R : ℕ) (𝔛 : Lt E N) (φ : Fam E n N) : Fam E n N := fun Λ x =>
  if h : (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) ∧
      ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, (s : E) • v ∈ 𝔛 then
    φ Λ ((h.2.choose : E) • x) else 0
def gidx (𝔛 : Lt E N) : ℝ :=
  ((stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup : ℝ) /
    (𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup : ℝ)
def Nb (M : ℕ) (P : Ideal (𝓞 E)) (Λ : Lt E n) : Set (Lt E n) :=
  {Λ' | Λ' ∈ Vset E n M ∧ P • Λ ≤ Λ' ∧
    Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P}
def conjI (P : Ideal (𝓞 E)) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ b ∈ P, ((a : 𝓞 E) : E) = cc ((b : 𝓞 E) : E)}
def GoodPrime (m q : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  q.Prime ∧ q.Coprime m ∧ Ideal.absNorm P = q ∧ IsCoprime P (conjI P) ∧
    ¬ (q : ℤ) ∣ 2 * NumberField.discr E
def dropZ (Z : CM Ψ (N + 1) (N + 1)) : CM Ψ N N := fun τ => (Z τ).submatrix Fin.succ Fin.succ
def dropF (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ) : Matrix (Fin n) (Fin N) E → ℂ := fun x =>
  φ (Matrix.of fun k => Fin.cons 0 (x k))
def pushZ (Z : CM Ψ N N) (v : Fin N → E) (t : ℝ) : CM Ψ N N := fun τ =>
  Z τ + (I * t) • vecMulVec (fun a => τ.1 (v a)) fun a => conj (τ.1 (v a))
namespace Base
open Classical in

def indF (E : Type) [Field E] [NumberField E] (n N : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ x then 1 else 0
end Base
end
end GlobalTheory.SW


