-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
-- name    : Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:05.400799+00:00
-- url     : https://prove2.me/theorems/058ce292-dbce-4206-8756-796f469f5638
-- title:
--   Lattice Determinant Index Sq
-- statement:
--   Definitions and structural lemmas for Lattice Determinant Index Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/LatticeDeterminantIndexSq.lean

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnitSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure
def SignatureBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (A Pos : Submodule ℂ V),
    (∀ x ∈ A, (h x x).re ≤ 0) → (∀ x ∈ Pos, x ≠ 0 → 0 < (h x x).re) →
    finrank ℂ A + finrank ℂ Pos ≤ finrank ℂ V
def PerpSplit : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (σ : K →+* K)
    (B : V →ₗ[K] V →ₛₗ[σ] K) (U A : Submodule K V), A ≤ U → IsCompl U (perpR B U) →
    perpR B A = perpR B U ⊔ (U ⊓ perpR B A) ∧ Disjoint (perpR B U) (U ⊓ perpR B A)
def MinorLift : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (c : Fin (r + 1) → R), c (Fin.last r) = 0 →
    (Z.updateRow (Fin.last r) (Z (Fin.last r) + Matrix.vecMul c Z)).det = Z.det ∧
    ((Z.updateRow (Fin.last r) (Z (Fin.last r) + Matrix.vecMul c Z)).submatrix
        Fin.castSucc Fin.castSucc).det = (Z.submatrix Fin.castSucc Fin.castSucc).det ∧
    (Z.updateCol (Fin.last r) ((fun b => Z b (Fin.last r)) + Matrix.mulVec Z c)).det = Z.det ∧
    ((Z.updateCol (Fin.last r) ((fun b => Z b (Fin.last r)) + Matrix.mulVec Z c)).submatrix
        Fin.castSucc Fin.castSucc).det = (Z.submatrix Fin.castSucc Fin.castSucc).det
def CoprimeDiv : Prop :=
  ∀ (R : Type) [CommRing R] (g T : ℕ) (c : R), Nat.Coprime g T → (g : R) ∣ c * (T : R) →
    (g : R) ∣ c
def LatticeDeterminantIndexSq : Prop :=
  ∀ (detTh detLa GG i cardB : ℝ), 0 < cardB → detTh = detLa * i → detTh * cardB = GG →
    detLa * i ^ 2 = GG * i / cardB
def PolariseSesq : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (σ : K →+* K)
    (h : V →ₗ[K] V →ₛₗ[σ] K) (y₁ y₂ A₁ A₂ y₁' y₂' A₁' A₂' : V),
    y₁ - A₁ = y₁' + A₁' → y₂ - A₂ = y₂' + A₂' →
    h y₁ A₂ = 0 → h A₁ y₂ = 0 → h y₁' A₂' = 0 → h A₁' y₂' = 0 →
    h y₁ y₂ + h A₁ A₂ = h y₁' y₂' + h A₁' A₂'
def CofactorLine : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : Fin (r + 1) → K),
    Z.det ≠ 0 → (∀ a, a ≠ Fin.last r → ∑ b, c b * Z b a = 0) →
    ∃ t : K, ∀ b, c b = t * Z.adjugate (Fin.last r) b
def IndefiniteUnitaryInverse : Prop :=
  ∀ (N : Matrix (Fin 2) (Fin 2) ℂ), N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * N = Formalism.SLP.GlobalBoundRefinements.J →
    N⁻¹ = Formalism.SLP.GlobalBoundRefinements.J * N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J
def ThmBEntryDiag : Prop :=
  ∀ (M N : Matrix (Fin 2) (Fin 2) ℂ),
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J →
    N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * N = Formalism.SLP.GlobalBoundRefinements.J →
    ‖(M * N⁻¹) 0 0‖ ≤ ‖M 0 0‖ * ‖N 0 0‖ + ‖M 1 0‖ * ‖N 1 0‖
def HadamardIdeal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g t : ℕ) (β : E) (J : FractionalIdeal (𝓞 E)⁰ E),
    0 < g → β ≠ 0 → J ≠ 0 → (∀ x ∈ J, ∃ y : 𝓞 E, β * x = (g : E) ^ t * (y : E)) →
    (g : ℚ) ^ (t * finrank ℚ E) ≤ |Algebra.norm ℚ β| * FractionalIdeal.absNorm J
def KerImageCard : Prop :=
  ∀ (A C : Type) [AddCommGroup A] [Finite A] [AddCommGroup C] (φ : A →+ C) (K : AddSubgroup A)
    (S : AddSubgroup C), K ≤ φ.ker → S ≤ φ.range → Nat.card K * Nat.card S ≤ Nat.card A
def RadImageIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cc : FractionalIdeal (𝓞 E)⁰ E) (α α' : E)
    (rr : Ideal (𝓞 E)), cc ≠ 0 →
    (∀ c : 𝓞 E, c ∈ rr ↔ ∀ x ∈ cc, IsInt ((c : E) * x * α) ∧ IsInt ((c : E) * x * α')) →
    ∀ (K H : AddSubgroup E), (∀ x, x ∈ H ↔ x ∈ cc) →
      (∀ x, x ∈ K ↔ IsInt (x * α) ∧ IsInt (x * α')) →
      K.relIndex H = Ideal.absNorm rr
def ZZgParam : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (p : E × E),
    p ∈ (ZZ g : Set (E × E)) ↔
      ∃ c a₁ a₂ : 𝓞 E, p = (-(c : E) + (g : E) * (a₁ : E), (c : E) + (g : E) * (a₂ : E))
def ZZgLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (a b c d : E) (P : Ideal (𝓞 E)),
    (∀ p ∈ (ZZ g : Set (E × E)), (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (ZZ g : Set (E × E))) →
    (g : 𝓞 E) ∉ P → LocIn P a 1 ∧ LocIn P b 1 ∧ LocIn P c 1 ∧ LocIn P d 1
def SIntOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (T T' g : ℕ) (s a c : E),
    0 < T → 0 < T' → Nat.Coprime g (T * T') →
    s = (T' : E) * c * σ c / (T : E) → s = a * σ a - 1 → IsInt ((g : E) * a) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (g : 𝓞 E) ∉ P → LocIn P c T) →
    ∃ β : 𝓞 E, (g : E) ^ 2 * s = (T : E) * (T' : E) * (β : E)
def DiagConj : Prop :=
  ∀ (ga : Matrix (Fin 2) (Fin 2) ℂ) (T T' : ℝ), 0 < T → 0 < T' →
    ((Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)]) * ga *
        (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹) 0 0 = ga 0 0
def HypAdd : Prop :=
  ∀ (ch₁ sh₁ ch₂ sh₂ x : ℝ), 0 < sh₁ → 0 < sh₂ → 0 ≤ ch₁ → 0 ≤ ch₂ → ch₁ ^ 2 = sh₁ ^ 2 + 1 →
    ch₂ ^ 2 = sh₂ ^ 2 + 1 → 0 ≤ x → x ≤ ch₁ / sh₁ * (ch₂ / sh₂) + 1 / sh₁ * (1 / sh₂) →
    x ^ 2 - 1 ≤ ((ch₁ + ch₂) / (sh₁ * sh₂)) ^ 2
def ScalarMore : Prop :=
  ∀ (K : Type) [Field K] (t₁ t₂ D₁ D₂ R₁ R₂ : K), t₁ ≠ 0 → t₂ ≠ 0 →
    t₁ * D₁ = t₂ * D₂ → t₁ * R₁ = t₂ * R₂ → (R₁ = 0 ↔ R₂ = 0) ∧ D₁ / R₁ = D₂ / R₂
def CofactorVecDual : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R),
    (∀ b : Fin (r + 1), ∑ a, Z b a * Z.adjugate a (Fin.last r) =
        if b = Fin.last r then Z.det else 0) ∧
      Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det
def UniqueLift : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : Fin (r + 1) → K),
    (Z.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 → c (Fin.last r) = 1 →
    (∀ a, a ≠ Fin.last r → ∑ b, c b * Z b a = 0) →
    (∀ b, c b = Z.adjugate (Fin.last r) b / (Z.submatrix Fin.castSucc Fin.castSucc).det) ∧
      ∑ b, c b * Z b (Fin.last r) = Z.det / (Z.submatrix Fin.castSucc Fin.castSucc).det
def HermSphereCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L], finrank K L = 2 →
    ∀ (M : ℕ) (c : K), c ≠ 0 →
    (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) =
      (Fintype.card K : ℤ) ^ M * ((Fintype.card K : ℤ) ^ (M + 1) - (-1) ^ (M + 1))
def SplitSphereCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (M : ℕ),
    Nat.card {p : (Fin (M + 1) → K) × (Fin (M + 1) → K) // ∑ i, p.1 i * p.2 i = 1} =
      Fintype.card K ^ M * (Fintype.card K ^ (M + 1) - 1)
def MassRatioArith : Prop :=
  ∀ (M f : ℕ) (v d : ℝ), 0 < v → d = (2 * v) ^ f →
    (((M - 1).factorial : ℝ) / (2 * Real.pi) ^ M) ^ f * d ^ ((M : ℝ) - 1 / 2) =
      (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f * d ^ (-(1 / 2) : ℝ)
def EulerLog : Prop :=
  ∀ (ι : Type) (s : Finset ι) (e : ι → ℕ) (X : ℝ), 0 < X → X < 1 → (∀ p ∈ s, 1 ≤ e p) →
    ∑ p ∈ s, -Real.log (1 - X ^ e p) ≤ ((∑ p ∈ s, e p : ℕ) : ℝ) * -Real.log (1 - X)
def TailSum : Prop :=
  HasSum (fun i : ℕ => (∑' n : ℕ, (((n : ℝ) + 1) ^ (i + 2))⁻¹) - 1) 1
def ConvexBodyCond : Prop :=
  ∀ (f : ℕ) (rd : ℝ), 0 < rd →
    (2 : ℝ) ^ (4 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ * (rd ^ f) ^ 2 ≤ (Real.pi ^ 2 * rd ^ 2 / 2) ^ f
def UnitsSquareIndex : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], (∀ w : InfinitePlace F, w.IsReal) →
    Nat.card ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range) = 2 ^ finrank ℚ F
def IdealCountBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : ℝ), 1 ≤ X →
    {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      ({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ) ≤
        X * (1 + Real.log X) ^ finrank ℚ K
def MinkConst : Prop :=
  ∀ f : ℕ, (4 / Real.pi) ^ f * ((2 * f).factorial : ℝ) / ((2 * f : ℕ) : ℝ) ^ (2 * f) ≤
    (2 / Real.pi) ^ f
def ClassNumberBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], (∀ w : InfinitePlace E, w.IsComplex) →
    (classNumber E : ℝ) ≤ Real.sqrt |(discr E : ℝ)| *
      (1 + Real.log (Real.sqrt |(discr E : ℝ)|)) ^ finrank ℚ E
def LogMassBound : Prop :=
  ∀ (f : ℕ) (rd : ℝ), 1 ≤ f → 1 ≤ rd →
    Real.log ((4 : ℝ) ^ f * (rd ^ f) ^ 5 * (1 + Real.log (rd ^ f)) ^ (5 * f)) ≤
      f * (2 + 10 * Real.log rd + 5 * Real.log f)
def MassBoundOfFactorBounds : Prop :=
  ∀ (f : ℕ) (h2 I hE d : ℝ), 1 ≤ d → 0 ≤ I → 0 ≤ hE → h2 ≤ I * ((2 : ℝ) ^ f * hE) ^ 2 * d ^ 2 →
    I ≤ d * (1 + Real.log d) ^ f → hE ≤ d * (1 + Real.log d) ^ (2 * f) →
    h2 ≤ (4 : ℝ) ^ f * d ^ 5 * (1 + Real.log d) ^ (5 * f)
def WeightProd : Prop :=
  ∀ (r : ℕ) (c : ℕ → ℝ),
    ∏ l ∈ Icc 1 r, (∏ a ∈ Icc 1 l, c a) ^ 4 = ∏ a ∈ Icc 1 r, c a ^ (4 * (r + 1 - a))
def CovSplit : Prop :=
  ∀ (f r k : ℕ) (v cc : ℝ), 1 ≤ f → 0 < v → 0 < cc →
    ((2 : ℝ) ^ f)⁻¹ * (2 * v) ^ ((f : ℝ) / 2) ≤ cc → cc ≤ (2 * v) ^ ((f : ℝ) / 2) →
    1 / 2 ≤ cc ^ (1 / (f : ℝ)) * ((2 * v) ^ (1 / 2 : ℝ))⁻¹ ∧
      cc ^ (1 / (f : ℝ)) * ((2 * v) ^ (1 / 2 : ℝ))⁻¹ ≤ 1 ∧
      ((2 * v) ^ (f * (r * (k + 1) + r * (r - 1))) * cc ^ r) ^ (1 / (f : ℝ)) =
        (2 * v) ^ (r * k) * (2 * v) ^ ((r : ℝ) ^ 2 + (r : ℝ) / 2) *
          (cc ^ (1 / (f : ℝ)) * ((2 * v) ^ (1 / 2 : ℝ))⁻¹) ^ r
def StBound : Prop :=
  ∀ j : ℕ, (Real.exp 1 / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) * (j.factorial : ℝ) ≤ 3
def ConstExact : Prop :=
  ∀ (j r : ℕ) (T T' g v th dimpi Vd VV Tc : ℝ), 0 < T → 0 < T' → 0 < g → 0 < v → 0 < th →
    Vd ≠ 0 → VV ≠ 0 → 0 < Tc →
    Tc ^ (j + 1) * ((Real.pi / v) ^ ((2 * r + 1) * (j + 1) + (2 * r + 2) * (2 * r + 1) / 2) *
        (2 * v) ^ (((2 * r + 1 : ℕ) : ℝ) / 2)) =
      g ^ ((j + 1) * (2 * r + 2) + (2 * r + 2) * (2 * r + 1) / 2) * (VV / Vd) →
    (Real.exp 1 * Real.pi / (g ^ (2 * r + 2) * T * ((j + 1 : ℕ) : ℝ) * v)) ^ (j + 1) *
      (((2 : ℝ) ^ (r + 1))⁻¹ * (th ^ (2 * r))⁻¹ * dimpi *
        (Vd / ∏ i ∈ range (j + 1), (i.factorial : ℝ)) * (T * T') ^ (j + 1) *
        volU (j + 1 + (2 * r + 1)) * volU j /
        (VV / (∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ)) * volU (j + 1) ^ 2 *
          (2 * v) ^ (2 * r * (j + 1) + 2 * r ^ 2 + r))) =
      dimpi * (Tc / T')⁻¹ ^ (j + 1) *
        (((2 : ℝ) ^ (r + 1))⁻¹ * (th ^ (2 * r))⁻¹ *
          ((Real.exp 1 / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) * (j.factorial : ℝ)) *
          (2 * v) ^ ((r : ℝ) + 1 / 2) * g ^ ((2 * r + 2) * (2 * r + 1) / 2))
def ConstFinal : Prop :=
  ∀ (r : ℕ) (th st : ℝ), 1 / 2 ≤ th → 0 ≤ st → st ≤ 3 →
    ((2 : ℝ) ^ (r + 1))⁻¹ * (th ^ (2 * r))⁻¹ * st ≤ 3 * (2 : ℝ) ^ r / 2
def SamePlaceConst : Prop :=
  ∀ (ι : Type) (k : ℕ) (x dimpi dimpi' deg VV Vd Tc : ι → ℝ) (K Pn Pk A B T' : ℝ),
    Pn ≠ 0 → Pk ≠ 0 → A ≠ 0 → B ≠ 0 → T' ≠ 0 → (∀ v, deg v ≠ 0) → (∀ v, dimpi' v ≠ 0) →
    (∀ v, x v = K * (dimpi v * dimpi' v / deg v)) → (∀ v, VV v = deg v * Pn) →
    (∀ v, Vd v = dimpi' v * Pk) → (∀ v, Tc v ^ k * A = B * (VV v / Vd v)) →
    ∀ v, x v = (K * (B * Pn / (A * Pk * T' ^ k))) * (dimpi v * (Tc v / T')⁻¹ ^ k)
end Formalism.HermitianLatticeCounting.LocalIntegralStructure


