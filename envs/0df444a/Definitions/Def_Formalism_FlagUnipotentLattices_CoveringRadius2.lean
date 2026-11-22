-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
-- name    : Formalism_FlagUnipotentLattices_CoveringRadius2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:56.615263+00:00
-- url     : https://prove2.me/theorems/c3cd99f0-cc06-40fc-a12e-3a64c63d6b30
-- title:
--   Covering Radius2
-- statement:
--   Definitions and structural lemmas for Covering Radius2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/CoveringRadius2.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
noncomputable section
namespace Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
def PolarInv : Prop :=
  ∀ (N : ℕ) (k X : Matrix (Fin N) (Fin N) ℂ), k ∈ Matrix.unitaryGroup (Fin N) ℂ → X.IsHermitian →
    (k * NormedSpace.exp X)⁻¹ = k.conjTranspose * NormedSpace.exp (-(k * X * k.conjTranspose)) ∧
      (-(k * X * k.conjTranspose)).IsHermitian ∧ hs (-(k * X * k.conjTranspose)) = hs X ∧
      ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - (k * NormedSpace.exp X).conjTranspose * (k * NormedSpace.exp X)).PosSemidef
open Classical in

def AllSum : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h ε : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 ≤ B → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → B * ε ≤ 1 →
    32 * B ≤ h * ε → 16 ≤ h * ε ^ 2 →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ A * 4 ^ Fintype.card ι
open Classical in

def AllSumRate : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 < B → 16 * B * Real.sqrt (2 * (q : ℝ)) ≤ h →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤
      A * (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card ι
def ThreshCount : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 46 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    16 * (2 * (n : ℝ) ^ 2) * Real.sqrt (2 * (q : ℝ)) ≤ h
def NearUnipotent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n g : ℕ) (ε : ℝ), Squarefree g → 4 * n < g →
    (∀ P : Ideal (𝓞 E), P.IsPrime → ((g : ℤ) : 𝓞 E) ∈ P → P.ramificationIdx ℤ = 1) →
    (n : ℝ) * ε ≤ 1 → ε ≤ 1 / 4 →
    ∀ γ : Matrix (Fin n) (Fin n) E, IsUnit γ →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      (∀ x ∈ L, γ *ᵥ x ∈ L) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → ((g : ℤ) : 𝓞 E) ∈ P →
        ∀ x ∈ L, ((γ - 1) ^ n) *ᵥ x ∈ P • L) →
      ∀ (x k X : (E →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
      (∀ φ, IsUnit (x φ) ∧ k φ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (X φ).IsHermitian ∧ hs (X φ) ≤ ε ∧
        (x φ)⁻¹ * γ.map φ * x φ = k φ * NormedSpace.exp (X φ)) →
      (γ - 1) ^ n = 0 ∧ ∀ φ, hs ((x φ)⁻¹ * γ.map φ * x φ - 1) ≤ 3 * Real.sqrt (n * ε)
def NearAssembly : Prop :=
  Formalism.SA.D.Unipotence → NearPowBound → UnipTrace → NearIdentity → NearUnipotent
def IsotropicDim : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (W : Submodule ℂ (Fin N → ℂ)),
    (∀ x ∈ W, ∀ y ∈ W, ∑ a, (if ep a then (1 : ℂ) else -1) * star (x a) * y a = 0) →
    Module.finrank ℂ W ≤ q0 ep
def LayerCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (N : ℕ) (de la laM : ℝ), 0 ≤ de → 0 < la → la / 2 ≤ laM →
    (1 + 2 * (∏ _v : ι, 3 * de) ^ ((1 : ℝ) / Fintype.card ι) / laM) ^ (N * Fintype.card ι) ≤
      (1 + 12 * de / la) ^ (N * Fintype.card ι)
def KappaAssembly : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (a p q n0 f : ℕ) (j : Fin a → ℕ) (v res cIw volN volR : ℝ) (volGL : Fin a → ℝ),
    (∀ x, 1 ≤ j x) → 1 ≤ a → (∑ x, j x) ≤ q → q ≤ p → p + q = n0 + 2 * ∑ x, j x → 1 ≤ f →
    1 / 2 ≤ v → 0 ≤ res →
    0 ≤ volN → volN ≤ (C * v) ^ ((f : ℝ) * dimN j n0 / 2) →
    (∀ x, 0 ≤ volGL x ∧ volGL x ≤ (C * v) ^ (j x ^ 2 * f) * res * C ^ f) →
    0 ≤ volR → volR ≤ v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) * C ^ ((p + q) * f) →
    0 ≤ cIw → cIw ≤ (C ^ dimN j n0 * (Vsph p * Vsph q /
      (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f →
    cIw * volN * (∏ x, volGL x) * volR ≤
      v ^ (-((f : ℝ) * dimN j n0 / 2)) * C' ^ ((∑ x, j x) * (p + q) * f) * res ^ a
        * ((C' / (p : ℝ)) ^ ((∑ x, j x) * (p - ∑ x, j x))
          * ((∑ x, j x : ℕ) : ℝ) ^ (((∑ x, j x : ℕ) : ℝ) ^ 2 / 2)) ^ f
def DedekindProduct : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] (j : ℕ),
    ∏ i ∈ Icc 2 j, ‖dedekindZeta E (i : ℂ)‖ ≤ C ^ Module.finrank ℚ E
def DedekindZetaResidueBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E], 2 ≤ Module.finrank ℚ E →
    dedekindZeta_residue E ≤
      (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E
def LogVolumeBound : Prop :=
  ∀ (a q f : ℕ) (j : Fin a → ℕ) (C₁ Y : ℝ), 1 ≤ C₁ → 2 ≤ Y → 1 ≤ q → (∀ x, j x ≤ q) →
    0 < Y ^ (-(C₁ * q)) ∧ Y ^ (-(C₁ * q)) ≤ 1 / 2 ∧
    ∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * Y ^ (-(C₁ * q))))) ≤
      (2 * C₁ * f * (q : ℝ) ^ 2 * Real.log Y) ^ a
def EpsSide : Prop :=
  ∀ (n q f : ℕ) (c : ℝ), 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n → 0 < c → c ≤ 1 / 90000 →
    2 * (n : ℝ) ^ 2 * epsN c n f ≤ 1 ∧ epsN c n f * Real.sqrt (2 * (q : ℝ)) ≤ 1
def ThreshSide : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ (n f : ℕ) (rd b h : ℝ), 1 ≤ n → 1 ≤ f → 2 ≤ b → 1 ≤ rd →
    C * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
    32 * (2 * (n : ℝ) ^ 2) ≤ h * epsN c n f ∧ 16 ≤ h * epsN c n f ^ 2
def FarPrefactorOp : Prop :=
  ∀ (n f : ℕ) (τs : ℝ), 1 ≤ n → 1 ≤ f → 0 < τs →
    (3 / τs ^ 2) ^ (2 * n ^ 2 * f) * 4 ^ f ≤ (6 / τs) ^ (4 * n ^ 2 * f)
def CoveringRadius2 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)
def StepsRoom : Prop :=
  ∀ (n q f P : ℕ) (b : ℝ), 1 ≤ q → P0 n q f + n ^ 2 * f ≤ 2 * P0 n q f ∧
    (P ≤ 2 * P0 n q f → b ^ 2 + (P : ℝ) * n ≤ b1 n q f b)
def BasisCS : Prop :=
  ∀ (ι H : Type) [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H] (c : ι → ℝ) (v : ι → H)
    (B : ℝ), (∀ i, ‖v i‖ ≤ B) →
    ‖∑ i, c i • v i‖ ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (Fintype.card ι) * B
def PathOsc : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (φ φ' : ℝ → H) (T B : ℝ), 0 ≤ T →
    (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt φ (φ' t) (Set.Icc 0 T) t) →
    (∀ t ∈ Set.Icc 0 T, ‖φ' t‖ ≤ B) → ‖φ T - φ 0‖ ≤ T * B
def OscBound : Prop :=
  ∀ (V H ι : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup H]
    [NormedSpace ℝ H] [Fintype ι] (e : OrthonormalBasis ι ℝ V) (φ : V → H) (φ' : V → V →L[ℝ] H)
    (s : Set V) (B : ℝ), Convex ℝ s → (∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) →
    (∀ x ∈ s, ∀ i, ‖φ' x (e i)‖ ≤ B) →
    ∀ x ∈ s, ∀ y ∈ s, ‖φ x - φ y‖ ≤ ‖x - y‖ * Real.sqrt (Fintype.card ι) * B
def PeriodicSup : Prop :=
  ∀ (V H ι : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [Fintype ι] (e : OrthonormalBasis ι ℝ V) (M : Submodule ℤ V) (D : Set V) (φ : V → H)
    (φ' : V → V →L[ℝ] H) (ρ B : ℝ),
    DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    IsAddFundamentalDomain M D (volume : Measure V) →
    (∀ x, HasFDerivAt φ (φ' x) x) → (∀ x, ∀ y ∈ M, φ (x + y) = φ x) →
    (∫ x in D, φ x) = 0 → (∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ ρ) → (∀ x i, ‖φ' x (e i)‖ ≤ B) →
    ∀ x, ‖φ x‖ ≤ ρ * Real.sqrt (Fintype.card ι) * B
def SobolevCube : Prop :=
  ∀ (m : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Dv : Finset (Fin m) → (Fin m → ℝ) → H) (s : ℝ), 0 < s →
    (∀ S, ContinuousOn (Dv S) (Set.Icc (0 : Fin m → ℝ) (fun _ => s))) →
    (∀ (S : Finset (Fin m)) (i : Fin m), i ∉ S → ∀ t ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => s),
      HasDerivWithinAt (fun r : ℝ => Dv S (Function.update t i r)) (Dv (insert i S) t)
        (Set.Icc 0 s) (t i)) →
    ‖Dv ∅ 0‖ ^ 2 ≤ (2 / s) ^ m * ∑ S : Finset (Fin m), s ^ (2 * S.card) *
      ∫ t in Set.Icc (0 : Fin m → ℝ) (fun _ => s), ‖Dv S t‖ ^ 2
def SobolevSum : Prop :=
  ∀ (m : ℕ) (s β X : ℝ) (I : Finset (Fin m) → ℝ), 0 < s → 0 ≤ β → s * β ≤ 1 → 0 ≤ X →
    (∀ S, I S ≤ β ^ (2 * S.card) * X) →
    (2 / s) ^ m * ∑ S : Finset (Fin m), s ^ (2 * S.card) * I S ≤ (4 / s) ^ m * X
end Formalism.HermitianLatticeCounting.S7


