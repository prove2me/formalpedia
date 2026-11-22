-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
-- name    : Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:18.641802+00:00
-- url     : https://prove2.me/theorems/f382920a-0cd3-473d-80c4-7cb554275cae
-- title:
--   Mem Lp Two Of One Top
-- statement:
--   Definitions and structural lemmas for Mem Lp Two Of One Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MemLpTwoOfOneTop.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology TensorProduct
noncomputable section
namespace Formalism.HermitianLatticeCounting.S8
def sgnD (k m t j : ℕ) : List Bool :=
  List.replicate (k - 1 + (j + 1) + j * t) true ++
    (List.range (m - j - 1)).map (fun i => decide (i % 2 = 1))
def sigP (l : List Bool) : ℕ := l.count true
def sigQ (l : List Bool) : ℕ := l.count false
def dimX (k t j : ℕ) : ℕ := k + j * (t + 1)
def BaseFormSignature : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → Even m → 2 ≤ m →
    sigP (sgnD k m t 0) = k - 1 + m / 2 ∧ sigQ (sgnD k m t 0) = m / 2 ∧
      (sgnD k m t 0).length = k + m - 1
def SignZBessel : Prop :=
  ∀ k m t j : ℕ, 1 ≤ k → Even m → Even j → j < m →
    ∀ s : Bool,
      (sigP (sgnD k m t j) = dimX k t j + (m - j - 2) / 2 + (if s then 1 else 0) ∧
        sigQ (sgnD k m t j) = (m - j - 2) / 2 + (if s then 0 else 1)) ↔ s = false
def SignFJ : Prop :=
  ∀ k m t j : ℕ, 1 ≤ k → Even m → Odd j → j < m →
    sigP (sgnD k m t j) = dimX k t j + (m - j - 1) / 2 ∧ sigQ (sgnD k m t j) = (m - j - 1) / 2
def SignFlip : Prop :=
  ∀ k m t j : ℕ, 1 ≤ j → j < m →
    sgnD k m t j = (sgnD k m t (j - 1)).take (k - 1 + j + (j - 1) * t) ++ List.replicate t true ++
      ((sgnD k m t (j - 1)).drop (k - 1 + j + (j - 1) * t)).map (fun s => !s)
def blockP (c : ℝ) (len : ℕ) : List ℝ :=
  (List.range len).map (fun i : ℕ => c + ((len : ℝ) - 1) / 2 - (i : ℝ))
def alt : List ℝ → List ℝ → List ℝ
  | a :: as, b :: bs => a :: b :: alt as bs
  | as, [] => as
  | [], bs => bs
def Interlaces (A B : List ℝ) : Prop :=
  A.length = B.length + 1 ∧ (alt A B).IsChain (· > ·)
def paramD (t j m : ℕ) (v : List ℝ) (b e : ℕ → ℝ) : List ℝ :=
  v ++ (List.range m).flatMap (fun i => -b i :: if i < j then blockP (-e i) t else [])
def Centring : Prop :=
  ∀ (k m t : ℕ) (h : ℝ) (b e : ℕ → ℝ), 1 ≤ k →
    2 * (((k + m - 1 : ℕ) : ℝ) + (m : ℝ) * t) ^ 3 + t + 3 < h →
    (∀ i, i + 1 < m → h ≤ b (i + 1) - b i) →
    (∀ j, j + 1 < m → |e j - (b j + b (j + 1)) / 2| ≤ 1 / 2) →
    (0 < m → b (m - 1) + h / 2 ≤ e (m - 1)) →
    ∀ j < m,
      (∀ i < m, ((t : ℝ) + 3) / 2 < |b i - e j|) ∧
      (∀ j' < m, j' ≠ j → ∀ len ≤ t + 1, ∀ x ∈ blockP (-e j') len, ((t : ℝ) + 3) / 2 < |x + e j|) ∧
      (∀ x : ℝ, -b 0 < x → ((t : ℝ) + 3) / 2 < |x + e j|) ∧
      (∀ x ∈ blockP (-e j) t, (((k + m - 1 : ℕ) : ℝ) + (m : ℝ) * t) ^ 3 < -b j - x ∧
        (j + 1 < m → (((k + m - 1 : ℕ) : ℝ) + (m : ℝ) * t) ^ 3 < x + b (j + 1)))
def GapD : Prop :=
  ∀ (k m t j : ℕ) (h : ℝ) (u v : List ℝ) (b e : ℕ → ℝ),
    1 ≤ k → j < m → Interlaces u v → u.length = k → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t : ℝ) + 3) / 2 ≤ |b i' - e i|) →
    (∀ i, i + 1 < m → h ≤ b (i + 1) - b i) →
    Formalism.QuantumDeterminants.GapAtLeast (n := (paramD t j m v b e).length)
      (fun a => (sgnD k m t j).getD (a : ℕ) true) (fun a => (paramD t j m v b e).get a) h
def ParamDChain : Prop :=
  ∀ (k m t j : ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    1 ≤ k → j < m → Interlaces u v → u.length = k → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t : ℝ) + 3) / 2 ≤ |b i' - e i|) →
    (paramD t j m v b e).IsChain (· > ·) ∧ (paramD t j m v b e).length = (sgnD k m t j).length ∧
      (sgnD k m t j).length = k + m - 1 + j * t
def ParamDCoset : Prop :=
  ∀ (k m t j : ℕ) (v : List ℝ) (b e : ℕ → ℝ), 1 ≤ k → Even m → Odd t →
    (∀ x ∈ v, ∃ z : ℤ, x = (z : ℝ) + (k : ℝ) / 2) → (∀ i < m, ∃ z : ℤ, b i = (z : ℝ) + (k : ℝ) / 2) →
    (∀ i < m, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramD t j m v b e,
      (Even j → ∃ z : ℤ, x - (((k + m - 1 + j * t : ℕ) : ℝ) - 1) / 2 = (z : ℝ)) ∧
      (Odd j → ∃ z : ℤ, x + 1 / 2 - (((k + m - 1 + j * t : ℕ) : ℝ) - 1) / 2 = (z : ℝ))
def InterlaceBlocks : Prop :=
  ∀ (m : ℕ) (t : ℕ → ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    Interlaces u v → (∀ x ∈ u, -b 0 < x) →
    (∀ j < m, b j < e j) → (∀ j, j + 1 < m → e j < b (j + 1)) →
    (∀ i < m, ∀ j < m, ((t j : ℝ) + 3) / 2 ≤ |b i - e j|) →
    Interlaces (u ++ (List.range m).flatMap (fun j => blockP (-e j) (t j + 1)))
      (v ++ (List.range m).flatMap (fun j => -b j :: blockP (-e j) (t j)))
def InterlaceStep2 : Prop :=
  ∀ (m t : ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    Interlaces u v → (∀ x ∈ u, -b 0 < x) →
    (∀ j < m, b j < e j) → (∀ j, j + 1 < m → e j < b (j + 1)) →
    (∀ i < m, ∀ j < m, ((t : ℝ) + 3) / 2 ≤ |b i - e j|) →
    Interlaces (u ++ (List.range m).flatMap (fun j => blockP (-e j) (t + 1)))
      (v ++ (List.range m).flatMap (fun j => -b j :: blockP (-e j) t))
def NotEntryStep3 : Prop :=
  ∀ (c : ℝ) (t : ℕ) (Q : List ℝ), (∀ q ∈ Q, ((t : ℝ) + 3) / 2 ≤ |q - c|) →
    c + ((t : ℝ) + 1) / 2 ∉ Q ++ blockP c t ∧ c - ((t : ℝ) + 1) / 2 ∉ Q ++ blockP c t
def ConvRange : Prop :=
  ∀ k m t : ℕ, (k + m - 1) + 5 ≤ t → 1 + ((k : ℝ) - 1) / 2 < ((t : ℝ) + 2) / 2
def ConvRangeIff : Prop :=
  ∀ k t : ℕ, 1 ≤ k → ((1 + ((k : ℝ) - 1) / 2 < ((t : ℝ) + 2) / 2 ↔ k - 1 < t) ∧
    (2 * dimX k t 0 < dimX k t 1 ↔ k - 1 < t))
def HeckeArgs : Prop :=
  ∀ t : ℕ, (blockP 0 (t + 1)).map (fun x => ((t : ℝ) + 2) / 2 + x) =
    (List.range (t + 1)).map (fun l : ℕ => ((t : ℝ) + 1) - (l : ℝ))
def CentresDistinct : Prop :=
  ∀ (m : ℕ) (b e : ℕ → ℝ), (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    ∀ i < m, ∀ j < m, i < j → e i < e j
def EulerNonzero : Prop :=
  ∀ (ι : Type) (q : ι → ℝ) (d : ℕ) (α : ι → Fin d → ℂ) (θ σ : ℝ),
    (∀ v, 1 < q v) → (∀ τ : ℝ, 1 < τ → Summable (fun v => q v ^ (-τ))) →
    (∀ v i, ‖α v i‖ ≤ q v ^ θ) → 1 + θ < σ →
    Multipliable (fun v => ∏ i, (1 - α v i * ((q v : ℂ) ^ (-(σ : ℂ))))⁻¹) ∧
      (∏' v, ∏ i, (1 - α v i * ((q v : ℂ) ^ (-(σ : ℂ))))⁻¹) ≠ 0
def DenseStable : Prop :=
  ∀ (K : Type) [TopologicalSpace K] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : K → V →L[ℂ] V) (Γ : Set K) (W : Submodule ℂ V),
    (∀ w : V, Continuous fun g => ρ g w) → Dense Γ →
    (∀ γ ∈ Γ, ∀ w ∈ W, ρ γ w ∈ W) →
    (∀ g : K, ∀ w ∈ W, ρ g w ∈ W) ∧
      ((∀ U : Submodule ℂ V, (∀ g : K, ∀ w ∈ U, ρ g w ∈ U) → U = ⊥ ∨ U = ⊤) → W ≠ ⊥ → W = ⊤)
def BumpLimit : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (μ : Measure T)
    [IsFiniteMeasureOnCompacts μ] (f : T → ℂ) (x₀ : T), Continuous f →
    ∀ ε : ℝ, 0 < ε → ∃ O ∈ 𝓝 x₀, ∀ β : T → ℝ, Continuous β → HasCompactSupport β → (∀ x, 0 ≤ β x) →
      Function.support β ⊆ O → ∫ x, β x ∂μ = 1 → ‖(∫ x, (β x : ℂ) * f x ∂μ) - f x₀‖ ≤ ε
def BumpNonzero : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (μ : Measure T)
    [IsFiniteMeasureOnCompacts μ] (f : T → ℂ) (x₀ : T), Continuous f → f x₀ ≠ 0 →
    ∃ O ∈ 𝓝 x₀, ∀ β : T → ℝ, Continuous β → HasCompactSupport β → (∀ x, 0 ≤ β x) →
      Function.support β ⊆ O → ∫ x, β x ∂μ = 1 → (∫ x, (β x : ℂ) * f x ∂μ) ≠ 0
def DenseNonzero : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (L : E →ₗ[ℂ] ℂ) (D : Submodule ℂ E),
    Continuous L → Dense (D : Set E) → L ≠ 0 → ∃ x ∈ D, L x ≠ 0
def DescentChain : Prop :=
  ∀ (m : ℕ) (P : ℕ → Prop), P m → (∀ j, 1 ≤ j → j ≤ m → P j → P (j - 1)) → P 0
def TensorSlice : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ℓ : V ⊗[ℂ] W →ₗ[ℂ] ℂ),
    ℓ ≠ 0 → ∃ (v : V) (w : W), ℓ (v ⊗ₜ w) ≠ 0
def ConjDual : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (G : Type) [Group G]
    (ρ : G →* (E →L[ℂ] E)), (∀ g, ρ g ∈ unitary (E →L[ℂ] E)) →
    ∀ (g : G) (v : E), InnerProductSpace.toDual ℂ E (ρ g v) = (InnerProductSpace.toDual ℂ E v).comp (ρ g⁻¹)
def CoeffBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (P U : E →L[ℂ] E) (w : E),
    ContinuousLinearMap.adjoint P = P → P w = w → ‖w‖ = 1 → ‖(inner ℂ (U w) w : ℂ)‖ ≤ ‖P * U * P‖
def CyclicNonzero : Prop :=
  ∀ (E F : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [T1Space F] (G : Type) (ρ : G → E → E) (ℓ : E →ₗ[ℂ] F) (w : E),
    Continuous ℓ → ℓ ≠ 0 → Dense ((Submodule.span ℂ (Set.range fun g => ρ g w) : Submodule ℂ E) : Set E) →
    ∃ g, ℓ (ρ g w) ≠ 0
def ESelfAdj : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (G : Type) [Group G]
    (ρ : G →* (E →L[ℂ] E)), (∀ g, ρ g ∈ unitary (E →L[ℂ] E)) →
    ∀ (w : E) (d : ℝ) (g : G),
      star ((d : ℂ) * star (inner ℂ w (ρ g⁻¹ w) : ℂ)) = (d : ℂ) * star (inner ℂ w (ρ g w) : ℂ)
def PosInt : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (μ : Measure T)
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] (E : Type) [NormedAddCommGroup E] (χ : T → ℝ) (W : T → E),
    Continuous χ → HasCompactSupport χ → (∀ x, 0 ≤ χ x) → Continuous W → (∃ x, χ x ≠ 0 ∧ W x ≠ 0) →
    0 < ∫ x, χ x * ‖W x‖ ^ 2 ∂μ
def AssemblyB : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : (T → E) → (T → E)) (χ : T → ℝ) (W : T → E),
    (∫ x, (inner ℂ (W x) (P (fun y => (χ y : ℂ) • W y) x) : ℂ) ∂μ) =
        ∫ x, (inner ℂ (W x) ((χ x : ℂ) • W x) : ℂ) ∂μ →
    0 < ∫ x, χ x * ‖W x‖ ^ 2 ∂μ →
    ¬ (P (fun y => (χ y : ℂ) • W y) =ᵐ[μ] 0)
def ConvArith : Prop :=
  ∀ c : ℝ, 0 < c → ∀ C₁ C₂ : ℝ, ∃ C : ℝ, ∀ r m : ℕ, 1 ≤ r → 1 ≤ m → m ≤ r → ∀ h A : ℝ,
    C * (r : ℝ) ^ 3 ≤ h → c * h / Real.sqrt m ≤ A → C₁ * (r : ℝ) ^ 2 + C₂ < A
def stdRep (n : ℕ) : Fin n → Fin n → Module.End ℂ (Fin n → ℂ) :=
  fun a b => Matrix.toLin' (Matrix.single a b (1 : ℂ))
def OmegaMatrix : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (x : ℂ) (ξ : Fin n → V),
    (x • (1 : Module.End ℂ (V ⊗[ℂ] (Fin n → ℂ))) - Formalism.REAL.Om (fun _ => true) E (stdRep n))
        (∑ c, ξ c ⊗ₜ[ℂ] (Pi.single c (1 : ℂ) : Fin n → ℂ)) =
      ∑ b, (∑ c, Formalism.REAL.Tm (fun a b => -E b a) x b c (ξ c)) ⊗ₜ[ℂ] (Pi.single b (1 : ℂ) : Fin n → ℂ) ∧
    (x • (1 : Module.End ℂ (V ⊗[ℂ] (Fin n → ℂ))) - Formalism.REAL.Om (fun _ => true) E (fun a b => -stdRep n b a))
        (∑ c, ξ c ⊗ₜ[ℂ] (Pi.single c (1 : ℂ) : Fin n → ℂ)) =
      ∑ a, (∑ c, Formalism.REAL.Tm E x a c (ξ c)) ⊗ₜ[ℂ] (Pi.single a (1 : ℂ) : Fin n → ℂ)
def NegTransposeGl : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → Formalism.REAL.GlRel (fun a b => -E b a)
def ResolventMinor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V),
    Formalism.REAL.GlRel E →
    ∀ (y : ℂ) (ξ η : Fin (m + 1) → V), (∀ j, ∑ l, Formalism.REAL.Tm E y j l (ξ l) = η j) →
      ∀ i, Formalism.REAL.qdet E (y + (m : ℂ)) (ξ i) =
        ∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (y + (m : ℂ)) (η j)
def ChainLabel {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) : Prop :=
  (∀ i ≤ 2 * r, ∀ j ≤ 2 * r, c i = c j → i = j) ∧ (∀ s < k, ∀ s' < k, w s = w s' → s = s') ∧
    (∀ i ≤ 2 * r, ∀ s < k, c i ≠ w s)
def ChainEquivariant {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] {n : ℕ} (r k : ℕ)
    (c w : ℕ → Fin n) (E : Fin n → Fin n → Module.End ℂ V) (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ)
    (ℓ : V →ₗ[ℂ] U) : Prop :=
  (∀ i ≤ 2 * r, ∀ j < i, ∀ v, ℓ (E (c i) (c j) v) = (if i = j + 1 then d j else 0) • ℓ v) ∧
    (∀ s < k, ∀ j < r, ∀ v, ℓ (E (w s) (c j) v) = 0) ∧
    (∀ s < k, ∀ i, r < i → i ≤ 2 * r → ∀ v, ℓ (E (c i) (w s) v) = 0) ∧
    (∀ s s' : Fin k, ∀ v, ℓ (E (w s) (w s') v) = π s s' (ℓ v))
def chainCol {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) : Fin (2 * r + k) → Fin n :=
  fun p => if (p : ℕ) < r then c p else if (p : ℕ) < r + k then w (p - r) else c (p - k)
def chainRow {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) : Fin (2 * r + k) → Fin n :=
  fun p => if (p : ℕ) < r then c (p + 1) else if (p : ℕ) < r + k then w (p - r) else c (p - k + 1)
def MinorExpand : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (n r k : ℕ) (c w : ℕ → Fin n)
    (E : Fin n → Fin n → Module.End ℂ V) (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U),
    ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    ∀ (x : ℂ) (v : V),
      ℓ (Formalism.REAL.qminor E (chainRow r k c w) (chainCol r k c w) x v) =
        (∏ j ∈ Finset.range (2 * r), d j) • Formalism.REAL.qdet π (x - (r : ℂ)) (ℓ v)
def ResolventChain : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (r k : ℕ)
    (c w : ℕ → Fin (2 * r + k + 1)) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V)
    (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U),
    Formalism.REAL.GlRel E → ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    ∀ (y : ℂ) (ξ : Fin (2 * r + k + 1) → V) (v : V),
      (∀ j, ∑ l, Formalism.REAL.Tm E y j l (ξ l) = if j = c 0 then v else 0) →
      ℓ (Formalism.REAL.qdet E (y + ((2 * r + k : ℕ) : ℂ)) (ξ (c (2 * r)))) =
        (∏ j ∈ Finset.range (2 * r), d j) • Formalism.REAL.qdet π (y + ((r + k : ℕ) : ℂ)) (ℓ v)
def ResolventFormula : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (r k : ℕ)
    (c w : ℕ → Fin (2 * r + k + 1)) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V)
    (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U)
    (lam : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℂ),
    Formalism.REAL.GlRel E → ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    (∀ (x : ℂ) (v : V), Formalism.REAL.qdet E x v = (∏ s, (x - ((2 * r + k : ℕ) : ℂ) / 2 + lam s)) • v) →
    (∀ (x : ℂ) (a : U), Formalism.REAL.qdet π x a = (∏ j, (x - ((k : ℂ) - 1) / 2 + u j)) • a) →
    ∀ (y : ℂ) (ξ : Fin (2 * r + k + 1) → V) (v : V),
      (∀ j, ∑ l, Formalism.REAL.Tm E y j l (ξ l) = if j = c 0 then v else 0) →
      (∏ s, (y + ((2 * r + k : ℕ) : ℂ) / 2 + lam s)) • ℓ (ξ (c (2 * r))) =
        ((∏ j ∈ Finset.range (2 * r), d j) * ∏ j, (y + ((2 * r + k + 1 : ℕ) : ℂ) / 2 + u j)) • ℓ v
def ResolventPF : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] (N : ℕ) (p : Fin N → Module.End ℂ E) (c : Fin N → ℂ)
    (Ω : Module.End ℂ E),
    ∑ i, p i = 1 → (∀ i j, p i * p j = if i = j then p i else 0) → Ω = ∑ i, c i • p i →
    ∀ x : ℂ, (∀ i, x ≠ c i) →
      (x • (1 : Module.End ℂ E) - Ω) * (∑ i, (x - c i)⁻¹ • p i) = 1 ∧
        (∑ i, (x - c i)⁻¹ • p i) * (x • (1 : Module.End ℂ E) - Ω) = 1
def Residue : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] (n k : ℕ) (lam : Fin n → ℂ) (u : Fin k → ℂ) (a : Fin n → E)
    (K : E) (s₀ s₁ : ℂ),
    Function.Injective lam → K ≠ 0 →
    (∀ x : ℂ, (∀ s, x + s₀ - lam s ≠ 0) →
      ∑ i, (x - (lam i - s₀))⁻¹ • a i = ((∏ j, (x + s₁ - u j)) / ∏ s, (x + s₀ - lam s)) • K) →
    ∀ i, (a i = 0 ↔ ∃ j, u j = lam i + (s₁ - s₀))
def CentreHalf : Prop :=
  ∀ k m : ℕ, 1 ≤ k → Even m → 2 ≤ m →
    (((k + m - 1 : ℕ) : ℝ) - 1) / 2 - ((m / 2 - 1 : ℕ) : ℝ) - ((k : ℝ) - 1) / 2 = 1 / 2
def cas {n : ℕ} (lam : Fin n → ℝ) : ℝ := ∑ a, lam a ^ 2 - ∑ a, Formalism.QuantumDeterminants.rhoStd n a ^ 2
def OmegaEig : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (i : Fin n),
    (cas (lam + Pi.single i 1) - cas lam -
        cas (Formalism.QuantumDeterminants.rhoStd n + Pi.single (⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ : Fin n) 1)) / 2 =
      lam i + (1 - (n : ℝ)) / 2
def OmegaEigDual : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (i : Fin n) (hn : 0 < n),
    (cas (lam - Pi.single i 1) - cas lam -
        cas (Formalism.QuantumDeterminants.rhoStd n - Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) / 2 =
      -lam i + (1 - (n : ℝ)) / 2
def CasHWVal : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ),
    ∑ a : Fin n, μ a * (μ a + (n : ℝ) - 1 - 2 * (a : ℕ)) = cas (μ + Formalism.QuantumDeterminants.rhoStd n)
def CasCval : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ),
    Formalism.REAL.cval (fun a => (μ a : ℂ)) = ((cas (μ + Formalism.QuantumDeterminants.rhoStd n) : ℝ) : ℂ)
def InterlaceUL (k n : ℕ) (u lam : ℕ → ℝ) : Prop :=
  (∀ i, i + 1 < k → lam i < u i ∧ u (i + 1) < lam i) ∧
    (∀ s, k - 1 ≤ s → s < n → lam s < u (k - 1)) ∧
    (∀ s, s + 1 < n → lam (s + 1) < lam s)
def MoveInterlace : Prop :=
  ∀ (k n : ℕ) (u lam : ℕ → ℝ), 1 ≤ k → k ≤ n → InterlaceUL k n u lam →
    (∀ j < k, ∀ s < n, ∃ z : ℤ, u j - lam s = (z : ℝ) + 1 / 2) →
    (∀ s, k - 1 ≤ s → s + 1 < n → 1 < lam s - lam (s + 1)) →
    ∀ i < n,
      (InterlaceUL k n u (Function.update lam i (lam i + 1)) ↔ ¬ ∃ j < k, u j = lam i + 1 / 2) ∧
      (InterlaceUL k n u (Function.update lam i (lam i - 1)) ↔ ¬ ∃ j < k, u j = lam i - 1 / 2)
def PathGaps : Prop :=
  ∀ (m : ℕ) (h : ℝ) (b b0 : ℕ → ℝ), (∀ i, i + 1 < m → h ≤ b (i + 1) - b i) →
    (∀ i, i + 1 < m → h ≤ b0 (i + 1) - b0 i) → (∀ i < m, b i ≤ b0 i) →
    ∀ j < m, ∀ b' : ℝ, b j ≤ b' → b' ≤ b0 j → ∀ c : ℕ → ℝ,
      (∀ i, c i = if i < j then b i else if i = j then b' else b0 i) →
      ∀ i, i + 1 < m → h ≤ c (i + 1) - c i
def PathNoPole : Prop :=
  ∀ (m : ℕ) (h : ℝ) (c : ℕ → ℝ), 1 / 2 ≤ h → (∀ i, i + 1 < m → h ≤ c (i + 1) - c i) →
    ∀ x : ℝ, -c 0 < x → ∀ j, 1 ≤ j → j < m → x ≠ -c j + 1 / 2
def MemLp_two_of_one_top : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] (f : X → E),
    MemLp f 1 μ → MemLp f ⊤ μ → MemLp f 2 μ
end Formalism.HermitianLatticeCounting.S8


