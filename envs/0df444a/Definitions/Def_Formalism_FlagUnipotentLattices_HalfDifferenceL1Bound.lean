-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
-- name    : Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:47.910334+00:00
-- url     : https://prove2.me/theorems/42aa80c5-cfcb-4c7d-b428-bd80662f7e8f
-- title:
--   Half Difference L1 Bound
-- statement:
--   Definitions and structural lemmas for Half Difference L1 Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/HalfDifferenceL1Bound.lean

import Mathlib
import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LatticeRigidity_StatementD
import Definitions.Def_Formalism_LatticeRigidity_HeightMin
import Definitions.Def_Formalism_LatticeRigidity_PackCount
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_StatementCor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField
open scoped ComplexOrder
noncomputable section
namespace Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
def decExp (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := h / 8 * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ)))
def Ydat (n f : ℕ) (rd g b : ℝ) : ℝ := (n : ℝ) * f * rd * g * b
def epsN (c : ℝ) (n f : ℕ) : ℝ := c / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)
def hsG {ι : Type} [Fintype ι] (Y : Matrix ι ι ℂ) : ℝ := Real.sqrt (∑ a, ∑ b, ‖Y a b‖ ^ 2)
def ThreshHead : Prop :=
  ∀ C₂ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ (n q f : ℕ) (b rd h : ℝ), 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n → 2 ≤ b →
    1 ≤ rd → C * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ C₂ * (n : ℝ) ^ 2 * Real.sqrt q ≤ h ∧
      32 * (n : ℝ) * q < h
def ThreshHaar : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 1 ≤ n → 1 ≤ q → 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
    32 * (n : ℝ) * q < h
def HaarCompare : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 1 ≤ q →
    (32 * (n : ℝ) * q < h ↔
      2 * (n : ℝ) * Real.sqrt (2 * (q : ℝ)) < h / 8 / Real.sqrt (2 * (q : ℝ)))
def PowerDecayIntegrable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (q : ℕ) (h B r : ℝ), 1 ≤ q → 1 ≤ r → 0 ≤ B →
    B < h / 8 / Real.sqrt (2 * (q : ℝ)) →
    Integrable (fun X : V => Real.exp (-(decExp h q ‖X‖)) ^ r * Real.exp (B * ‖X‖))
      (volume : Measure V)
def ThreshCusp : Prop :=
  ∃ C : ℝ, ∀ (n q : ℕ) (h : ℝ), 1 ≤ q → q ≤ n → C * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    2 * (n : ℝ) * Real.sqrt (2 * (q : ℝ)) + 2 * (n : ℝ) ^ 2 < h / 8 / Real.sqrt (2 * (q : ℝ))
def ExpQuad : Prop := ∀ y : ℝ, |y| ≤ 1 → 1 + y + y ^ 2 / 3 ≤ Real.exp y
def LogQuarter : Prop := ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x / 4 ≤ Real.log (1 + x / 3)
def ConvexChord : Prop :=
  ∀ (F : ℝ → ℝ) (t : ℝ), ConvexOn ℝ (Set.Icc 0 1) F → F 0 = 0 → 0 < t → t ≤ 1 → F t / t ≤ F 1
def GapSum : Prop :=
  ∀ (lam : ℕ → ℝ) (a b : ℕ), b ≤ a →
    ∑ i ∈ Ico b a, (lam i - lam (i + 1) + 1) = lam b - lam a + ((a : ℝ) - b)
def ResolutionNorm : Prop :=
  ∀ (Ω T : Type) [MeasurableSpace Ω] (μ : Measure Ω) [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] (v : Ω → T) (c : Ω → ℝ) (M : ℝ) (A : T →L[ℂ] T), 0 ≤ M →
    (∀ x y : T, (∫ k, inner ℂ x (v k) * inner ℂ (v k) y ∂μ) = inner ℂ x y) →
    (∀ k, |c k| ≤ M) →
    (∀ x y : T, inner ℂ x (A y) = ∫ k, (c k : ℂ) * (inner ℂ x (v k) * inner ℂ (v k) y) ∂μ) →
    ‖A‖ ≤ M
def ConjInv : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (k X : Matrix (Fin N) (Fin N) ℂ),
    k ∈ Matrix.unitaryGroup (Fin N) ℂ → (∀ a b, ep a ≠ ep b → k a b = 0) →
    X.IsHermitian → (∀ a b, ep a = ep b → X a b = 0) →
    (k.conjTranspose * X * k).IsHermitian ∧
      (∀ a b, ep a = ep b → (k.conjTranspose * X * k) a b = 0) ∧
      hs (k.conjTranspose * X * k) = hs X ∧
      k.conjTranspose * NormedSpace.exp X * k = NormedSpace.exp (k.conjTranspose * X * k)
def DecayRightSide : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (lam : ℕ → ℝ) (h : ℝ) (Ω T : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [NormedAddCommGroup T] [InnerProductSpace ℂ T]
    (κ : Ω → Matrix (Fin N) (Fin N) ℂ) (v : Ω → T) (X : Matrix (Fin N) (Fin N) ℂ)
    (A : T →L[ℂ] T),
    (∀ i, 1 ≤ i → i < N → lam (i + 1) < lam i) →
    (∀ a b : Fin N, b < a → ep a ≠ ep b → h ≤ lam (b.val + 1) - lam (a.val + 1)) →
    (∀ k, κ k ∈ Matrix.unitaryGroup (Fin N) ℂ ∧ ∀ a b, ep a ≠ ep b → κ k a b = 0) →
    X.IsHermitian → (∀ a b, ep a = ep b → X a b = 0) →
    (∀ x y : T, (∫ k, inner ℂ x (v k) * inner ℂ (v k) y ∂μ) = inner ℂ x y) →
    (∀ x y : T, inner ℂ x (A y) =
      ∫ k, ((∏ i ∈ Ico 1 N,
          (lead ((κ k).conjTranspose * NormedSpace.exp X * κ k) i).re
            ^ (-(lam i - lam (i + 1) + 1)) : ℝ) : ℂ)
        * (inner ℂ x (v k) * inner ℂ (v k) y) ∂μ) →
    ‖A‖ ≤ Real.exp (-(decExp h (q0 ep) (hs X)))
def DecAssembly : Prop :=
  Formalism.NuclearRankWeightBounds.D.Decay → ResolutionNorm → ConjInv → GapSum → DecayRightSide
def UnitaryLeft : Prop :=
  ∀ (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] (U A : T →L[ℂ] T),
    (∀ x, ‖U x‖ = ‖x‖) → ‖U ∘L A‖ = ‖A‖
def CoeffLeOp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E U : H →L[ℂ] H) (w : H),
    (∀ x y, inner ℂ (E x) y = inner ℂ x (E y)) → E w = w → ‖w‖ = 1 →
    ‖inner ℂ w (U w)‖ ≤ ‖E ∘L U ∘L E‖
def MinorTriangular : Prop :=
  ∀ (N : ℕ) (b x : Matrix (Fin N) (Fin N) ℂ) (i : ℕ), i ≤ N →
    (∀ r c : Fin N, r < c → b r c = 0) →
    lead (b * x * b.conjTranspose) i =
      ((∏ a ∈ univ.filter (fun a : Fin N => a.val < i), ‖b a a‖ ^ 2 : ℝ) : ℂ) * lead x i
def Phi {N : ℕ} (L : ℕ → ℝ) (x : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (lead x N).re ^ (-(L N)) * ∏ i ∈ Ico 1 N, (lead x i).re ^ (-(L i - L (i + 1)))
def PhiEquivariant : Prop :=
  ∀ (N : ℕ) (L : ℕ → ℝ) (b x : Matrix (Fin N) (Fin N) ℂ), x.PosDef →
    (∀ r c : Fin N, r < c → b r c = 0) → (∀ a, b a a ≠ 0) →
    Phi L (b * x * b.conjTranspose) = (∏ a : Fin N, ‖b a a‖ ^ (-(2 * L (a.val + 1)))) * Phi L x
def ProjCoeff : Prop :=
  ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : G → H →L[ℂ] H)
    (P : H →L[ℂ] H) (m : G → ℂ),
    (∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) → (∀ g, P ∘L U g ∘L P = m g • P) →
    ∀ v, P v = v → ‖v‖ = 1 → ∀ g, inner ℂ v (U g v) = m g
def CoeffIso : Prop :=
  ∀ (G H₁ H₂ : Type) [Group G] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (U₁ : G →* (H₁ →L[ℂ] H₁)) (U₂ : G →* (H₂ →L[ℂ] H₂)),
    (∀ g x, ‖U₁ g x‖ = ‖x‖) → (∀ g x, ‖U₂ g x‖ = ‖x‖) →
    ∀ (v₁ : H₁) (v₂ : H₂), (∀ g, inner ℂ v₁ (U₁ g v₁) = inner ℂ v₂ (U₂ g v₂)) →
      (Submodule.span ℂ (Set.range fun g => U₂ g v₂)).topologicalClosure = ⊤ →
      ∃ J : H₂ →ₗᵢ[ℂ] H₁, J v₂ = v₁ ∧ (∀ g x, J (U₂ g x) = U₁ g (J x)) ∧
        Set.range J = ((Submodule.span ℂ (Set.range fun g => U₁ g v₁)).topologicalClosure : Set H₁)
def RankOne : Prop :=
  ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : G → H →L[ℂ] H)
    (P : H →L[ℂ] H) (m : G → ℂ),
    (∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) → (∀ g, P ∘L U g ∘L P = m g • P) →
    ∀ v, P v = v → (Submodule.span ℂ (Set.range fun g => U g v)).topologicalClosure = ⊤ →
    ∀ v', P v' = v' → ∃ c : ℂ, v' = c • v
def PsInv : Prop :=
  ∀ (G N : Type) [Group G] [Group N] [MeasurableSpace N] [MeasurableInv N] (ν : Measure N)
    [ν.IsInvInvariant] (j : N →* G) (m : G) (cj : N ≃ᵐ N) (δ : ℝ) (Ph : G → ℝ), 0 ≤ δ →
    (∀ n, j (cj n) = m⁻¹ * j n * m) → ν.map cj = ENNReal.ofReal δ • ν →
    (∀ g, Ph g⁻¹ = Ph g) →
    (∫ n, Ph (m⁻¹ * j n) ∂ν) = δ * ∫ n, Ph (m * j n) ∂ν
def HalfDifferenceL1Bound : Prop :=
  ∀ (M : Type) [Group M] [MeasurableSpace M] [MeasurableInv M] (μ : Measure M) [μ.IsInvInvariant]
    (ps δ : M → ℝ), (∀ m, 0 ≤ ps m) → (∀ m, 0 < δ m) → Measurable δ → Integrable ps μ →
    (∀ m, ps m⁻¹ = δ m * ps m) →
    Integrable (fun m => δ m * ps m) μ ∧ Integrable (fun m => Real.sqrt (δ m) * ps m) μ
def KernelBound : Prop :=
  ∀ (X ι : Type) [MeasurableSpace X] (μ : Measure X) [Fintype ι] [DecidableEq ι] (F : ι → X → ℂ)
    (c : ι → ℂ), (∀ w, MemLp (F w) 2 μ) →
    (∀ w w', (∫ x, star (F w x) * F w' x ∂μ) = if w = w' then 1 else 0) →
    ∀ y, ‖∑ w, c w * F w y‖ ^ 2 ≤ (∫ x, ‖∑ w, c w * F w x‖ ^ 2 ∂μ) * ∑ w, ‖F w y‖ ^ 2
def TraceDiag : Prop :=
  ∀ (X ι : Type) [MeasurableSpace X] (μ : Measure X) [Fintype ι] [DecidableEq ι] (F : ι → X → ℂ),
    (∀ w w', (∫ x, star (F w x) * F w' x ∂μ) = if w = w' then 1 else 0) →
    (∫ x, ∑ w, ‖F w x‖ ^ 2 ∂μ) = Fintype.card ι
def IsPosType {G : Type} [Group G] (e : G → ℂ) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ), 0 ≤ ∑ x ∈ s, ∑ y ∈ s, star (c x) * c y * e (x⁻¹ * y)
def PosTypeBound : Prop :=
  ∀ (G : Type) [Group G] (e : G → ℂ), IsPosType e → ∀ x, ‖e x‖ ≤ (e 1).re
def TauLip : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X k Y : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    (∀ v, k v ∈ Matrix.unitaryGroup ι ℂ) → (∀ v, (Y v).IsHermitian) →
    ∀ L : Submodule (𝓞 K) V, L.FG → L ≠ ⊥ →
      Formalism.HN.leastSize b X L * Real.exp (-(1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, hsG (Y v)) ≤
        Formalism.HN.leastSize b (fun v => X v * (k v * NormedSpace.exp (Y v))) L
def NearPowBound : Prop :=
  ∀ (N : ℕ) (x k X γ : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ), IsUnit x →
    k ∈ Matrix.unitaryGroup (Fin N) ℂ → X.IsHermitian → hs X ≤ ε → (N : ℝ) * ε ≤ 1 →
    x⁻¹ * γ * x = k * NormedSpace.exp X →
    ((x⁻¹).conjTranspose * x⁻¹).PosDef ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ N →
        ((Real.exp 1 ^ 2 : ℝ) • ((x⁻¹).conjTranspose * x⁻¹)
          - (γ ^ j).conjTranspose * ((x⁻¹).conjTranspose * x⁻¹) * γ ^ j).PosSemidef
def TraceOpBound : Prop :=
  ∀ (N : ℕ) (A H : Matrix (Fin N) (Fin N) ℂ) (ρ : ℝ), 0 ≤ ρ → H.PosDef →
    ((ρ ^ 2 : ℝ) • H - A.conjTranspose * H * A).PosSemidef → ‖A.trace‖ ≤ N * ρ
def NormForces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : 𝓞 E) (g : ℕ), ((g : ℕ) : 𝓞 E) ∣ α →
    (∀ φ : E →+* ℂ, ‖φ (α : E)‖ < g) → α = 0
def TracePowers : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K),
    (∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) → (A - 1) ^ n = 0
def UnipTrace : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K), (A - 1) ^ n = 0 → A.trace = n
def NearIdentity : Prop :=
  ∀ (N : ℕ) (k X : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ), k ∈ Matrix.unitaryGroup (Fin N) ℂ →
    X.IsHermitian → hs X ≤ ε → ε ≤ 1 / 4 → (k * NormedSpace.exp X).trace = N →
    (N : ℝ) - 2 * N * ε ≤ k.trace.re ∧ hs (k - 1) ^ 2 = 2 * ((N : ℝ) - k.trace.re) ∧
      hs (k * NormedSpace.exp X - 1) ≤ 3 * Real.sqrt (N * ε)
def DeltaSmall : Prop :=
  ∀ (n q f : ℕ) (c : ℝ), 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n → 0 < c → c ≤ 1 / 90000 →
    3 * Real.sqrt (n * epsN c n f) * q * n * f ≤ 1 / 100 ∧
      3 * Real.sqrt (n * epsN c n f) < 1 / 4 ∧ (n : ℝ) * epsN c n f ≤ 1 ∧ epsN c n f ≤ 1 / 4
def FibreCount : Prop :=
  ∀ (α : Type) (S : Finset α) (r : ℕ) (β : ℕ → Type) (π : ∀ i, α → β i) (c : ℕ → ℝ),
    (∀ i, 0 ≤ c i) → (∀ x ∈ S, ∀ y ∈ S, π 0 x = π 0 y) →
    (∀ x ∈ S, ∀ y ∈ S, π r x = π r y → x = y) →
    (∀ i, i < r → ∀ T : Finset α, T ⊆ S → (∀ y ∈ T, ∀ z ∈ T, π i y = π i z) →
      (∀ y ∈ T, ∀ z ∈ T, π (i + 1) y = π (i + 1) z → y = z) → (T.card : ℝ) ≤ c i) →
    (S.card : ℝ) ≤ ∏ i ∈ range r, c i
def NearDiff : Prop :=
  ∀ (N : ℕ) (γ₀ γ : Matrix (Fin N) (Fin N) ℂ) (de : ℝ), de < 1 / 4 → hs (γ₀ - 1) ≤ de →
    hs (γ - 1) ≤ de → IsUnit γ₀ ∧ hs (γ₀⁻¹ * γ - 1) ≤ 3 * de
def wt (a : ℕ) (z : ℤ) : ℤ := z.sign * 4 ^ (a + 1 - z.natAbs)
def WeightGaps : Prop :=
  ∀ (a : ℕ) (x y x' y' : ℤ), x.natAbs ≤ a → y.natAbs ≤ a → x'.natAbs ≤ a → y'.natAbs ≤ a →
    0 < wt a y - wt a x → wt a y - wt a x = wt a y' - wt a x' →
    (x' = x ∧ y' = y) ∨ (x' = -y ∧ y' = -x)
def dimN {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : ℕ :=
  (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y)
    + (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y)
    + (∑ x, j x ^ 2) + ∑ x, 2 * j x * n0
def DimIdentity : Prop :=
  ∀ (a : ℕ) (j : Fin a → ℕ) (n0 : ℕ),
    (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 2 * (∑ x, j x ^ 2) + 2 * dimN j n0 ∧
      dimN j n0 ≤ 2 * (∑ x, j x) * (n0 + 2 * ∑ x, j x) ∧
      (n0 : ℝ) ^ 2 / 2 + (∑ x, (j x : ℝ) ^ 2) + (dimN j n0 : ℝ) / 2
          - ((n0 : ℝ) + 2 * ∑ x, (j x : ℝ)) ^ 2 / 2 = -((dimN j n0 : ℝ) / 2)
def Vsph (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, 2 * Real.pi ^ l / ((l - 1).factorial : ℝ)
def VRatio : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (p q a : ℕ) (j : Fin a → ℕ), (∑ x, j x) ≤ q → q ≤ p →
    Vsph p * Vsph q / (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)) ≤
      C ^ ((∑ x, j x) * (p + q)) * (C / (p : ℝ)) ^ ((∑ x, j x) * (p - ∑ x, j x))
        * ((∑ x, j x : ℕ) : ℝ) ^ (((∑ x, j x : ℕ) : ℝ) ^ 2 / 2)
def KappaBound : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (n p q J a f dN : ℕ) (v res ℓ : ℝ),
    n₀ ≤ n → p + q = n → q ^ 2 ≤ n → 1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f → dN ≤ 2 * J * n →
    1 / 2 ≤ v → 0 < ℓ → Real.log ℓ ≤ n → 0 ≤ res → res ≤ (C * ℓ) ^ (2 * f) →
    v ^ (-((f : ℝ) * dN / 2)) * C ^ (J * n * f) * res ^ a
        * ((C / (p : ℝ)) ^ (J * (p - J)) * (J : ℝ) ^ ((J : ℝ) ^ 2 / 2)) ^ f ≤
      Real.exp (-(c * J * n * f * Real.log n))
def NearProduct : Prop :=
  ∀ (R : Type) [Fintype R] (la : R → ℝ) (d : R → ℕ) (n q J f : ℕ) (de k : ℝ),
    (∀ r, 0 < la r ∧ la r < 1) → 0 ≤ de → 0 ≤ k → k ≤ 24 → ∑ r, d r ≤ 2 * J * n → J ≤ q →
    de * q * n * f ≤ 1 / 100 →
    (∏ r, (1 + k * de / la r) ^ (d r * f)) * (∏ r, la r ^ (d r * f)) ≤ 2
def LogVolume : Prop :=
  ∀ (f j : ℕ) (ts : ℝ), 0 < ts → ts ≤ 1 / 2 →
    (∫ t in ts..(1 / 2 : ℝ), 2 * (f : ℝ) * j / t) = 2 * (f : ℝ) * j * Real.log (1 / (2 * ts))
def TypeCount : Prop :=
  ∀ q : ℕ, ∑ J ∈ Icc 1 q, Fintype.card (Composition J) ≤ 2 ^ q
def NearTotal : Prop :=
  ∀ c C : ℝ, 0 < c → 1 ≤ C → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ,
    ∀ (n q J a f : ℕ) (rd g b : ℝ), n₀ ≤ n → q ^ 2 ≤ n → 1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f →
    Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ C → 1 ≤ rd →
    Real.log (Real.log rd) ≤ n → Real.log (Real.log b) ≤ c₁ * n * f * Real.log n →
    (2 : ℝ) ^ q * (2 * Real.exp (-(c * J * n * f * Real.log n)))
        * (C * f * (q : ℝ) ^ 2 * Real.log (Ydat n f rd g b)) ^ a ≤
      Real.exp (-(c₂ * n * f * Real.log n))
def FarCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) (r : ι → ℝ) (τ k : ℝ), 0 < τ → τ ≤ 1 → 1 ≤ k →
    (∀ v, 0 ≤ r v) →
    (1 + 2 * (∏ v, k * Real.exp (r v)) ^ ((1 : ℝ) / Fintype.card ι) / τ ^ 2)
        ^ (2 * n ^ 2 * Fintype.card ι) ≤
      (3 * k / τ ^ 2) ^ (2 * n ^ 2 * Fintype.card ι) * Real.exp (2 * (n : ℝ) ^ 2 * ∑ v, r v)
def MinLinear : Prop :=
  ∀ (q : ℕ) (ε s : ℝ), 1 ≤ q → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → ε ≤ s →
    ε * s ≤ min (s ^ 2) (s / Real.sqrt (2 * (q : ℝ)))
open Classical in

def FarSum : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h ε : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 ≤ B → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → B * ε ≤ 1 →
    32 * B ≤ h * ε → 16 ≤ h * ε ^ 2 →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) → (∀ γ ∈ S, ∃ v, ε < d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤
      A * 4 ^ Fintype.card ι * (2 * Fintype.card ι) * Real.exp (-(h * ε ^ 2 / 16))
def ThreshFar : Prop :=
  ∀ C' c Cg : ℝ, 0 < C' → 0 < c → 1 ≤ Cg → ∃ C : ℝ, 0 < C ∧
    ∀ (n q f : ℕ) (rd g b h : ℝ), 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n → Real.log f ≤ Real.sqrt n →
    2 ≤ b → 1 ≤ rd → 1 ≤ g → g ≤ b ^ Cg →
    C * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
    C' * (n : ℝ) ^ 2 * q * f * Real.log (Ydat n f rd g b) ≤ h * epsN c n f ^ 2
def FarPrefactor : Prop :=
  ∀ (n f : ℕ) (τs : ℝ), 1 ≤ n → 1 ≤ f → 0 < τs → (n : ℝ) * τs ≤ 1 →
    (3 * Real.sqrt n / τs ^ 2) ^ (2 * n ^ 2 * f) * 4 ^ f ≤ (3 / τs) ^ (5 * n ^ 2 * f)
def FarNegligible : Prop :=
  ∀ (C C₁ c : ℝ) (m : ℕ), 1 ≤ C → 1 ≤ C₁ → 0 < c → ∃ C' : ℝ, 0 < C' ∧
    ∀ (n q f : ℕ) (rd g b x : ℝ), 1 ≤ n → 1 ≤ q → 1 ≤ f → 1 ≤ rd → 1 ≤ g → 2 ≤ b →
    C' * (n : ℝ) ^ 2 * q * f * Real.log (Ydat n f rd g b) ≤ x →
    (C / Ydat n f rd g b ^ (-(C₁ * q))) ^ (m * n ^ 2 * f) * (2 * f) * Real.exp (-(x / 16)) ≤
      Real.exp (-(c * n * f * Real.log n))
def TauIntegral : Prop :=
  ∀ (f j n0 : ℕ), 1 ≤ f → 1 ≤ j → 1 ≤ n0 →
    (∫ t in (0 : ℝ)..(1 / 2 : ℝ), t ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / t)) =
      (1 / 2 : ℝ) ^ (2 * j * n0 * f) / n0
def ProbINonzero : Prop :=
  ∀ c : ℝ, 0 < c → ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ n₀ : ℕ, ∀ (n q J f : ℕ), n₀ ≤ n → q ^ 2 ≤ n → 1 ≤ J →
    1 ≤ f →
    (2 : ℝ) ^ q * Real.exp (-(c * J * n * f * Real.log n)) ≤ Real.exp (-(c₂ * n * f * Real.log n))
def GapPigeonhole : Prop :=
  ∀ (a q : ℕ) (τ : ℕ → ℝ), 1 ≤ a → a ≤ q → (∀ i, 0 < τ i) → τ (a + 1) = 1 / 2 → τ 1 < 1 / 2 →
    ∃ b', 1 ≤ b' ∧ b' ≤ a ∧ τ b' / τ (b' + 1) ≤ (2 * τ 1) ^ ((1 : ℝ) / q)
def CoverRadius : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) ^ 3 / (2 * κ)
def CoverArith : Prop :=
  ∀ (n f N : ℕ) (rd ρ : ℝ), 1 ≤ f → N ≤ 2 * n ^ 2 * f → 0 < rd → 0 < ρ →
    (N : ℝ) / 2 / (Real.sqrt f / (2 * rd * ρ)) ≤ 2 * (n : ℝ) ^ 2 * Real.sqrt f * rd * ρ ∧
      (N : ℝ) ^ 2 / (Real.sqrt f / (2 * rd * ρ)) ≤
        8 * (n : ℝ) ^ 4 * (f : ℝ) ^ ((5 : ℝ) / 2) * rd * ρ ∧
      (N : ℝ) ^ 3 / (2 * (Real.sqrt f / (2 * rd * ρ))) ≤
        8 * (n : ℝ) ^ 6 * (f : ℝ) ^ ((5 : ℝ) / 2) * rd * ρ
def MeanZeroSup : Prop :=
  ∀ (X H : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (φ : X → H) (M : ℝ),
    Integrable φ μ → (∫ x, φ x ∂μ) = 0 → (∀ x y, ‖φ x - φ y‖ ≤ M) → ∀ x, ‖φ x‖ ≤ M
def IterSup : Prop :=
  ∀ (a θ : ℕ → ℝ) (Θ : ℝ) (P₀ : ℕ), (∀ P, P < P₀ → 0 ≤ θ P ∧ θ P ≤ Θ) → (∀ P, 0 ≤ a P) →
    (∀ P, P < P₀ → a P ≤ θ P * a (P + 1)) → a 0 ≤ Θ ^ P₀ * a P₀
def P0 (n q f : ℕ) : ℕ := 8 * q * n ^ 2 * f
def b1 (n q f : ℕ) (b : ℝ) : ℝ := b ^ 2 + 2 * (P0 n q f : ℝ) * n
def DeepChain : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n q f : ℕ) (rd g b τ₁ τs ρ Kxx Bs D volG volK : ℝ), 1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f →
    1 ≤ rd → 1 ≤ g → 2 ≤ b → 0 < τ₁ → τ₁ < τs → 0 ≤ D → 0 < volK → 0 ≤ volG → 0 ≤ ρ →
    ρ ≤ C * (n : ℝ) ^ 2 * f * g * rd * (2 * τ₁) ^ ((1 : ℝ) / q) →
    Kxx ≤ (C * ρ * (n : ℝ) ^ 2 * f * b1 n q f b) ^ (2 * P0 n q f) * Bs →
    Bs ≤ D * volK⁻¹ * (C * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (C / τ₁) ^ (4 * n ^ 2 * f) →
    volG / volK ≤ (C * n * rd * g) ^ (n ^ 2 * f) →
    volG * Kxx ≤ D * Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * f)
      * (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
      * τs ^ (12 * n ^ 2 * f)
def DeepBound : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C₁ : ℝ, 1 ≤ C₁ ∧
    ∀ (n q f : ℕ) (rd g b : ℝ), 1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f → 1 ≤ rd → 1 ≤ g → 2 ≤ b →
    Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f)
        * (C * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
        * (Ydat n f rd g b ^ (-(C₁ * q))) ^ (12 * n ^ 2 * f) ≤
      Real.exp (-((n : ℝ) ^ 2 * f))
def DeepChainY : Prop :=
  ∀ (C : ℝ) (n q f : ℕ) (Y τ₁ τs θ Kxx Bs D volG volK : ℝ), 0 ≤ C → 1 ≤ q → 2 ≤ Y → 0 < τ₁ →
    τ₁ < τs → 0 ≤ D → 0 < volK → 0 ≤ volG → 0 ≤ θ →
    θ ≤ Y ^ C * (2 * τ₁) ^ ((1 : ℝ) / q) →
    Kxx ≤ θ ^ (2 * P0 n q f) * Bs →
    Bs ≤ Y ^ (C * (n : ℝ) ^ 2 * f) * (1 / τ₁) ^ (4 * n ^ 2 * f) * D / volK →
    volG / volK ≤ Y ^ (C * (n : ℝ) ^ 2 * f) →
    volG * Kxx ≤ D * Y ^ ((16 * q * C + 2 * C + 16) * (n : ℝ) ^ 2 * f) * τs ^ (12 * n ^ 2 * f)
def DeepBoundY : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (n q f : ℕ) (Y : ℝ), 1 ≤ q → 2 ≤ Y →
    Y ^ ((16 * q * C + 2 * C + 16) * (n : ℝ) ^ 2 * f) * (Y ^ (-(C₁ * q))) ^ (12 * n ^ 2 * f) ≤
      Real.exp (-((n : ℝ) ^ 2 * f))
def Sobolev1 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H)
    (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivWithinAt φ (φ' t) (Set.Icc 0 s) t) →
    ContinuousOn φ' (Set.Icc 0 s) →
    ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * (∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2)
def DiagSplit : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (K Rm : X → ℝ)
    (Mod : Set X) (k0 : ℝ), MeasurableSet Mod → Integrable K μ → (∀ x ∈ Mod, K x = k0 + Rm x) →
    (∫ x, K x ∂μ) = k0 * μ.real Mod + (∫ x in Mod, Rm x ∂μ) + (∫ x in Modᶜ, K x ∂μ)
def FinalSum : Prop :=
  ∀ c A : ℝ, 0 < c → 0 ≤ A → ∃ c' : ℝ, 0 < c' ∧ ∃ n₀ : ℕ,
    ∀ (n f : ℕ) (D Ds pr E₁ E₂ : ℝ), n₀ ≤ n → 1 ≤ f → 0 ≤ D → 0 ≤ Ds → pr ≤ 1 →
    1 - Real.exp (-(c * n * f * Real.log n)) ≤ pr →
    |E₁| ≤ A * Real.exp (-(c * n * f * Real.log n)) * Ds →
    |E₂| ≤ A * Real.exp (-((n : ℝ) ^ 2 * f)) * D →
    D = Ds * pr + E₁ + E₂ →
    |D - Ds| ≤ Real.exp (-(c' * n * f * Real.log n)) * Ds
end Formalism.HermitianLatticeCounting.S7


