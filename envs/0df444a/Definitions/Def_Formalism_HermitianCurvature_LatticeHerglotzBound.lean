-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
-- name    : Formalism_HermitianCurvature_LatticeHerglotzBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:39.377442+00:00
-- url     : https://prove2.me/theorems/68168a2e-e78e-456b-8927-2caa48bcccb2
-- title:
--   Lattice Herglotz Bound
-- statement:
--   Definitions and structural lemmas for Lattice Herglotz Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/LatticeHerglotzBound.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.crystallineComparison
open MeasureTheory Filter Topology Finset
noncomputable section
open Classical
abbrev V (f : ℕ) := Fin f → ℂ
def Vx (f : ℕ) : Set (V f) := {z | ∀ v, z v ≠ 0}
def mfac (K : ℕ) (L a : ℝ) : ℝ := if a = 0 then 1 else min 1 ((L / a) ^ K)
def mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (σ : V f) : ℝ := ∏ v, mfac K (L v) ‖σ v‖
def pat {f : ℕ} (L : Fin f → ℝ) (σ : V f) : Finset (Fin f) := univ.filter (fun v => L v < ‖σ v‖)
def psi {f : ℕ} (z : V f) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (z v + starRingEnd ℂ (z v)))
def dualSet {f : ℕ} (La : Submodule ℤ (V f)) : Set (V f) := {σ | ∀ z ∈ La, psi (σ * z) = 1}
def fourier {f : ℕ} (g : V f → ℝ) (σ : V f) : ℂ := ∫ z, (g z : ℂ) * psi (σ * z)
def PDOn {f : ℕ} (T : Set (V f)) (A : V f → ℂ) : Prop :=
  ∀ (S : Finset (V f)) (c : V f → ℂ), (∀ σ ∈ S, σ ∈ T) →
    0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re
def Bdd {α : Type} (g : α → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B
def IsMean {Λ : Type} [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) : Prop :=
  (∀ g h, Bdd g → Bdd h → LIM (g + h) = LIM g + LIM h) ∧
  (∀ (c : ℂ) g, Bdd g → LIM (c • g) = c * LIM g) ∧
  (∀ g, Bdd g → (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) → 0 ≤ (LIM g).re ∧ (LIM g).im = 0) ∧
  LIM (fun _ => 1) = 1 ∧
  (∀ g (σ : Λ), Bdd g → LIM (fun x => g (x + σ)) = LIM g)
def atInfAll (f : ℕ) : Filter (V f) :=
  ⨅ v : Fin f, Filter.comap (fun x : V f => ‖x v‖) Filter.atTop
def IsMeanInf {f : ℕ} (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) : Prop :=
  IsMean LIM ∧ ∀ g : Λ → ℂ, Bdd g →
    Tendsto g (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) (𝓝 0) → LIM g = 0
def MajIntegral : Prop :=
  ∀ (K : ℕ) (x : ℝ), 2 < K → 0 < x →
    Integrable (fun l : ℂ => mfac K x ‖l‖) ∧
      ∫ l : ℂ, mfac K x ‖l‖ = Real.pi * x ^ 2 * K / ((K : ℝ) - 2)
def MajIntegralProd : Prop :=
  ∀ (f K : ℕ) (x : Fin f → ℝ), 2 < K → (∀ v, 0 < x v) →
    Integrable (fun l : V f => mL K x l) ∧
      ∫ l : V f, mL K x l = ∏ v, (Real.pi * x v ^ 2 * K / ((K : ℝ) - 2))
def LatticeSummable : Prop :=
  ∀ (f K : ℕ) (L : Fin f → ℝ) (La : Submodule ℤ (V f)) [DiscreteTopology La], 2 < K →
    (∀ v, 0 < L v) → Summable (fun σ : La => mL K L (σ : V f))
def DensityChange : Prop :=
  ∀ (s M : ℕ) (t : ℂ) (g : ℂ → ENNReal), 1 ≤ s → 2 ≤ M → t ≠ 0 → Measurable g →
    ∫⁻ c : ℂ, ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) * ‖c‖ ^ (2 * (M - 2)) /
          (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
        ((Polynomial.nthRoots s ((-1) ^ (s + 1) * (c * t ^ (s - 1)))).map
          (fun z => ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z)).sum
      = ∫⁻ z : ℂ, ENNReal.ofReal (‖z‖ ^ (2 * s * (M + s - 3))) * g z
def MeanBound : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) (g : Λ → ℂ) (B : ℝ),
    IsMean LIM → (∀ x, ‖g x‖ ≤ B) → ‖LIM g‖ ≤ B
def MeanExists : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La],
    ∃ LIM : (La.toAddSubgroup → ℂ) → ℂ, IsMeanInf La.toAddSubgroup LIM
def MeanSplit : Prop :=
  ∀ (f : ℕ) (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a r : V f → H) (Nh : V f → ℂ) (B : ℝ),
    IsMeanInf Λ LIM → (∀ x, ‖a x‖ ≤ B ∧ ‖r x‖ ≤ B) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (a (x + σ))) (atInfAll f) (𝓝 (Nh σ))) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (r (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (r x) (a (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, LIM (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        Nh σ + LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) ∧
    PDOn (Λ : Set (V f)) (fun σ => LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ))))
def LatticeHerglotzBound : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (N : V f → ℝ) (A : V f → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N → PDOn (dualSet La) A →
    Summable (fun σ : dualSet La => ‖fourier N σ + A σ‖) →
    ∀ (z₀ : V f) (S : Finset (V f)), (∀ z ∈ S, z - z₀ ∈ La) →
      ZLattice.covolume La * ∑ z ∈ S, N z ≤ ∑' σ : dualSet La, ‖fourier N σ + A (σ : V f)‖
def chainMat {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) : ℕ → W → W → ℝ
  | 0 => fun w w' => if w = w' then 1 else 0
  | 1 => c 1
  | (n + 2) => fun w w'' => ∑ w' ∈ Wd, c (n + 2) w w' * chainMat Wd c (n + 1) w' w''
def coMat {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (caa : W → W → ℝ) (s : ℕ) (w w'' : W) : ℝ :=
  ∑ w' ∈ Wd, caa w w' * chainMat Wd c (s - 1) w' w''
def ChainSum : Prop :=
  ∀ (W X : Type) (Wd : Finset W) (s : ℕ) (c : ℕ → W → W → ℝ) (caa : W → W → ℝ)
    (Nd : ℕ → W → X → ℝ) (N0 : W → ℝ) (T : W → ℝ), 2 ≤ s →
    (∀ w ∈ Wd, ∀ t, Nd 1 w t ≤ ∑ w' ∈ Wd, c 1 w w' * N0 w') →
    (∀ n, 2 ≤ n → n ≤ s - 1 → ∀ B : W → ℝ, (∀ w' ∈ Wd, ∀ t, Nd (n - 1) w' t ≤ B w') →
        ∀ w ∈ Wd, ∀ t, Nd n w t ≤ ∑ w' ∈ Wd, c n w w' * B w') →
    (∀ B : W → ℝ, (∀ w' ∈ Wd, ∀ t, Nd (s - 1) w' t ≤ B w') →
        ∀ w ∈ Wd, T w ≤ ∑ w' ∈ Wd, caa w w' * B w') →
    ∀ w ∈ Wd, T w ≤ ∑ w'' ∈ Wd, coMat Wd c caa s w w'' * N0 w''
def RowSums : Prop :=
  ∀ (W : Type) (Wd : Finset W) (s : ℕ) (c : ℕ → W → W → ℝ) (caa : W → W → ℝ) (M : ℕ → ℝ) (Maa : ℝ),
    2 ≤ s → (∀ n w w', 0 ≤ c n w w') → (∀ w w', 0 ≤ caa w w') →
    (∀ n, 1 ≤ n → n < s → ∀ w ∈ Wd, ∑ w' ∈ Wd, c n w w' = M n) →
    (∀ w ∈ Wd, ∑ w' ∈ Wd, caa w w' = Maa) →
    ∀ w ∈ Wd, ∑ w'' ∈ Wd, coMat Wd c caa s w w'' = Maa * ∏ n ∈ Ico 1 s, M n ∧
      (0 < Maa * ∏ n ∈ Ico 1 s, M n →
        TB.IsProb Wd (fun w'' => if w'' ∈ Wd then coMat Wd c caa s w w'' / (Maa * ∏ n ∈ Ico 1 s, M n)
          else 0))
def BaseGramMonotone : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W), D.GramPSD → D.WordsPos →
    ∀ ε, 0 < ε → ∀ (k : ℕ) (w : W) (Y : Finset (TB.Pt E)) (κ κ' : TB.Pt E → TB.Pt E → ℂ),
      TB.PSDOn Y κ → TB.PSDOn Y (fun h h' => κ' h h' - κ h h') →
      0 ≤ D.N0 ε k w Y κ ∧ D.N0 ε k w Y κ ≤ D.N0 ε k w Y κ'
def CorT : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W), D.GramPSD → D.WordsPos →
    ∀ ε, 0 < ε → ∀ (k : ℕ) (Y : Finset (TB.Pt E)) (T0 : Finset E)
      (Th : E → TB.Pt E → TB.Pt E → ℂ) (KK : TB.Pt E → TB.Pt E → ℂ) (e : ℝ) (Ws : Finset W)
      (θ : W → ℝ) (Mv Bmax : ℝ) (Lhs : E → ℝ),
      0 ≤ e → 0 ≤ Mv → TB.IsProb Ws θ →
      (∀ t₀ ∈ T0, TB.PSDOn Y (Th t₀)) →
      TB.PSDOn Y (fun h h' => (1 + (e : ℂ)) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') →
      (∀ t₀ ∈ T0, Lhs t₀ ≤ Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y (Th t₀)) →
      (∀ w' ∈ Ws, D.N0 ε k w' Y KK ≤ Bmax) →
      ∑ t₀ ∈ T0, Lhs t₀ ≤ (1 + e) * Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK ∧
        (1 + e) * Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK ≤ (1 + e) * Mv * Bmax
def SumForm {E W : Type} [Field E] (D : TB.Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Mv : ℝ) : Prop :=
  ∃ θ : W → ℝ, TB.IsProb (D.Wb (D.cnt w + s * D.K)) θ ∧
    ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
      ∀ (t₀ : E) (S : Finset E), (∀ t ∈ S, t ≠ 0 ∧ t - t₀ ∈ D.La (i - s + 1) s) →
        ∑ t ∈ S, (D.Nst ε i s w Y κ t t).re ≤
          Mv * ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ
def SizesProduct : Prop :=
  ∀ (f s : ℕ) (Maa C₄ A B : ℝ) (M vol : ℕ → ℝ), 2 ≤ s → 1 ≤ C₄ → 0 ≤ A → A ≤ C₄ → 0 ≤ B → B ≤ C₄ →
    (∀ n, 0 ≤ vol n) → 0 ≤ Maa → Maa ≤ A ^ f →
    (∀ n ∈ Ico 1 s, 0 ≤ M n ∧ M n ≤ B ^ f * vol n) →
    Maa * ∏ n ∈ Ico 1 s, M n ≤ C₄ ^ (f * s) * ∏ n ∈ Ico 1 s, vol n
def EstBlockOfSumForm : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (C₄ : ℝ), D.GramPSD → D.WordsPos →
    (∀ ε, 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ w ∈ D.Wall,
      D.cnt w + (s + 1) * D.K ≤ D.Ntop → D.vol (i - s + 1) s ≤ 1 →
      ∃ Mv, Mv ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ∧ SumForm D ε i s w Mv) →
    D.EstBlock C₄
end
end Formalism.FourierDecayAlt.crystallineComparison


