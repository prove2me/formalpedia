-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:39.918776+00:00
-- url     : https://prove2.me/theorems/99f20268-1471-4202-a67c-7d0f4537ffad
-- title:
--   Is Period On
-- statement:
--   Definitions and structural lemmas for Is Period On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/IsPeriodOn.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Inputs_pullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial Matrix GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}
def IsPeriodOn {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X) (j : ℕ) (V : Set X)
    (Pi G : Ψ → X → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsOpen V ∧ (∀ τ a b, A.HoloOn V fun x => Pi τ x a b) ∧ ∀ τ, ∀ x ∈ V, IsPeriodGram j (Pi τ x) (G τ x)
structure BaseMetric (M : FlagModel y Ψ N j) (n : ℕ) where

  Rb : AnLogRes (mCoordIdeal M.x) ⊤ n

  L : LocPot Rb.X

  s : Rb.X → Rb.X → ℂ

  nb : ℕ

  m : Fin nb → ℕ

  W : Fin nb → Set Rb.X
  potL : IsPotential Rb.A L
  sec : IsSection Rb.A L s
  snc : IsSNC Rb.A L s m W
  norm_le : ∀ x, logNormSec L s x ≤ 0

  Bat : FinHolAtlas n Rb.X
  adapted : IsAdaptedAtlas Rb.A Bat L s

  q : ℕ

  O : Fin q → Set Rb.X
  O_open : ∀ l, IsOpen (O l)
  O_cover : ∀ x, ∃ l, x ∈ O l

  F : Fin q → FrameData ι Ψ N M.Ω M.blk
  isFrame : ∀ l, M.IsFrame (F l)
  good : ∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))

  G : Fin q → Ψ → Rb.X → Matrix (Fin N) (Fin N) ℂ
  G_pos : ∀ l τ, ∀ x ∈ O l \ bdry s, IsBlockDiag j (G l τ x) ∧ (G l τ x).PosDef
  G_smooth : ∀ l τ a b, Rb.A.SmoothOn (O l \ bdry s) (fun x => (G l τ x a b).re) ∧
    Rb.A.SmoothOn (O l \ bdry s) fun x => (G l τ x a b).im

  Cst : ℝ
  size : ∀ l τ, ∀ x ∈ O l \ bdry s,
    (((rW L s x ^ Cst : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G l τ x).PosSemidef ∧
      (((rW L s x ^ Cst : ℝ) : ℂ) • G l τ x - 1).PosSemidef
  grad : ∀ l τ a b k, ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (Bat.chart k).symm w ∈ O l \ bdry s →
    ‖fderiv ℝ (fun w' => G l τ ((Bat.chart k).symm w') a b) w‖ ≤
      Cst * rW L s ((Bat.chart k).symm w) ^ Cst * Real.exp (rW L s ((Bat.chart k).symm w) / 2)
  period : ∀ l, ∀ x ∈ O l \ bdry s, ∃ V Pi, x ∈ V ∧ IsPeriodOn Rb.A j V Pi (G l)
  immersion : ∃ l, ∃ x ∈ O l \ bdry s, ∃ V Pi, x ∈ V ∧ IsPeriodOn Rb.A j V Pi (G l) ∧
    ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin n → ℂ,
      (∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ x)⁻¹ * Matrix.of fun a b =>
        fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0

  hom : Ψ × Fin N → HermLine ι
  hom_deg : ∀ p, (hom p).a = M.dy p
  induced : ∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (G l p.1 x) (hom p)
structure FlagAn {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (d : ℕ) where

  S : AnSys (d + 1) (Option (Ψ × Fin N))

  Re : Realis S (mCoordIdeal y)
  J_top : Re.J = ⊤
  deg_one : Re.deg = 1
  br_empty : Re.br = ∅
  ref_some : ∀ p, Re.ref (some p) = fsHerm ι (M.dy p)
  ref_none : Re.ref none = fsHerm ι fun _ => 1
  line_none : ∀ t, Re.line none t = fsHerm ι fun _ => 1
  ph_none : S.ph none = 0 ∧ ∀ t, S.phT none t = 0
  pos_none : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t, IsPsh S.A (S.potT none t + S.Θ.rsmul (-c₀))

  pr : S.X → BM.Rb.X
  pr_holo : HoloMap S.A BM.Rb.A pr
  pr_eq : ∀ x, SameOrbit (basePart M.blk (Re.R.lift x x)) (BM.Rb.lift (pr (Re.π x)) (pr (Re.π x)))
  L_eq : S.L = BM.L.pullback pr pr_holo.1
  s_eq : S.s = fun x x' => BM.s (pr x) (pr x')
  hom_eq : ∀ p x, Re.π x ∈ S.open' → Real.log ((BM.hom p).h (Re.R.lift x x)) =
    Real.log ((Re.ref (some p)).h (Re.R.lift x x)) + S.ph (some p) (Re.π x)
  step : ∀ p t, M.OnStep p (Re.line (some p) t)
  step_ph : ∀ p x x', pr (Re.π x) = pr (Re.π x') →
    (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, Re.R.lift x x ⟨k, m⟩ = a * Re.R.lift x' x' ⟨k, m⟩) →
      S.ph (some p) (Re.π x) = S.ph (some p) (Re.π x') ∧ ∀ t, S.phT (some p) t (Re.π x) = S.phT (some p) t (Re.π x')
  flat : ∀ p : Ψ × Fin N, (p.2 : ℕ) + 1 = N → ∀ t, IsPsh S.A ((S.potT (some p) t).rsmul (-1)) ∧
    IsPsh S.A (S.potT (some p) t) ∧ S.phT (some p) t = S.ph (some p)
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}
structure FlagCover (M' : FlagModel y' Ψ N j) (M : FlagModel y Ψ N j) where

  κ : NonPluckerBlocks M.blk → NonPluckerBlocks M'.blk

  v : (Σ k, baseIdx ι M.blk k) → (Σ k, baseIdx ι' M'.blk k)
  block : IsBlockMap κ v

  φ : M.Ω →+* M'.Ω
  x_eq : ∀ q, M'.x (v q) = φ (M.x q)
  deg_pos : 0 < IntermediateField.relfinrank (blockFnField (M'.x ∘ v)) (blockFnField M'.x)
  agree : ∀ z ∈ mcPts (mCoordIdeal M'.x), ∀ F' F, M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal z) →
    M.GoodAt F (mCoordIdeal (z ∘ v)) → ∀ τ a b,
      RegAt M'.x (mCoordIdeal z) ((((F.T τ).map φ)⁻¹ * F'.T τ) a b) ∧
        RegAt M'.x (mCoordIdeal z) (((F'.T τ)⁻¹ * (F.T τ).map φ) a b)
def FlagCover.deg {M' : FlagModel y' Ψ N j} {M : FlagModel y Ψ N j} (Cv : FlagCover M' M) : ℕ :=
  IntermediateField.relfinrank (blockFnField (M'.x ∘ Cv.v)) (blockFnField M'.x)
def FlagCover.trans {M' : FlagModel y' Ψ N j} {M : FlagModel y Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ)
    (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => valAt M'.x ((((F.T τ).map Cv.φ)⁻¹ * F'.T τ) a b) zb
def FlagModel.ExactAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (z : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) ∧ ∀ k, M.blk p = some k → ∀ m : ι k,
    z ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2)
def FlagModel.upsLog (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (z : (Σ k, ι k) → ℂ) : ℝ :=
  (M.blk p).elim (Real.log ‖valAt M.x (F.υ p) (basePart M.blk z)‖) fun _ => 0
structure CovReal {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d)
    {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) where

  Re : Realis (FA.S.comap some) (mCoordIdeal y')
  deg_eq : Re.deg = Cv.deg
  ref_deg : ∀ p, (Re.ref p).a = M'.dy p
  step : ∀ p t, M'.OnStep p (Re.line p t)

  ϖ : ((Σ k, ι' k) → ℂ) → FA.S.X
  ϖ_torus : ∀ z z', z ∈ mcPts (mCoordIdeal y') → SameOrbit z' z → ϖ z' = ϖ z
  π_eq : ∀ x, Re.π x = ϖ (Re.R.lift x x)
  line_pt : ∀ p t, 0 < t → t ≤ FA.S.t₀ → ∀ z ∈ mcPts (mCoordIdeal y'),
    Real.log ((Re.line p t).h z) = Real.log ((Re.ref p).h z) + FA.S.phT (some p) t (ϖ z)
  flags : ∀ z ∈ mcPts (mCoordIdeal y'), ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) →
    ∀ h, M'.IsFlagOf F' z h → ∀ x₀, FA.Re.π x₀ = ϖ z → ∃ z₀, SameOrbit z₀ (FA.Re.R.lift x₀ x₀) ∧
      SameOrbit (basePart M.blk z₀) (basePart M'.blk z ∘ Cv.v) ∧
        M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ
  metric : ∀ z ∈ mcPts (mCoordIdeal y'), ∀ z₀ ∈ mcPts (mCoordIdeal y), ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) →
    SameOrbit (basePart M.blk z₀) (basePart M'.blk z ∘ Cv.v) → ∀ p h, IsBlockDiag j h → h.det ≠ 0 →
    M'.ExactAt F' p z h → M.ExactAt F p z₀ (Cv.trans F' F (basePart M'.blk z) p.1 * h) →
      Real.log ((Re.ref p).h z) + M'.upsLog F' p z =
        Real.log ((fsHerm ι (M.dy p)).h z₀) + M.upsLog F p z₀ +
          Real.log ‖detFac j p.2 (Cv.trans F' F (basePart M'.blk z) p.1)‖
end GlobalTheory.CompanionTheory.Ar.PB


