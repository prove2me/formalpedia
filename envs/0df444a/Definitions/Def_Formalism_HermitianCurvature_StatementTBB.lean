-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementTBB
-- name    : Formalism_HermitianCurvature_StatementTBB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:13:56.949797+00:00
-- url     : https://prove2.me/theorems/0697cd41-5f07-46ea-b905-75d8f2dfeac1
-- title:
--   Statement TBB
-- statement:
--   Definitions and structural lemmas for Statement TBB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementTBB.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.TBB
open Finset Filter Topology MeasureTheory Formalism.QuantumDeterminants
open scoped ComplexConjugate ENNReal
noncomputable section
open Classical
def nPt (k r : ℕ) (TT : ℝ) (h : C.LPt) : ℝ := C.nAux k r (D.ptGG TT h) (fun _ _ => 1) 1 h
def normC (nn : ℝ → ℝ) (w : List C.Letter) : ℝ := (w.map fun l => nn l.2).prod
def mn (Λ : ℝ) (K : ℕ) (x : ℝ) : ℝ := if x = 0 then 1 else min 1 ((Λ / x) ^ K)
def AdmW (P : M.Par) (l0 : ℕ) (Y : Finset ℝ) (w : List C.Letter) : Prop :=
  KB.CutWord P l0 w ∧ ∀ l ∈ w, ∃ y ∈ Y, l = (true, y) ∨ l = (false, y + 1)
def IsExt (P : M.Par) (l0 : ℕ) (Y : Finset ℝ) (N m : ℕ) (w w' : List C.Letter) : Prop :=
  KB.CutWord P l0 w' ∧ w'.length ≤ N ∧ ∃ L : List C.Letter, w' = L ++ w ∧ L.length ≤ m ∧
    ∀ l ∈ L, ∃ y ∈ Y, l = (true, y) ∨ l = (false, y + 1)
def bigPt (r : ℕ) (c : Fin (r + 1) → ℂ) : C.LPt := List.ofFn fun l => (1, c l)
section one
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
def TTp (p : KB.Pl P Wp Wq) : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
def Tq (p : KB.Pl P Wp Wq) : ℝ := Tz P.k P.r p.T.base.z'
def Gp (p : KB.Pl P Wp Wq) (γ : C.LPt) : ℝ := D.ptG (TTp p) P.r γ
def NP (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (a b : C.LPt) : ℂ :=
  ((Real.sqrt (nPt P.k P.r (TTp p) a) * Real.sqrt (nPt P.k P.r (TTp p) b) / normC nn w : ℝ) : ℂ) * p.RR F i w a b
def Ew (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (h : C.LPt) : ℝ :=
  (NP p nn F i w h h).re
def jN2 (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : ℝ≥0∞ :=
  ∫⁻ c : Fin (P.r + 1) → ℂ, ENNReal.ofReal (Ew p (fun _ => 1) F (P.r + 1) [] (bigPt P.r c))
def bigCellDetWeightedEnergyIntegral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a : ℕ) : ℝ≥0∞ :=
  ∫⁻ c : Fin (P.r + 1) → ℂ, ENNReal.ofReal (‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * a) *
    Ew p (fun _ => 1) F (P.r + 1) [] (bigPt P.r c))
def HeadContinuityAtZero (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ j, j ≤ P.r → ∀ h : C.LPt, D.IsLocPt h j → ∀ w, AdmW P p.l0 Y w → w.length ≤ N →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      ∀ c : ℂ, c ≠ 0 → φ c = NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])
def KernelFourierIntegralBound (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) :
    Prop :=
  ∀ j, j ≤ P.r → ∀ h : C.LPt, D.IsLocPt h j → ∀ w, AdmW P p.l0 Y w → w.length + K ≤ N → ∀ s : ℂ,
    ∃ w', IsExt P p.l0 Y N K w w' ∧
      ‖∫ c : ℂ, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤ mn Λ K ‖s‖ * Ew p nn F j w' h
def KernelArgumentHypothesisScalar (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) :
    Prop :=
  ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → b + s - 1 ≤ P.r → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, AdmW P p.l0 Y w →
    w.length + K ≤ N → ∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
      ∃ w₁ w₂, IsExt P p.l0 Y N K w w₁ ∧ IsExt P p.l0 Y N K w w₂ ∧
        ‖NP p nn F (b + s - 1) w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
          mn Λ K ‖t⁻¹ - t'⁻¹‖ *
            ((Ew p nn F (b + s - 1) w₁ (h ++ [(s, t)]) + Ew p nn F (b + s - 1) w₂ (h ++ [(s, t')])) / 2)
def InDual (ω₁ ω₂ σ : ℂ) : Prop := ∀ a b : ℤ, P5.fsv σ ((a : ℂ) * ω₁ + (b : ℂ) * ω₂) = 1
def BlockGrowthBound (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, AdmW P p.l0 Y w →
    w.length + K ≤ N →
    (∀ w', IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))) →
    ∀ ω₁ ω₂ z₀ : ℂ, (conj ω₁ * ω₂).im ≠ 0 →
      ∃ k : ℂ → ℂ,
        ENNReal.ofReal (|(conj ω₁ * ω₂).im| / Real.pi) *
            ∑' ab : ℤ × ℤ, ENNReal.ofReal
              (Ew p nn F (b + s - 1) w (h ++ [(s, z₀ + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)])) ≤
          ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, (‖k σ.1‖₊ : ℝ≥0∞) ∧
        ∀ σ : ℂ, InDual ω₁ ω₂ σ →
          (‖k σ‖₊ : ℝ≥0∞) ≤ limsup (fun t : ℂ =>
            (‖NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, (t⁻¹ + σ)⁻¹)])‖₊ : ℝ≥0∞)) (𝓝[≠] 0)
def PosAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ i w (h : C.LPt), AdmW P p.l0 Y w → w.length ≤ N → 0 ≤ Ew p nn F i w h
def LemmaS (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ)
    (K N : ℕ) (C₂ : ℝ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, AdmW P p.l0 Y w →
    w.length + s * K ≤ N → ∀ t : ℂ, t ≠ 0 →
      ∃ w', IsExt P p.l0 Y N (s * K) w w' ∧
        Ew p nn F (b + s - 1) w (h ++ [(s, t)]) ≤ (C₂ * Λ ^ 2) ^ s * Ew p nn F (b - 1) w' h
def CorS (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (C₂ : ℝ) : Prop :=
  ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → ∃ w', IsExt P p.l0 Y N ((P.r + 1) * K) [] w' ∧
    Ew p nn F (P.r + 1) [] γ ≤ (C₂ * Λ ^ 2) ^ (P.r + 1) * Ew p nn F 0 w' []
def PtBound (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ) : Prop :=
  ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
    ENNReal.ofReal (Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤ ENNReal.ofReal c * jN2 p F
def VecCutAt (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → ε ≤ Gp p γ → p.V (D.cutF p.T.base χ F ε) γ = p.V F γ
def LimZeroAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) (κ₀ : ℝ) : Prop :=
  ∀ w, AdmW P p.l0 Y w → w.length ≤ N →
    limsup (fun ε : ℝ => ENNReal.ofReal (Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0) ≤
      ENNReal.ofReal κ₀ * jN2 p F
def NormAt (p : KB.Pl P Wp Wq) (f Fp Fm : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ p₀ : ℕ) : Prop :=
  (∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
    Ew p (fun _ => 1) f (P.r + 1) [] γ ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
      (Ew p (fun _ => 1) Fp (P.r + 1) [] γ + Ew p (fun _ => 1) Fm (P.r + 1) [] γ)) ∧
  ∀ c : Fin (P.r + 1) → ℂ, ∀ F ∈ ({Fp, Fm} : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp))),
    Ew p (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)
def RegularityBoundBigCell (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∀ a, a ≤ a₁ → bigCellDetWeightedEnergyIntegral p f a ≤ ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ))) * jN2 p f
def ThmBpAt (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₄ : ℝ) (n₀ p₀ : ℕ) : Prop :=
  ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
    ENNReal.ofReal (Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
      ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f
end one
def StepOne : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
    3 ≤ K → 0 ≤ Λ → HeadContinuityAtZero p nn F Y N → KernelFourierIntegralBound p nn F Y Λ K N →
    ∀ j, j ≤ P.r → ∀ h : C.LPt, D.IsLocPt h j → ∀ w, AdmW P p.l0 Y w → w.length + K ≤ N → ∀ c : ℂ, c ≠ 0 →
      ∃ w', IsExt P p.l0 Y N K w w' ∧ Ew p nn F (j + 1) w (h ++ [(1, c)]) ≤ 3 / Real.pi * Λ ^ 2 * Ew p nn F j w' h
def StepUp : Prop :=
  ∃ Cu : ℝ, 0 < Cu ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
    3 ≤ K → 1 ≤ Λ → PosAt p nn F Y N → KernelArgumentHypothesisScalar p nn F Y Λ K N → BlockGrowthBound p nn F Y K N →
    ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, AdmW P p.l0 Y w →
      w.length + K ≤ N → ∀ Mb : ℝ,
      (∀ w', IsExt P p.l0 Y N K w w' → ∀ t : ℂ, t ≠ 0 → Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t)]) ≤ Mb) →
      ∀ z : ℂ, z ≠ 0 → Ew p nn F (b + s - 1) w (h ++ [(s, z)]) ≤ Cu * Λ ^ 2 * Mb
def LemmaSOfSteps : Prop :=
  StepOne → StepUp → ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ)
    (K N : ℕ), 3 ≤ K → 1 ≤ Λ → PosAt p nn F Y N → HeadContinuityAtZero p nn F Y N → KernelFourierIntegralBound p nn F Y Λ K N →
    KernelArgumentHypothesisScalar p nn F Y Λ K N → BlockGrowthBound p nn F Y K N → LemmaS p nn F Y Λ K N C₂
def CorSOfLemmaS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (C₂ : ℝ),
    (P.r + 1) * K ≤ N → 0 ≤ C₂ → PosAt p nn F Y N → LemmaS p nn F Y Λ K N C₂ → CorS p nn F Y Λ K N C₂
def PtBoundOfCorS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (C₂ κ₀ : ℝ),
    0 ≤ C₂ → 0 < κ₀ → (∀ y, 0 < nn y) → (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      CorS p nn (D.cutF p.T.base χ F ε) Y Λ K N C₂) →
    VecCutAt p χ F → LimZeroAt p nn χ F Y N κ₀ → PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1))
def VecCutAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → VecCutAt p χ F
def ThmBpOfParts : Prop :=
  ∀ C₃ CΛ C₀ C₂ Cκ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 1 / 2 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (Wp Wq : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f Fp Fm : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ),
    3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
    κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ Tq p →
    n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
    NormAt p f Fp Fm b n₀ p₀ → PtBound p Fp (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) →
    PtBound p Fm (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) → RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → ThmBpAt p f b C₄ n₀ p₀
def TriAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a : Fin n → ℂ)
    (b C₁ C₄ : ℝ) (n₀ p₀ : ℕ) (γ : C.LPt) (Qγ : ℝ),
    1 ≤ b → ∑ i, ‖a i‖ ≤ b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) → (∀ i, jN2 p (fi i) ≤ jN2 p f) →
    (∀ i, ThmBpAt p (fi i) b C₄ n₀ p₀) → D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
    (Qγ : ℂ) • p.V f γ = ∑ i, a i • p.V (fi i) γ →
    ENNReal.ofReal (Qγ ^ 2 * Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
      ENNReal.ofReal (b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f
end
end Formalism.FourierDecayAlt.TBB


