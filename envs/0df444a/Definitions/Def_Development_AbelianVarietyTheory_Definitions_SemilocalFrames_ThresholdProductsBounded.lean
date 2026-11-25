-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ThresholdProductsBounded
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ThresholdProductsBounded
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:20.094226+00:00
-- url     : https://prove2.me/theorems/7ae728b9-6918-5794-81bb-d7d9882cdefd
-- title:
--   Threshold Products Bounded
-- statement:
--   Definitions and structural lemmas for Threshold Products Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ThresholdProductsBounded.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HerGenC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ThA
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB Finset NumberField MeasureTheory Formalism.QuantumDeterminants
noncomputable section
open Classical
def ThresholdProductsBounded {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (Θ : ℝ) : Prop :=
  (∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i : ℕ, 2 ≤ i → i ≤ G.r + 1 →
    ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i s : ℕ, 1 ≤ i → 2 ≤ s → s + i ≤ G.r + 2 →
    ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ G.r →
    ∏ w, Sz.lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') ≤ (Θ ^ G.f)⁻¹)
def arData (E : Type) [Field E] [NumberField E] [IsCMField E] (g r : ℕ) (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ)
    (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) : TB.Data E Unit where
  r := r
  f := 0
  K := 5
  av := fun _ _ => 0
  wt := fun _ => 1
  cnt := fun _ => 0
  Wall := {()}
  emp := ()
  emp_mem := by simp
  cnt_emp := rfl
  wt_emp := rfl
  gram := fun _ _ _ _ _ => 0
  Kr := Kr
  K0 := hK0
  Th := fun _ _ _ _ _ => 0
  e := e
  La := fun b s => J.LaB E g r b s
  Lap := fun b s => J.LapB E g r b s
  Lad := fun b => J.LadB E g r b
  Nhat := fun _ _ _ _ _ _ => 0
  szD := fun _ _ => 0
  szL := fun _ _ _ => 0
  vol := fun _ _ => 0
def ArAx (E : Type) [Field E] [NumberField E] [IsCMField E] (g r : ℕ) (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ)
    (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) : Prop :=
  TC.KrPSD (arData E g r Kr hK0 e) ∧ (arData E g r Kr hK0 e).KernelSupport ∧ TC.EBounds (arData E g r Kr hK0 e) ∧
    TC.DomAfter (arData E g r Kr hK0 e)
def frS (rd : ℝ) (r b s : ℕ) : ℝ := rd ^ (-(S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ))
abbrev parG {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (x : ι) : M.Par :=
  ⟨G.k, G.r, T, T', (G.place x).u de, (G.place x).u de'⟩
section place
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def vStd {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g rd : ℝ) (p : C.LPt) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  ((√(C.nLoc k r (frS rd r) (D.ptGG (Tz k r Bs.z * Tz k r Bs.z')) p) * (D.bSt (D.kapG g rd) p)⁻¹ : ℝ) : ℂ) •
    B.hsVec (D.vecV Bs ν' m₀ F (D.toStd r g 1 p))
structure PlaceOK {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (x : ι)
    (Bs : B.RealPlaceData G.k G.r Wp Wq) (ν' : Fin (2 * G.r + G.k + 1) → ℂ) (m₀ : B.Mat G.k G.r)
    (F : B.Mat G.k G.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) : Prop where
  hW : Bs.μW Set.univ = 1
  hW' : Bs.μW' Set.univ = 1
  hN : Bs.μN = D.muN G.k G.r
  frame : D.IsBaseFrame Bs ν' m₀
  place : Q.IsPlace (parG G de de' T T' x) Bs.z Bs.z' Bs.π Bs.π'
  smooth : B.CkOn ⊤ (B.GV G.k G.r) F
  decay : ∀ m : ℕ, B.InCC A₀ m F
  eigen : ∀ Y : ℝ, ∀ g ∈ B.GV G.k G.r, Q.CV G.k G.r (Y : ℂ) F g = (((G.place x).P Y : ℝ) : ℂ) • F g
end place
def ChaptersBuilt : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsLeadingFormPlace Cb Cc S p f c.χ A₀ → JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    (∀ v, B.normSq (plT S p v).base (f v) ≠ ⊤) ∧
    ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄
      (∏ v, (B.normSq (plT S p v).base (f v)).toReal /
        D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0) Vt
def SizesLe : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ) (Θ : ℝ),
    S6.Unram E → 0 < S.G.g1 → 0 < S.G.g2 → 0 ≤ S.CA → 0 < S.G.lenI → 4 < Θ →
    ThresholdProductsBounded S.G S.CA S.de S.de' S.T S.T' S.l Θ →
    (S.mkData Kr hK0 Th e).SizesBelow Θ ∧
      (S.mkData Kr hK0 Th e).LatticeSums ((C₁ * Θ ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f)
def MainBuilt : Prop :=
  ∀ Cb : ℝ, ∃ Cc Cst Cst' : ℝ, 0 ≤ Cc ∧ 0 ≤ Cst ∧ 4 < Cst' ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) (Θ : ℝ) (cr : ℕ → TB.Pt E → ℂ),
    IsLeadingFormPlace Cb Cc S p f c.χ A₀ → JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    Cst' ≤ Θ → ((S.G.r : ℝ) + 1) * (Cst / Θ) ^ S.f ≤ 1 → ThresholdProductsBounded S.G S.CA S.de S.de' S.T S.T' S.l Θ →
    ArAx E S.g S.G.r Kr hK0 e → (arData E S.g S.G.r Kr hK0 e).LeadingDomination Vt cr →
    (∀ v, B.normSq (plT S p v).base (f v) ≠ ⊤) ∧
    ∀ Rs : Finset ℕ, ∑ ρ ∈ Rs, ‖∑' q, cr ρ q • Vt q‖ ^ 2 ≤
      (1 + Cst * ((S.G.r : ℝ) + 1) * (Cst / Θ) ^ S.f) * (∏ i ∈ Icc 1 (S.G.r + 1), (1 + e i)) *
        ∏ v, (B.normSq (plT S p v).base (f v)).toReal /
          D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0
def GridsExist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    (∀ v, (S.G.place (S.pl v)).Ok) → 1 ≤ S.l → S.l + 2 ≤ S.G.k → 42 * (S.Ntop : ℝ) ^ 3 ≤ S.G.lenI →
    ∃ (gr : Fin S.f → ℕ → Finset ℝ) (gr1 : Fin S.f → Finset ℝ),
      C.GridsOK { S with grid := gr, grid1 := gr1 } ∧ GridsRich { S with grid := gr, grid1 := gr1 }
def PlExists : Prop :=
  ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (l0 : ℕ),
    1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.μW Set.univ = 1 → Bs.μW' Set.univ = 1 → Bs.μN = D.muN P.k P.r →
    D.IsBaseFrame Bs ν' m₀ → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∃ p : Pl P Wp Wq, p.l0 = l0 ∧ p.T.base = Bs ∧ p.ν' = ν' ∧ p.m₀ = m₀ ∧ InDDplus2 P l0 p.T.base Cb p.Θ
def MainFreeAt (C C' : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (G : Sz.Glob (InfinitePlace E)) (emb : InfinitePlace E → (E →+* ℂ)) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
    (Bs : ∀ x, B.RealPlaceData G.k G.r (Wp x) (Wq x)) (ν' : InfinitePlace E → Fin (2 * G.r + G.k + 1) → ℂ)
    (m₀ : InfinitePlace E → B.Mat G.k G.r) (F : ∀ x, B.Mat G.k G.r → (Wq x →L[ℂ] Wp x)) (A₀ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) (Θ : ℝ) (cr : ℕ → TB.Pt E → ℂ),
    (∀ x, InfinitePlace.mk (emb x) = x) → S6.Unram E → G.v = S6.rd E / 2 → 0 < G.g1 → 0 < G.g2 →
    (∀ x, (G.place x).Ok) → Sz.IsWord G.k de → Sz.IsWord G.k de' → 1 ≤ l → l + 2 ≤ G.k → de l ≠ de' l →
    C * ((G.k : ℝ) * G.N * ((G.r : ℝ) + 1) ^ 2 + G.N ^ 2 * ((G.r : ℝ) + 1) ^ 2 + G.N ^ 3) ≤ G.lenI →
    C * ((G.r : ℝ) + 1) ^ 4 * (G.N * (2 * (G.r : ℝ) + G.k + 1) ^ 2 + (2 * (G.r : ℝ) + G.k + 1) ^ 3) ≤ A₀ →
    (∀ x, PlaceOK G de de' T T' x (Bs x) (ν' x) (m₀ x) (F x) A₀) →
    (∀ p q : TB.Pt E, TB.IsPt p (G.r + 1) → TB.IsPt q (G.r + 1) → inner ℂ (Vt q) (Vt p) =
      ∏ x, inner ℂ (vStd (Bs x) (ν' x) (m₀ x) (F x) G.g (S6.rd E) (Formalism.FourierDecayAlt.C.loc (emb x) q))
        (vStd (Bs x) (ν' x) (m₀ x) (F x) G.g (S6.rd E) (Formalism.FourierDecayAlt.C.loc (emb x) p))) →
    C' ≤ Θ → ((G.r : ℝ) + 1) * (C / Θ) ^ G.f ≤ 1 → ThresholdProductsBounded G C de de' T T' l Θ →
    ArAx E (G.g1 * G.g2) G.r Kr hK0 e → (arData E (G.g1 * G.g2) G.r Kr hK0 e).LeadingDomination Vt cr →
    (∀ x, B.normSq (Bs x) (F x) ≠ ⊤) ∧
    ∀ Rs : Finset ℕ, ∑ ρ ∈ Rs, ‖∑' q, cr ρ q • Vt q‖ ^ 2 ≤
      (1 + C * ((G.r : ℝ) + 1) * (C / Θ) ^ G.f) * (∏ i ∈ Icc 1 (G.r + 1), (1 + e i)) *
        ∏ x, (B.normSq (Bs x) (F x)).toReal / D.GamLev G.k G.r (D.kapG G.g (S6.rd E)) (D.deG G.g (S6.rd E)) 0
def MainFree : Prop := ∃ C₀ C' : ℝ, 1 ≤ C₀ ∧ 4 < C' ∧ ∀ C : ℝ, C₀ ≤ C → MainFreeAt C C'
end
end GlobalTheory.ThA


