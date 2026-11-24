-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementKB
-- name    : Formalism_HermitianCurvature_StatementKB
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:33:09.909975+00:00
-- url     : https://prove2.me/theorems/1160d8d3-7f15-43bb-85ea-38163c53e5f0
-- title:
--   Statement KB
-- statement:
--   Definitions and structural lemmas for Statement KB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementKB.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementTop
import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.KB
open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Classical
def BlockPSD {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) : Prop :=
  TB.PSDOn (Y₁.disjSum Y₂) fun x y => match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q
def BlockOfCS : Prop :=
  ∀ (α β : Type) (Y₁ : Finset α) (Y₂ : Finset β) (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ),
    TB.PSDOn Y₁ a → TB.PSDOn Y₂ b →
    (∀ (c : α → ℂ) (d : β → ℂ), ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, c p * conj (d q) * w p q‖ ^ 2 ≤
      (∑ p ∈ Y₁, ∑ p' ∈ Y₁, c p * conj (c p') * a p p').re * (∑ q ∈ Y₂, ∑ q' ∈ Y₂, d q * conj (d q') * b q q').re) →
    BlockPSD Y₁ Y₂ a w b
def BlockSchur : Prop :=
  ∀ (ι α β : Type) [Fintype ι] (Y₁ : Finset α) (Y₂ : Finset β) (κa : α → α → ℂ) (κw : α → β → ℂ) (κb : β → β → ℂ)
    (a : ι → α → α → ℂ) (w : ι → α → β → ℂ) (b : ι → β → β → ℂ),
    BlockPSD Y₁ Y₂ κa κw κb → (∀ v, BlockPSD Y₁ Y₂ (a v) (w v) (b v)) →
    ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, κw p q * ∏ v, w v p q‖ ≤
      ((∑ p ∈ Y₁, ∑ p' ∈ Y₁, κa p p' * ∏ v, a v p p').re + (∑ q ∈ Y₂, ∑ q' ∈ Y₂, κb q q' * ∏ v, b v q q').re) / 2
section loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
def GridsRich (S : C.HidaSetting E Wp Wq) : Prop :=
  ∀ v, S.Ntop ≤ (S.grid1 v).card ∧ ∀ a, 1 ≤ a → a ≤ S.Ntop → ∀ n, n ≤ 2 * S.G.r →
    ∃ y : Fin (n + 1) → ℝ, Function.Injective y ∧ (∀ j, y j ∈ S.grid v a) ∧
      ∑ j, |F7.lagCo y j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n
def LocProb (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (n : ℕ) (U : Finset (List C.Letter)) (θ : List C.Letter → ℝ) : Prop :=
  TB.IsProb U θ ∧ ∀ a ∈ U, D.AdmAt S v a ∧ a.length ≤ n
def gN (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) (a : List C.Letter) (p q : C.LPt) : ℂ :=
  S.gramLoc v ε i a p q / (S.sizeAt v a : ℂ)
def mix (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) (U : Finset (List C.Letter)) (θ : List C.Letter → ℝ)
    (p q : C.LPt) : ℂ := ∑ a ∈ U, (θ a : ℂ) * gN S v ε i a p q
def psiL (S : C.HidaSetting E Wp Wq) (l c : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((2 * (l * c).re / (S.g : ℝ) : ℝ) : ℂ))
def dlB (S : C.HidaSetting E Wp Wq) (b s : ℕ) : ℝ :=
  S6.rd E ^ (2 * S6.nuBlock S.G.r b s) / D.deG S.g (S6.rd E)
def hatB (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (l : ℂ) (h h' : C.LPt) : ℂ :=
  ((dlB S b s : ℝ) : ℂ)⁻¹ * ∫ c : ℂ, gN S v ε (b + s - 1) a (h ++ [(s, c)]) (h' ++ [(s, c)]) * psiL S l c
def WaveLoc (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (X : ℕ → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → a.length + C.Kst ≤ S.Ntop →
    ∃ Up θp Um θm, LocProb S v (a.length + C.Kst) Up θp ∧ LocProb S v (a.length + C.Kst) Um θm ∧
      ∀ ε, 0 < ε → ∀ (l : ℂ) (Y : Finset C.LPt), (∀ h ∈ Y, D.ptSize h = i - 1) →
        BlockPSD Y Y (gN S v ε (i - 1) a) (hatB S v ε i 1 a l) (gN S v ε (i - 1) a) ∧
        ∃ u : ℂ, ‖u‖ = 1 ∧
          BlockPSD Y Y (fun p q => ((X i ^ C.Kst : ℝ) : ℂ) * mix S v ε (i - 1) Up θp p q)
            (fun p q => u * l ^ C.Kst * hatB S v ε i 1 a l p q)
            (fun p q => ((X i ^ C.Kst : ℝ) : ℂ) * mix S v ε (i - 1) Um θm p q)
def LiftLoc (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Λ : ℕ → ℕ → ℝ) : Prop :=
  ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → a.length + C.Kst ≤ S.Ntop →
    ∃ Up θp Um θm, LocProb S v (a.length + C.Kst) Up θp ∧ LocProb S v (a.length + C.Kst) Um θm ∧
      ∀ ε, 0 < ε → ∀ (t t' : ℂ) (Y : Finset C.LPt), t ≠ 0 → t' ≠ 0 → (∀ h ∈ Y, D.ptSize h = b - 1) →
        ∃ u : ℂ, ‖u‖ = 1 ∧
          BlockPSD Y Y
            (fun p q => ((Λ b s ^ C.Kst : ℝ) : ℂ) * mix S v ε (b + s - 1) Up θp (p ++ [(s, t)]) (q ++ [(s, t)]))
            (fun p q => u * (t⁻¹ - t'⁻¹) ^ C.Kst * gN S v ε (b + s - 1) a (p ++ [(s, t)]) (q ++ [(s, t')]))
            (fun p q => ((Λ b s ^ C.Kst : ℝ) : ℂ) * mix S v ε (b + s - 1) Um θm (p ++ [(s, t')]) (q ++ [(s, t')]))
def TopLoc (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Λ' : ℕ → ℕ → ℝ) : Prop :=
  ∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → a.length + C.Kst ≤ S.Ntop →
    ∃ U θ, LocProb S v (a.length + C.Kst) U θ ∧
      ∀ ε, 0 < ε → ∀ (t : ℂ) (Y : Finset C.LPt), t ≠ 0 → (∀ h ∈ Y, D.ptSize h = S.G.r + 1 - s) →
        TB.PSDOn Y fun p q =>
          (((‖t‖ * Λ' (S.G.r + 2 - s) s) ^ (2 * C.Kst) : ℝ) : ℂ) *
              mix S v ε (S.G.r + 1) U θ (p ++ [(s, t)]) (q ++ [(s, t)]) -
            gN S v ε (S.G.r + 1) a (p ++ [(s, t)]) (q ++ [(s, t)])
def GermLoc (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ Y : Finset C.LPt,
    (∀ h ∈ Y, D.ptSize h = b - 1) →
    (∃ B : ℝ, ∀ h ∈ Y, ∀ t : ℂ, t ≠ 0 → ‖gN S v ε (b + s - 2) a (h ++ [(s - 1, t)]) (h ++ [(s - 1, t)])‖ ≤ B) →
    (∀ h ∈ Y, ∀ h' ∈ Y,
      ContinuousOn (fun z : ℂ => gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)])) {0}ᶜ ∧
      Integrable fun z : ℂ => gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)])) ∧
    ∃ Pua Paa : C.LPt × ℂ → C.LPt × ℂ → ℂ,
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs)
        (fun p q => gN S v ε (b + s - 2) a (p.1 ++ [(s - 1, p.2⁻¹)]) (q.1 ++ [(s - 1, q.2⁻¹)])) Pua Paa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖Paa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
        Tendsto (fun x => Paa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB S v ε b s a σ h h')) ∧
        Tendsto (fun x => Pua (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB S v ε b s a σ h h')) ∧
        Tendsto (fun x => conj (Pua (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hatB S v ε b s a σ h h'))
def IntAll (S : C.HidaSetting E Wp Wq) : Prop := ∀ v, JC.ThmPIntPlace S v fun i => dlB S i 1
def withRR (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ) :
    C.HidaSetting E Wp Wq :=
  { S with pd := fun v => { S.pd v with RR := RR v }, hT := S.hT }
end loc
def WaveOfLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (X : ℕ → Fin S.f → ℝ),
    0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → C.GridsOK S → IntAll S → (∀ i v, 0 ≤ X i v) →
    (∀ v, WaveLoc S v fun i => X i v) → JC.WaveByPlaces S X
def LiftOfLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (Λ : ℕ → ℕ → Fin S.f → ℝ),
    C.ThmPPos S → C.GridsOK S → (∀ b s v, 0 ≤ Λ b s v) → (∀ v, LiftLoc S v fun b s => Λ b s v) → JC.LiftBelowTop S Λ
def TopOfLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (Λ' : ℕ → ℕ → Fin S.f → ℝ),
    C.ThmPPos S → C.GridsOK S → (∀ v, TopLoc S v fun b s => Λ' b s v) → JC.LiftTopDiag S Λ'
def SumFormOfLoc : Prop :=
  ∃ C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (X : ℕ → Fin S.f → ℝ) (Λ : ℕ → ℕ → Fin S.f → ℝ),
    0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → C.ThmPPos S → C.GridsOK S → IntAll S →
    (∀ v, WaveLoc S v fun i => X i v) → JC.HidaCurvatureBarriers S X → (∀ v, LiftLoc S v fun b s => Λ b s v) →
    (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) →
    (∀ b s v, 1 ≤ b → 1 ≤ s → 0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v)) →
    (∀ v, GermLoc S v) → JC.SumFormConcrete S C₄
def LimitClosed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ),
    (∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q, Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q))) →
    (∀ Λ, (∀ n, JC.LiftBelowTop (withRR S (RR n)) Λ) → JC.LiftBelowTop S Λ) ∧
    (∀ Λ', (∀ n, JC.LiftTopDiag (withRR S (RR n)) Λ') → JC.LiftTopDiag S Λ') ∧
    (∀ C₄, (∀ n, C.ThmPPos (withRR S (RR n))) → C.GridsOK S →
      (∀ n, JC.SumFormConcrete (withRR S (RR n)) C₄) → JC.SumFormConcrete S C₄)
def LimitInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ),
    0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E →
    (∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q, Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q))) →
    (∀ n, IntAll (withRR S (RR n))) →
    (∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 → D.ptSize h' = i - 1 →
      ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
          ‖(withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) * psiL S l c‖ ≤
          C * ((1 + ‖l‖) ^ 3)⁻¹) →
    IntAll S ∧ ∀ X, (∀ n, JC.WaveByPlaces (withRR S (RR n)) X) → JC.WaveByPlaces S X
end
end Formalism.FourierDecayAlt.KB


