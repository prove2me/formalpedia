-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- name    : Formalism_HermitianCurvature_StatementTB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:54.467872+00:00
-- url     : https://prove2.me/theorems/31972ada-bb61-4b04-9bce-fd61e41c8ab3
-- title:
--   Statement TB
-- statement:
--   Definitions and structural lemmas for Statement TB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementTB.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.TB
open Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexOrder
noncomputable section
open Classical
abbrev Pt (E : Type) := List (ℕ × E)
variable {E W : Type} [Field E]
def level (p : Pt E) : ℕ := (p.map Prod.fst).sum
def blockStart (p : Pt E) (k : ℕ) : ℕ := ((p.take k).map Prod.fst).sum + 1
def join (h : Pt E) (s : ℕ) (t : E) : Pt E := h ++ [(s, t)]
def IsPt (p : Pt E) (i : ℕ) : Prop :=
  level p = i ∧ ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ≠ 0
def IsTower (Sg : ℕ → ℕ → Finset E) (X : ℕ → Finset (Pt E)) : Prop :=
  ∀ i p, p ∈ X i ↔ level p = i ∧
    ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ Sg (blockStart p k) (p[k]'hk).1
structure Tower (E : Type) [Field E] where

  Sg : ℕ → ℕ → Finset E

  X : ℕ → Finset (Pt E)
  isTower : IsTower Sg X
  zero_not_mem : ∀ b s, (0 : E) ∉ Sg b s
def PSDOn {α : Type} (Y : Finset α) (k : α → α → ℂ) : Prop :=
  Matrix.PosSemidef (Matrix.of fun x y : Y => k x y)
def IsProb {α : Type} (S : Finset α) (θ : α → ℝ) : Prop :=
  (∀ a, 0 ≤ θ a) ∧ (∀ a, a ∉ S → θ a = 0) ∧ ∑ a ∈ S, θ a = 1
structure Data (E W : Type) [Field E] where

  r : ℕ

  f : ℕ

  K : ℕ

  av : Fin f → E → ℝ

  wt : W → ℝ

  cnt : W → ℕ

  Wall : Finset W

  emp : W
  emp_mem : emp ∈ Wall
  cnt_emp : cnt emp = 0
  wt_emp : wt emp = 1

  gram : ℝ → ℕ → W → Pt E → Pt E → ℂ

  Kr : ℕ → Pt E → Pt E → ℂ
  K0 : Kr 0 [] [] = 1

  Th : ℕ → ℕ → E → Pt E → Pt E → ℂ

  e : ℕ → ℝ

  La : ℕ → ℕ → AddSubgroup E

  Lap : ℕ → ℕ → AddSubgroup E

  Lad : ℕ → AddSubgroup E

  Nhat : ℝ → ℕ → W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ

  szD : ℕ → Fin f → ℝ

  szL : ℕ → ℕ → Fin f → ℝ

  vol : ℕ → ℕ → ℝ
variable (D : Data E W)
namespace Data
def Ntop : ℕ := 4 * D.K * (D.r + 1)
def budget (i : ℕ) : ℕ := 4 * D.K * (D.r + 1 - i)
def Wb (n : ℕ) : Finset W := D.Wall.filter (fun w => D.cnt w ≤ n)
def Sf (ε : ℝ) (i : ℕ) (w : W) (Y : Finset (Pt E)) : ℝ :=
  (∑ p ∈ Y, ∑ q ∈ Y, D.Kr i p q * D.gram ε i w p q).re
def Q (T : Tower E) (ε : ℝ) (i : ℕ) (w : W) : ℝ := D.Sf ε i w (T.X i) / D.wt w
def Nst (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (t t' : E) : ℂ :=
  (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * D.gram ε i w (join h s t) (join h' s t')) / D.wt w
def N0 (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) : ℝ :=
  (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * D.gram ε k w h h').re / D.wt w
def maj (ρ : Fin D.f → ℝ) (l : E) : ℝ := ∏ v, min 1 ((ρ v / D.av v l) ^ D.K)
end Data
def blk (κ : Pt E → Pt E → ℂ) (s : ℕ) (t t' : E) : Pt E → Pt E → ℂ :=
  fun h h' => κ (join h s t) (join h' s t')
def Xs (T : Tower E) (i s : ℕ) : Finset (Pt E) :=
  (T.X i).filter (fun p => p.getLast?.map Prod.fst = some s)
def pts (Y : Finset (Pt E)) (s : ℕ) (S : Finset E) : Finset (Pt E) :=
  (Y ×ˢ S).image (fun x => join x.1 s x.2)
namespace Data
def Dg (T : Tower E) (ε : ℝ) (i s : ℕ) (w : W) : ℝ :=
  ∑ t ∈ T.Sg (i - s + 1) s, (D.Nst ε i s w (T.X (i - s)) (blk (D.Kr i) s t t) t t).re
def GramPSD : Prop := ∀ ε, 0 < ε → ∀ i w (Y : Finset (Pt E)), PSDOn Y (D.gram ε i w)
def WordsPos : Prop := ∀ w, 0 < D.wt w
def KernelPSD : Prop :=
  (∀ i (Y : Finset (Pt E)), PSDOn Y (D.Kr i)) ∧ (∀ i s t (Y : Finset (Pt E)), PSDOn Y (D.Th i s t))
def KernelSupport : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ (h h' : Pt E) (t t' : E),
    level h = i - s → level h' = i - s → t ≠ 0 → t' ≠ 0 → t ≠ t' →
    D.Kr i (join h s t) (join h' s t') ≠ 0 →
      ¬ (i = D.r + 1 ∧ s = 1) ∧ t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s
def ThetaDomination : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (0 ≤ D.e i ∧ D.e i ≤ 1) ∧
    (∀ t : E, t ≠ 0 → ∀ Y : Finset (Pt E), (∀ h ∈ Y, level h = i - s) →
      PSDOn Y (fun h h' => D.Th i s t h h' - blk (D.Kr i) s t t h h')) ∧
    (∀ t t' : E, t - t' ∈ D.La (i - s + 1) s → D.Th i s t = D.Th i s t') ∧
    (∀ S : Finset E, (∀ t ∈ S, ∀ t' ∈ S, t - t' ∈ D.La (i - s + 1) s → t = t') →
      ∀ Y : Finset (Pt E), (∀ h ∈ Y, level h = i - s) →
        PSDOn Y (fun h h' => (1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, D.Th i s t h h'))
def EstWave : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ D.r + 1 → ∀ w ∈ D.Wall, D.cnt w + D.K ≤ D.Ntop →
    ∃ θ : Finset (Fin D.f) → W → ℝ, (∀ A, IsProb (D.Wb (D.cnt w + D.K)) (θ A)) ∧
      ∀ Y : Finset (Pt E), (∀ h ∈ Y, level h = i - 1) → ∀ κ, PSDOn Y κ →
        D.Nhat ε i w Y κ 0 = (D.N0 ε (i - 1) w Y κ : ℂ) ∧
        ∀ l ∈ D.Lad i, l ≠ 0 → ∃ A,
          ‖D.Nhat ε i w Y κ l‖ ≤ D.maj (D.szD i) l *
            ∑ w' ∈ D.Wb (D.cnt w + D.K), θ A w' * D.N0 ε (i - 1) w' Y κ
def PoissonStep : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ D.r + 1 → ∀ (w : W) (Y : Finset (Pt E)), (∀ h ∈ Y, level h = i - 1) →
    ∀ κ, PSDOn Y κ → ∀ (t₀ : E) (B : ℝ),
      (∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lad i ∧ l ≠ 0) → ∑ l ∈ L, ‖D.Nhat ε i w Y κ l‖ ≤ B) →
      ∀ S : Finset E, (∀ t ∈ S, t ≠ 0 ∧ t - t₀ ∈ D.La i 1) →
        ∑ t ∈ S, (D.Nst ε i 1 w Y κ t t).re ≤ ‖D.Nhat ε i w Y κ 0‖ + B
def EstLift : Prop :=
  ∀ ε, 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ¬ (i = D.r + 1 ∧ s = 1) →
    ∀ w ∈ D.Wall, D.cnt w + D.K ≤ D.Ntop →
    ∃ θ : (Fin D.f → Fin 3) → W × W → ℝ,
      (∀ π, IsProb (D.Wb (D.cnt w + D.K) ×ˢ D.Wb (D.cnt w + D.K)) (θ π)) ∧
      ∀ (Y : Finset (Pt E)) (S : Finset E) (κ : Pt E → Pt E → ℂ),
        (∀ h ∈ Y, level h = i - s) → PSDOn (pts Y s S) κ →
        ∀ t ∈ S, ∀ t' ∈ S, t ≠ 0 → t' ≠ 0 → t⁻¹ - t'⁻¹ ≠ 0 →
          ∃ π, ‖D.Nst ε i s w Y (blk κ s t t') t t'‖ ≤
            D.maj (D.szL (i - s + 1) s) (t⁻¹ - t'⁻¹) *
              ∑ x ∈ D.Wb (D.cnt w + D.K) ×ˢ D.Wb (D.cnt w + D.K), θ π x *
                (((D.Nst ε i s x.1 Y (blk κ s t t) t t).re +
                  (D.Nst ε i s x.2 Y (blk κ s t' t') t' t').re) / 2)
def EstBlock (C₄ : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.r + 1 →
    ∀ w ∈ D.Wall, D.cnt w + (s + 1) * D.K ≤ D.Ntop → D.vol (i - s + 1) s ≤ 1 →
    ∃ θ : W → ℝ, IsProb (D.Wb (D.cnt w + (s + 1) * D.K)) θ ∧
      ∀ Y : Finset (Pt E), (∀ h ∈ Y, level h = i - s) → ∀ κ, PSDOn Y κ →
        ∀ (t₀ : E) (S : Finset E), (∀ t ∈ S, t ≠ 0 ∧ t - t₀ ∈ D.La (i - s + 1) s) →
          ∑ t ∈ S, (D.Nst ε i s w Y κ t t).re ≤
            C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
              ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * D.N0 ε (i - s) w' Y κ
def LatticeSums (ep : ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ D.r + 1 → ∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lad i ∧ l ≠ 0) →
    ∑ l ∈ L, D.maj (D.szD i) l ≤ ep) ∧
  (∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ¬ (i = D.r + 1 ∧ s = 1) → ∀ L : Finset E,
    (∀ l ∈ L, l ∈ D.Lap (i - s + 1) s ∧ l ≠ 0) → ∑ l ∈ L, D.maj (D.szL (i - s + 1) s) l ≤ ep)
def EstE (jn : ℝ) : Prop :=
  ∀ w ∈ D.Wb D.Ntop, Tendsto (fun ε => (D.gram ε 0 w [] []).re / D.wt w) (𝓝[>] 0) (𝓝 jn)
def Cutoff {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : Pt E → H) : Prop :=
  ∀ Y : Finset (Pt E), (∀ p ∈ Y, IsPt p (D.r + 1)) →
    ∀ᶠ ε in 𝓝[>] 0, ∀ p ∈ Y, ∀ q ∈ Y, D.Kr (D.r + 1) p q ≠ 0 →
      D.gram ε (D.r + 1) D.emp p q = ⟪Vt q, Vt p⟫
def LeadingDomination {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : Pt E → H)
    (c : ℕ → Pt E → ℂ) : Prop :=
  (∀ ρ p, c ρ p ≠ 0 → IsPt p (D.r + 1)) ∧
  (∀ Y : Finset (Pt E), (∀ p ∈ Y, IsPt p (D.r + 1)) → ∀ R : Finset ℕ,
    PSDOn Y (fun p q => D.Kr (D.r + 1) p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q))) ∧
  (∀ ρ, Summable fun p : Pt E => ‖c ρ p‖ * ‖Vt p‖)
def SizesBelow (Θ : ℝ) : Prop :=
  (∀ b s, 0 ≤ D.vol b s) ∧
  ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → D.vol b s ≤ ((Θ ^ D.f)⁻¹) ^ 2
end Data
open Data
def SplitBySize : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W), D.GramPSD → D.KernelPSD →
    ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ i, 1 ≤ i → ∀ w,
      √(D.Sf ε i w (T.X i)) ≤ ∑ s ∈ Icc 1 i, √(D.Sf ε i w (Xs T i s))
def SchurStep : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W) (ep : ℝ), D.GramPSD → D.KernelPSD → D.WordsPos →
    D.KernelSupport → D.EstLift → D.LatticeSums ep →
    ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
      ∀ w ∈ D.Wall, D.cnt w + D.K ≤ D.Ntop → ∀ M : ℝ,
        (∀ w' ∈ D.Wb (D.cnt w + D.K), D.Dg T ε i s w' ≤ M) →
        D.Sf ε i w (Xs T i s) / D.wt w ≤ D.Dg T ε i s w + 3 ^ D.f * ep * M
def DiagStep : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W), D.GramPSD → D.KernelPSD → D.WordsPos → D.ThetaDomination →
    ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ (w : W) (R : Finset E),
      (∀ t ∈ T.Sg (i - s + 1) s, ∃ t₀ ∈ R, t - t₀ ∈ D.La (i - s + 1) s) →
      D.Dg T ε i s w ≤ ∑ t₀ ∈ R, ∑ t ∈ (T.Sg (i - s + 1) s).filter (fun t => t - t₀ ∈ D.La (i - s + 1) s),
        (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re
def OneStep : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W) (ep : ℝ), D.GramPSD → D.KernelPSD → D.WordsPos →
    D.ThetaDomination → D.EstWave → D.PoissonStep → D.LatticeSums ep →
    ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ i, 1 ≤ i → i ≤ D.r + 1 →
      ∀ w ∈ D.Wall, D.cnt w + D.K ≤ D.Ntop → ∀ R : Finset E,
        (∀ t₀ ∈ R, ∀ t₀' ∈ R, t₀ - t₀' ∈ D.La i 1 → t₀ = t₀') → ∀ M : ℝ,
        (∀ w' ∈ D.Wb (D.cnt w + D.K), D.N0 ε (i - 1) w' (T.X (i - 1)) (D.Kr (i - 1)) ≤ M) →
        ∑ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
            (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re ≤
          (1 + D.e i) * (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) + 2 ^ D.f * ep * M)
def MultiStep : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W) (C₄ : ℝ), D.GramPSD → D.KernelPSD → D.WordsPos →
    D.ThetaDomination → D.EstBlock C₄ → 1 ≤ C₄ → (∀ b s, 0 ≤ D.vol b s) →
    ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.r + 1 →
      ∀ w ∈ D.Wall, D.cnt w + (s + 1) * D.K ≤ D.Ntop → D.vol (i - s + 1) s ≤ 1 →
      ∀ R : Finset E, (∀ t₀ ∈ R, ∀ t₀' ∈ R, t₀ - t₀' ∈ D.La (i - s + 1) s → t₀ = t₀') → ∀ M : ℝ,
        (∀ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), D.N0 ε (i - s) w' (T.X (i - s)) (D.Kr (i - s)) ≤ M) →
        ∑ t₀ ∈ R, ∑ t ∈ (T.Sg (i - s + 1) s).filter (fun t => t - t₀ ∈ D.La (i - s + 1) s),
            (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re ≤
          C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * ((1 + D.e i) * M)
def OneLevel : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W) (ep C₄ : ℝ), D.GramPSD → D.KernelPSD → D.WordsPos →
    D.KernelSupport → D.ThetaDomination → D.EstWave → D.PoissonStep → D.EstLift → D.EstBlock C₄ → D.LatticeSums ep →
    0 ≤ ep → 1 ≤ C₄ → (∀ b s, 0 ≤ D.vol b s) →
    (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → D.vol b s ≤ 1) →
    ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ (σ : ℕ → ℝ) (i : ℕ), 1 ≤ i → i ≤ D.r + 1 →
      (∀ k < i, 0 ≤ σ k ∧ ∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ σ k ^ 2) →
      ∀ w ∈ D.Wb (D.budget i),
        √(D.Q T ε i w) ≤
          √((1 + 3 ^ D.f * ep) * (1 + 2 ^ D.f * ep)) * √(1 + D.e i) * σ (i - 1) +
          ∑ s ∈ Icc 2 i, √((1 + 3 ^ D.f * ep) * (1 + D.e i) * C₄ ^ (D.f * s) *
              ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * σ (i - s)
def LimitStep : Prop :=
  ∀ (E W : Type) [Field E] (D : Data E W) (jn : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : Pt E → H) (c : ℕ → Pt E → ℂ),
    D.GramPSD → D.KernelPSD → D.EstE jn → D.Cutoff Vt → D.LeadingDomination Vt c → ∀ B : ℝ,
    (∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ σ₀ : ℝ,
      (∀ w ∈ D.Wb D.Ntop, (D.gram ε 0 w [] []).re / D.wt w ≤ σ₀) →
      D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤ B * σ₀) →
    ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ B * jn
def TheoremA : Prop :=
  ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
  ∀ (E W : Type) [Field E] (D : Data E W) (Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : Pt E → H) (c : ℕ → Pt E → ℂ),
    4 ≤ D.K → 1 ≤ D.f → 0 < Θ → C' ≤ Θ → (D.r : ℝ) * (C / Θ) ^ D.f ≤ 1 → D.SizesBelow Θ →
    D.GramPSD → D.KernelPSD → D.WordsPos → D.KernelSupport → D.ThetaDomination → D.EstWave → D.PoissonStep →
    D.EstLift → D.EstBlock C₄ → D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) →
    D.EstE jn → D.Cutoff Vt → D.LeadingDomination Vt c →
    ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤
      (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * jn
def OneLevelOfSteps : Prop :=
  SplitBySize → SchurStep → DiagStep → OneStep → MultiStep → OneLevel
def TheoremAOfSteps : Prop :=
  OneLevel → LimitStep → Formalism.FourierDecayAlt.K.JointTheoremA → TheoremA
end
end Formalism.FourierDecayAlt.TB


