-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementTC
-- name    : Formalism_HermitianCurvature_StatementTC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:58.505835+00:00
-- url     : https://prove2.me/theorems/cfbf1754-509e-4692-817d-cc11c6a630da
-- title:
--   Statement TC
-- statement:
--   Definitions and structural lemmas for Statement TC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementTC.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_StatementJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.TC
open Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
section towers
open TB TB.Data
variable {E W : Type} [Field E]
def withTh (D : TB.Data E W) (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) : TB.Data E W :=
  { D with Th := Th }
def KrPSD (D : TB.Data E W) : Prop := ∀ i (Y : Finset (TB.Pt E)), TB.PSDOn Y (D.Kr i)
def EBounds (D : TB.Data E W) : Prop := ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1
def DomText (D : TB.Data E W) (T : TB.Tower E) (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ t : E, TB.PSDOn (T.X (i - s)) (Th i s t)) ∧
    (∀ t : E, t ≠ 0 →
      TB.PSDOn (T.X (i - s)) (fun h h' => Th i s t h h' - TB.blk (D.Kr i) s t t h h')) ∧
    (∀ t t' : E, t - t' ∈ D.La (i - s + 1) s →
      ∀ h ∈ T.X (i - s), ∀ h' ∈ T.X (i - s), Th i s t h h' = Th i s t' h h') ∧
    (∀ S : Finset E, (∀ t ∈ S, ∀ t' ∈ S, t - t' ∈ D.La (i - s + 1) s → t = t') →
      TB.PSDOn (T.X (i - s))
        (fun h h' => (1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, Th i s t h h'))
def DomMin (D : TB.Data E W) (T : TB.Tower E) (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ t ∈ T.Sg (i - s + 1) s,
      TB.PSDOn (T.X (i - s)) (fun h h' => Th i s t h h' - TB.blk (D.Kr i) s t t h h')) ∧
    (∀ t ∈ T.Sg (i - s + 1) s, ∀ t' ∈ T.Sg (i - s + 1) s, t - t' ∈ D.La (i - s + 1) s →
      ∀ h ∈ T.X (i - s), ∀ h' ∈ T.X (i - s), Th i s t h h' = Th i s t' h h') ∧
    (∀ S : Finset E, S ⊆ T.Sg (i - s + 1) s →
      (∀ t ∈ S, ∀ t' ∈ S, t - t' ∈ D.La (i - s + 1) s → t = t') →
      TB.PSDOn (T.X (i - s))
        (fun h h' => (1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, Th i s t h h'))
def DomAfter (D : TB.Data E W) : Prop := ∀ T : TB.Tower E, ∃ Th, DomMin D T Th
end towers
def DomMinOfText : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (T : TB.Tower E) Th, DomText D T Th → DomMin D T Th
def AfterOfOld : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W), D.KernelPSD → D.ThetaDomination →
    KrPSD D ∧ EBounds D ∧ (∀ T : TB.Tower E, DomText D T D.Th) ∧ DomAfter D
def MajorantPSD : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (T : TB.Tower E) Th, KrPSD D → DomMin D T Th →
    ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ t ∈ T.Sg (i - s + 1) s, TB.PSDOn (T.X (i - s)) (Th i s t)
def DomMonoE : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (T : TB.Tower E) Th (e' : ℕ → ℝ), KrPSD D →
    (∀ i, D.e i ≤ e' i) → DomMin D T Th → DomMin { D with e := e' } T Th
def OneLevelAfter : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (ep C₄ : ℝ), D.GramPSD → KrPSD D → D.WordsPos →
    D.KernelSupport → EBounds D → D.EstWave → D.PoissonStep → D.EstLift → D.EstBlock C₄ → D.LatticeSums ep →
    0 ≤ ep → 1 ≤ C₄ → (∀ b s, 0 ≤ D.vol b s) →
    (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → D.vol b s ≤ 1) →
    ∀ (T : TB.Tower E), (∃ Th, DomMin D T Th) →
    ∀ (ε : ℝ), 0 < ε → ∀ (σ : ℕ → ℝ) (i : ℕ), 1 ≤ i → i ≤ D.r + 1 →
      (∀ k < i, 0 ≤ σ k ∧ ∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ σ k ^ 2) →
      ∀ w ∈ D.Wb (D.budget i),
        √(D.Q T ε i w) ≤
          √((1 + 3 ^ D.f * ep) * (1 + 2 ^ D.f * ep)) * √(1 + D.e i) * σ (i - 1) +
          ∑ s ∈ Icc 2 i, √((1 + 3 ^ D.f * ep) * (1 + D.e i) * C₄ ^ (D.f * s) *
              ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * σ (i - s)
def OneLevelAfterOfOld : Prop := TB.OneLevel → OneLevelAfter
def TheoremAAfter : Prop :=
  ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
    4 ≤ D.K → 1 ≤ D.f → 0 < Θ → C' ≤ Θ → (D.r : ℝ) * (C / Θ) ^ D.f ≤ 1 → D.SizesBelow Θ →
    D.GramPSD → KrPSD D → D.WordsPos → D.KernelSupport → EBounds D → DomAfter D → D.EstWave →
    D.PoissonStep → D.EstLift → D.EstBlock C₄ →
    D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) →
    D.EstE jn → D.Cutoff Vt → D.LeadingDomination Vt c →
    ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤
      (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * jn
def TheoremAAfterOfSteps : Prop :=
  OneLevelAfter → TB.LimitStep → Formalism.FourierDecayAlt.K.JointTheoremA → TheoremAAfter
def TheoremAOfAfter : Prop := TheoremAAfter → TB.TheoremA
section sets
variable {E : Type} [Field E] [DecidableEq E]
def withThA (D : TA.Data E) (Th : ℕ → ℕ → E → TA.Pt E → TA.Pt E → ℂ) : TA.Data E :=
  { D with Th := Th }
def DomTextA (D : TA.Data E) (Sg : ℕ → ℕ → Finset E)
    (Th : ℕ → ℕ → E → TA.Pt E → TA.Pt E → ℂ) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ t : E, TA.PSDOn (TA.PT Sg (i - s)) (Th i s t)) ∧
    (∀ t l : E, l ∈ D.La i s →
      ∀ h ∈ TA.PT Sg (i - s), ∀ h' ∈ TA.PT Sg (i - s), Th i s (t + l) h h' = Th i s t h h') ∧
    (∀ t : E, t ≠ 0 → TA.PSDOn (TA.PT Sg (i - s))
      (fun h h' => Th i s t h h' - D.K i (TA.ext h s t) (TA.ext h' s t))) ∧
    (∀ R : Finset E, (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      TA.PSDOn (TA.PT Sg (i - s))
        (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.K (i - s) h h' - ∑ t ∈ R, Th i s t h h'))
def DomMinA (D : TA.Data E) (Sg : ℕ → ℕ → Finset E)
    (Th : ℕ → ℕ → E → TA.Pt E → TA.Pt E → ℂ) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ t ∈ Sg i s, TA.PSDOn (TA.PT Sg (i - s))
      (fun h h' => Th i s t h h' - D.K i (TA.ext h s t) (TA.ext h' s t))) ∧
    (∀ t ∈ Sg i s, ∀ t' ∈ Sg i s, t - t' ∈ D.La i s →
      ∀ h ∈ TA.PT Sg (i - s), ∀ h' ∈ TA.PT Sg (i - s), Th i s t h h' = Th i s t' h h') ∧
    (∀ R : Finset E, R ⊆ Sg i s → (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      TA.PSDOn (TA.PT Sg (i - s))
        (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.K (i - s) h h' - ∑ t ∈ R, Th i s t h h'))
def DomAfterA (D : TA.Data E) : Prop :=
  ∀ Sg : ℕ → ℕ → Finset E, TA.NZSg Sg → ∃ Th, DomMinA D Sg Th
end sets
def DomMinOfTextA : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) Th,
    TA.NZSg Sg → DomTextA D Sg Th → DomMinA D Sg Th
def AfterOfOldA : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (D : TA.Data E), TA.ThetaDomination D →
    (∀ Sg : ℕ → ℕ → Finset E, TA.NZSg Sg → DomTextA D Sg D.Th) ∧ DomAfterA D
def MajorantPSDA : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) Th,
    TA.NZSg Sg → TA.AxK D → DomMinA D Sg Th →
    ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ t ∈ Sg i s, TA.PSDOn (TA.PT Sg (i - s)) (Th i s t)
def OneLevelAfterA : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) [Fintype W] (len : W → ℕ) (Kl : ℕ) (D : TA.Data E) (Sg : ℕ → ℕ → Finset E)
    (Φ : W → TA.Pt E → H) (tr : W → Finset (TA.Pt E) → (TA.Pt E → TA.Pt E → ℂ) → E → ℂ)
    (Pat1 Pat3 : Type) [Fintype Pat3] (pat1 : E → Pat1) (pat3 : ℕ → E → E → Pat3) (c1 : E → ℝ)
    (c3 : ℕ → E → ℝ) (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ),
    TA.NZSg Sg → 1 ≤ i → i ≤ D.r + 1 → 0 ≤ ep → 0 ≤ a →
    TA.AxK D → TA.KernelSupport D → (∃ Th, DomMinA D Sg Th) → TA.AxE D →
    TA.LevelEst len Kl D Φ tr pat1 pat3 c1 c3 bd4 i →
    TA.LevelSizes D Pat3 c1 c3 ep1 ep3 bd4 ep a i →
      √(TA.lsup D len Kl Sg Φ i) ≤ (1 + ep) * √(1 + D.e i) * √(TA.lsup D len Kl Sg Φ (i - 1)) +
        ∑ s ∈ Icc 2 i, a ^ (s - 1) * √(TA.lsup D len Kl Sg Φ (i - s))
def OneLevelAfterOfOldA : Prop := TA.OneLevel → OneLevelAfterA
def ReductionAfter : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ,
    ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (W : Type) [Fintype W] (len : W → ℕ) (Kl f : ℕ) (Θ : ℝ) (D : TA.Data E)
      (Pat1 Pat3 : Type) [Fintype Pat3] (pat1 : ℕ → E → Pat1) (pat3 : ℕ → ℕ → E → E → Pat3)
      (c1 : ℕ → E → ℝ) (c3 : ℕ → ℕ → E → ℝ) (ep1 : ℕ → ℝ) (ep3 bd4 : ℕ → ℕ → ℝ)
      (Φ : ℝ → W → TA.Pt E → H)
      (tr : ℝ → ℕ → W → Finset (TA.Pt E) → (TA.Pt E → TA.Pt E → ℂ) → E → ℂ)
      (w0 : W) (V : TA.Pt E → H) (jn : ℝ) (ρ : Type) (c : ρ → TA.Pt E → ℂ),
      4 ≤ Kl → 1 ≤ f → C' ≤ Θ → (D.r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
      TA.AxK D → TA.KernelSupport D → DomAfterA D → TA.AxE D →
      (∀ i ∈ Icc 1 (D.r + 1), TA.LevelSizes D Pat3 (c1 i) (c3 i) (ep1 i) (ep3 i) (bd4 i)
        ((C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f) ((C₀ / Θ) ^ f) i) →
      (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.r + 1),
        TA.LevelEst len Kl D (Φ eps) (tr eps i) (pat1 i) (pat3 i) (c1 i) (c3 i) (bd4 i) i) →
      (∀ w, len w ≤ 4 * Kl * (D.r + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
      len w0 = 0 →
      (∀ p, TA.IsPt (D.r + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = V p) →
      (∀ (P : Finset (TA.Pt E)) (R : Finset ρ), (∀ p ∈ P, TA.IsPt (D.r + 1) p) →
        TA.PSDOn P (fun p p' => D.K (D.r + 1) p p' - ∑ x ∈ R, conj (c x p) * c x p')) →
      (∀ x, Summable (fun p : {p : TA.Pt E // TA.IsPt (D.r + 1) p} => ‖c x p.1‖ * ‖V p.1‖)) →
        ∀ R : Finset ρ,
          ∑ x ∈ R, ‖∑' p : {p : TA.Pt E // TA.IsPt (D.r + 1) p}, c x p.1 • V p.1‖ ^ 2 ≤
          (1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * jn
def ReductionAfterOfSteps : Prop :=
  OneLevelAfterA → TA.EpsLimit → TA.TopDominationLimit → Formalism.FourierDecayAlt.K.JointTheoremA → ReductionAfter
def ReductionOfAfter : Prop := ReductionAfter → TA.TheoremAReduction
def DomAgree : Prop :=
  J.PSDAgree → J.PSDTranspose → J.TowersAgree →
  ∀ (E W : Type) [Field E] [DecidableEq E] (D : TB.Data E W) (T : TB.Tower E) Th,
    DomMin D T Th →
    DomMinA (J.toTA D) (fun j s => T.Sg (j - s + 1) s) (fun i s t h h' => Th i s t h' h)
def DomTextOfSystems : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (T : TB.Tower E) Th,
    (∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → (J.sysOf (withTh D Th) i s).Ok (T.X (i - s))) →
    DomText D T Th
def RecHypAfter {E W : Type} [Field E] (D : TB.Data E W) (C₁ C₄ Θ jn : ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) : Prop :=
  4 ≤ D.K ∧ 1 ≤ D.f ∧ 0 < Θ ∧ D.SizesBelow Θ ∧ D.GramPSD ∧ KrPSD D ∧ D.WordsPos ∧ D.KernelSupport ∧
  EBounds D ∧ DomAfter D ∧ D.EstWave ∧ D.PoissonStep ∧ D.EstLift ∧ D.EstBlock C₄ ∧
  D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) ∧ D.EstE jn ∧ D.Cutoff Vt ∧ D.LeadingDomination Vt c
def RecHypAfterOfOld : Prop :=
  AfterOfOld → ∀ (E W : Type) [Field E] (D : TB.Data E W) (C₁ C₄ Θ jn : ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
    J.RecHyp D C₁ C₄ Θ jn Vt c → RecHypAfter D C₁ C₄ Θ jn Vt c
def RecursionGivesUniformBoundsAfter : Prop :=
  TheoremAAfter → ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
    ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
      RecHypAfter D C₁ C₄ Θ jn Vt c → C' ≤ Θ → (D.r : ℝ) * (C / Θ) ^ D.f ≤ 1 →
      (∀ i ∈ Icc 1 (D.r + 1), D.e i = 0) →
      ∀ (P : Type) [Fintype P] (B : S3.MassData P), B.IntN = jn →
        B.δ = C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f →
        (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) → B.Smod ≤ M) →
        B.InTheoremA
def EOfDens : Prop :=
  ∀ (r : ℕ) (e : ℕ → ℝ) (sd : ℝ), (∀ i ∈ Icc 1 r, e i = 0) → 1 + e (r + 1) = max sd 1 → sd ≤ 2 →
    ∀ i, 1 ≤ i → i ≤ r + 1 → 0 ≤ e i ∧ e i ≤ 1
def ProductOfEMax : Prop :=
  ∀ (r : ℕ) (e : ℕ → ℝ) (sd : ℝ), (∀ i ∈ Icc 1 r, e i = 0) → 1 + e (r + 1) = max sd 1 →
    ∏ i ∈ Icc 1 (r + 1), (1 + e i) = max sd 1
def DensLeTwo : Prop :=
  ∀ f n : ℕ, 18 * f ≤ 2 ^ n → Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹) ≤ 2
def DensSize : Prop :=
  ∀ k r f : ℕ, 2 * r + 2 + f + 5 ≤ k → 18 * f ≤ 2 ^ (k - 2 * r - 2)
def SumBoundMax : Prop :=
  ∀ (α : Type) (Y : Finset α) (k m : α → α → ℂ) (sd : ℝ), TB.PSDOn Y k →
    TB.PSDOn Y (fun x y => (sd : ℂ) * k x y - m x y) →
    TB.PSDOn Y (fun x y => ((max sd 1 : ℝ) : ℂ) * k x y - m x y)
def RecursionWithDens : Prop :=
  TheoremAAfter → ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
    ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) (sd : ℝ),
      RecHypAfter D C₁ C₄ Θ jn Vt c → C' ≤ Θ → (D.r : ℝ) * (C / Θ) ^ D.f ≤ 1 →
      (∀ i ∈ Icc 1 D.r, D.e i = 0) → 1 + D.e (D.r + 1) = max sd 1 →
      ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤
        (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * max sd 1 * jn
def OnceOnlyMax : Prop :=
  J.OnceOnly → ∀ (P : Type) [Fintype P] (B : S3.MassData P), B.Pos → B.InKernel → B.InTheoremA →
    B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * max B.supdens 1 * (B.n0c * B.IntN)
def MassDataCovers : Prop :=
  ∀ (P : Type) [Fintype P] (B : S3.MassData P) (r : ℕ) (e : ℕ → ℝ), B.InDens → 1 ≤ B.e1 →
    (∀ i ∈ Icc 1 r, e i = 0) → 1 + e (r + 1) = max B.supdens 1 →
    ∏ i ∈ Icc 1 (r + 1), (1 + e i) ≤ B.e1
def scaleTop {E W : Type} [Field E] (D : TB.Data E W) (lam : ℝ) : TB.Data E W :=
  { D with
    Kr := fun i p q => if i = D.r + 1 then (lam : ℂ) * D.Kr i p q else D.Kr i p q
    K0 := by simp [D.K0]
    e := fun i => if i = D.r + 1 then lam - 1 else D.e i }
def DomScaleTop : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (T : TB.Tower E) Th (lam : ℝ), 0 ≤ lam →
    D.e (D.r + 1) = 0 → DomMin D T Th →
    DomMin (scaleTop D lam) T
      (fun i s t h h' => if i = D.r + 1 then (lam : ℂ) * Th i s t h h' else Th i s t h h')
def RecHypScaleTop : Prop :=
  DomScaleTop → SumBoundMax →
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (C₁ C₄ Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) (c c' : ℕ → TB.Pt E → ℂ) (sd : ℝ),
    sd ≤ 2 → D.e (D.r + 1) = 0 → RecHypAfter D C₁ C₄ Θ jn Vt c →
    (∀ ρ p, c' ρ p ≠ 0 → TB.IsPt p (D.r + 1)) →
    (∀ Y : Finset (TB.Pt E), (∀ p ∈ Y, TB.IsPt p (D.r + 1)) → ∀ R : Finset ℕ,
      TB.PSDOn Y (fun p q => (sd : ℂ) * D.Kr (D.r + 1) p q - ∑ ρ ∈ R, c' ρ p * conj (c' ρ q))) →
    (∀ ρ, Summable fun p : TB.Pt E => ‖c' ρ p‖ * ‖Vt p‖) →
    RecHypAfter (scaleTop D (max sd 1)) C₁ C₄ Θ jn Vt c' ∧
      (scaleTop D (max sd 1)).r = D.r ∧ (scaleTop D (max sd 1)).f = D.f ∧
      1 + (scaleTop D (max sd 1)).e (D.r + 1) = max sd 1 ∧
      ∀ i ∈ Icc 1 D.r, (scaleTop D (max sd 1)).e i = D.e i
def DomAfterOfLocal : Prop :=
  J.ProductLemma → J.ScaleOk → DomMinOfText →
  ∀ (E W : Type) [Field E] (D : TB.Data E W),
    (∀ (T : TB.Tower E) (i s : ℕ), 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
      ∃ (P : Type) (_ : Fintype P) (S : P → J.LocSys E (TB.Pt E)) (a : TB.Pt E → ℝ),
        (∀ p, (S p).Ok (T.X (i - s))) ∧
        (∀ t : E, t ≠ 0 → ∀ h ∈ T.X (i - s), ∀ h' ∈ T.X (i - s),
          (J.sysOf D i s).N t t h h' = (J.scaleSys a (J.prodSys S)).N t t h h') ∧
        (∀ h ∈ T.X (i - s), ∀ h' ∈ T.X (i - s),
          (J.sysOf D i s).B h h' = (J.scaleSys a (J.prodSys S)).B h h') ∧
        (J.sysOf D i s).L = ⨅ p, (S p).L) →
    (∀ T : TB.Tower E, ∃ Th, DomText D T Th) ∧ DomAfter D
def DensSum : Prop :=
  ∀ (P : Type) (S : Finset P) (q : P → ℝ) (l : P → ℕ) (f n : ℕ), 2 ≤ n →
    (∀ p ∈ S, (l p).Prime ∧ ((l p : ℕ) : ℝ) ≤ q p) →
    (∀ m : ℕ, (S.filter fun p => l p = m).card ≤ f) →
    ∑ p ∈ S, (q p ^ n)⁻¹ ≤ 3 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹
def DensChain : Prop :=
  DensSum → DensLeTwo → DensSize →
  ∀ (P : Type) (q : P → ℝ) (l : P → ℕ) (k r f : ℕ) (sd : ℝ),
    2 * r + 2 + f + 5 ≤ k → (∀ p, (l p).Prime ∧ ((l p : ℕ) : ℝ) ≤ q p) →
    (∀ (m : ℕ) (S : Finset P), (∀ p ∈ S, l p = m) → S.card ≤ f) →
    (∀ x : ℝ, x < sd → ∃ S : Finset P, x ≤ ∏ p ∈ S, Real.exp (4 * (q p ^ (k - 2 * r - 2))⁻¹)) →
    sd ≤ Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹) ∧ sd ≤ 2
end
end Formalism.FourierDecayAlt.TC


