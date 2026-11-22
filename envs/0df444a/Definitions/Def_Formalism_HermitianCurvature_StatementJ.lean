-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementJ
-- name    : Formalism_HermitianCurvature_StatementJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:02.640896+00:00
-- url     : https://prove2.me/theorems/c7191b0d-3d1e-417b-988e-bb471d9e3f75
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementJ.lean

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.J
open Finset NumberField
open scoped ComplexConjugate nonZeroDivisors
noncomputable section
def PSDAgree : Prop :=
  ∀ (α : Type) (F : Finset α) (k : α → α → ℂ),
    (TB.PSDOn F k ↔ TA.PSDOn F k) ∧ (A5.IsPSD F k ↔ TA.PSDOn F k)
def PSDTranspose : Prop :=
  ∀ (α : Type) (F : Finset α) (k : α → α → ℂ), TB.PSDOn F k → TB.PSDOn F (fun x y => k y x)
def toTA {E W : Type} [Field E] (D : TB.Data E W) : TA.Data E where
  r := D.r
  K := fun i p q => D.Kr i q p
  Th := fun i s t h h' => D.Th i s t h' h
  e := D.e
  La := fun i s => D.La (i - s + 1) s
  Lf := fun i s => D.Lap (i - s + 1) s
  Lv := fun i => D.Lad i
def AxiomsAgree : Prop :=
  ∀ (E W : Type) [Field E] [DecidableEq E] (D : TB.Data E W), D.KernelPSD → D.KernelSupport → D.ThetaDomination →
    TA.AxK (toTA D) ∧ TA.KernelSupport (toTA D) ∧ TA.ThetaDomination (toTA D) ∧ TA.AxE (toTA D)
def TowersAgree : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (T : TB.Tower E) (i : ℕ),
    T.X i = TA.PT (fun j s => T.Sg (j - s + 1) s) i
def FormsAgree : Prop :=
  ∀ (E W : Type) [Field E] [DecidableEq E] (D : TB.Data E W) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Φ : W → TA.Pt E → H) (T : TB.Tower E) (ε : ℝ) (i : ℕ) (w : W),
    D.wt w ≠ 0 → (∀ p q, D.gram ε i w p q = (D.wt w : ℂ) * inner ℂ (Φ w q) (Φ w p)) →
    D.Q T ε i w = TA.Slev (toTA D) (fun j s => T.Sg (j - s + 1) s) Φ w i
def prof {E : Type} [Field E] [NumberField E] (x : InfinitePlace E → ℝ) (K : ℕ) (l : E) : ℝ :=
  ∏ w, min 1 ((x w / w l) ^ K)
def BoxSumLattice : Prop :=
  Formalism.SA.C.BoxSum → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (aa : FractionalIdeal (𝓞 E)⁰ E)
      (L : AddSubgroup E) (x : InfinitePlace E → ℝ) (K : ℕ) (Θ a : ℝ),
      aa ≠ 0 → (∀ l ∈ L, l ∈ aa) → (∀ w, 0 ≤ x w) → 3 ≤ K → 1 ≤ a → 2 * a < Θ →
      ∏ w, x w ≤ (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) →
      TA.LatSum L (prof x K)
        ((C * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E))
def PlacesOf {E W : Type} [Field E] [NumberField E] (D : TB.Data E W)
    (e : Fin D.f ≃ InfinitePlace E) : Prop :=
  ∀ v l, D.av v l = e v l
def MajIsProf : Prop :=
  ∀ (E W : Type) [Field E] [NumberField E] (D : TB.Data E W) (e : Fin D.f ≃ InfinitePlace E),
    PlacesOf D e → ∀ (ρ : Fin D.f → ℝ) (l : E), D.maj ρ l = prof (fun w => ρ (e.symm w)) D.K l
def IdealSizes {E W : Type} [Field E] [NumberField E] (D : TB.Data E W)
    (aaD : ℕ → FractionalIdeal (𝓞 E)⁰ E) (aaL : ℕ → ℕ → FractionalIdeal (𝓞 E)⁰ E) (Θ a : ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ D.r + 1 →
    aaD i ≠ 0 ∧ (∀ l ∈ D.Lad i, l ∈ aaD i) ∧ (∀ v, 0 ≤ D.szD i v) ∧
      ∏ v, D.szD i v ≤ (1 / Θ) ^ D.f * √(FractionalIdeal.absNorm (aaD i) : ℝ)) ∧
  (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → ¬ (b = D.r + 1 ∧ s = 1) →
    aaL b s ≠ 0 ∧ (∀ l ∈ D.Lap b s, l ∈ aaL b s) ∧ (∀ v, 0 ≤ D.szL b s v) ∧
      ∏ v, D.szL b s v ≤ (a / Θ) ^ D.f * √(FractionalIdeal.absNorm (aaL b s) : ℝ))
def LatticeSumsJoint : Prop :=
  Formalism.SA.C.BoxSum → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E W : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (aaD : ℕ → FractionalIdeal (𝓞 E)⁰ E)
      (aaL : ℕ → ℕ → FractionalIdeal (𝓞 E)⁰ E) (Θ a : ℝ),
      PlacesOf D e → 3 ≤ D.K → 1 ≤ a → 2 * a < Θ → IdealSizes D aaD aaL Θ a →
      D.LatticeSums ((C * a ^ ((D.K : ℝ) - 5 / 2) * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
def LevelSizesJoint : Prop :=
  ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ →
    ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ : ℝ), 4 ≤ D.K → 1 ≤ D.f → 3 * C₁ ≤ Θ →
      (∀ v l, 0 ≤ D.av v l) → (∀ i v, 0 ≤ D.szD i v) → (∀ b s v, 0 ≤ D.szL b s v) →
      (∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1) → D.SizesBelow Θ →
      D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) →
      ∀ i ∈ Icc 1 (D.r + 1),
        TA.LevelSizes (toTA D) (Fin D.f → Fin 3) (D.maj (D.szD i))
          (fun s => D.maj (D.szL (i - s + 1) s))
          ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
          (fun _ => (C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
          (fun s => C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s')
          ((max (3 * C₁) (2 * C₄) * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
          ((max (3 * C₁) (2 * C₄) / Θ) ^ D.f) i
def LevelSizesJointMean : Prop :=
  ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ →
    ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ : ℝ), 4 ≤ D.K → 1 ≤ D.f → 3 * C₁ ≤ Θ →
      (∀ v l, 0 ≤ D.av v l) → (∀ i v, 0 ≤ D.szD i v) → (∀ b s v, 0 ≤ D.szL b s v) →
      (∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1) → D.SizesBelow Θ →
      D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) →
      ∀ i ∈ Icc 1 (D.r + 1),
        TA.LevelSizes (toTA D) (Fin D.f → Fin 3) (fun l => 2 ^ D.f * D.maj (D.szD i) l)
          (fun s => D.maj (D.szL (i - s + 1) s))
          (2 ^ D.f * (C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
          (fun _ => (C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
          (fun s => C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s')
          ((max (3 * C₁) (2 * C₄) * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
          ((max (3 * C₁) (2 * C₄) / Θ) ^ D.f) i
section Blocks
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
def LaB (g r b s : ℕ) : AddSubgroup E := (S6.perLat E g (S6.nuBlock r b s) s).toAddSubgroup
def LapB (g r b s : ℕ) : AddSubgroup E := (S6.liftLat E g (S6.nuBlock r b s) s).toAddSubgroup
def LadB (g r b : ℕ) : AddSubgroup E :=
  (S6.dualLat E g (S6.perLat E g (S6.nuBlock r b 1) 1)).toAddSubgroup
end Blocks
def NuIndex : Prop :=
  ∀ r i s : ℕ, 1 ≤ s → s ≤ i →
    S6.nuBlock r ((i - s + 1 : ℕ) : ℤ) s = 2 * r + 1 - 2 * i + s ∧
      S6.nuBlock r ((i - s + 1 : ℕ) : ℤ) s = 2 * ((r : ℤ) + 1) - ((i - s + 1 : ℕ) : ℤ) - i
def BlockLattices : Prop :=
  S6.LatticesGeneral → S6.IdealsMatch → S6.NormIdl →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], S6.Unram E → ∀ g r b s : ℕ, 0 < g →
      (∀ l ∈ LadB E g r b, l ∈ S6.dualIdl E g (S6.nuBlock r b 1)) ∧
      (∀ l ∈ S6.dualLat E g (S6.perLat E g (S6.nuBlock r b s) s), l ∈ S6.dualIdl E g (S6.nuBlock r b s)) ∧
      (∀ l ∈ LapB E g r b s, l ∈ S6.liftIdl E g (S6.nuBlock r b s)) ∧
      S6.dualIdl E g (S6.nuBlock r b s) ≠ 0 ∧ S6.liftIdl E g (S6.nuBlock r b s) ≠ 0 ∧
      S6.liftIdl E g (S6.nuBlock r b s) = S6.dualIdl E g (S6.nuBlock r b (s + 1 : ℕ)) ∧
      √(FractionalIdeal.absNorm (S6.dualIdl E g (S6.nuBlock r b s)) : ℝ) =
        (((g : ℝ) * S6.rd E ^ ((2 * r + 4 : ℤ) - 2 * b - s)) ^ S6.deg E)⁻¹ ∧
      √(FractionalIdeal.absNorm (S6.liftIdl E g (S6.nuBlock r b s)) : ℝ) =
        (((g : ℝ) * S6.rd E ^ ((2 * r + 3 : ℤ) - 2 * b - s)) ^ S6.deg E)⁻¹
section Frame
variable (E : Type) [Field E] [NumberField E]
abbrev CV : Type := EuclideanSpace ℂ (InfinitePlace E)
def cemb : E →+ CV E where
  toFun t := WithLp.toLp 2 (fun w : InfinitePlace E => w.embedding t)
  map_zero' := by ext w; simp
  map_add' := fun a b => by ext w; simp
def semb (c : ℝ) : E →+ CV E :=
  ((c • (LinearMap.id : CV E →ₗ[ℝ] CV E)).toAddMonoidHom).comp (cemb E)
def eLat (L : Submodule ℤ E) (c : ℝ) : Submodule ℤ (CV E) := L.map (semb E c).toIntLinearMap
def dm (g : ℕ) (c : ℝ) (l : E) : CV E :=
  WithLp.toLp 2 (fun w : InfinitePlace E => ((2 / ((g : ℝ) * c) : ℝ) : ℂ) * conj (w.embedding l))
def coord (w : InfinitePlace E) : CV E →L[ℝ] ℂ :=
  (EuclideanSpace.proj w : CV E →L[ℂ] ℂ).restrictScalars ℝ
end Frame
def EmbFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    Function.Injective (cemb E) ∧ (Function.Bijective fun (x : CV E) (w : InfinitePlace E) => coord E w x) ∧
    (∀ (t : E) (w : InfinitePlace E), ‖coord E w (cemb E t)‖ = w t) ∧
    (∀ (c : ℝ) (t : E), semb E c t = c • cemb E t) ∧
    ∀ (g : ℕ) (c : ℝ) (l : E) (w : InfinitePlace E), ‖coord E w (dm E g c l)‖ = |2 / ((g : ℝ) * c)| * w l
open scoped Classical in

def EuclidFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E) (c : ℝ),
    DiscreteTopology (S6.frameLat E L c) →
    Submodule.span ℝ (S6.frameLat E L c : Set (mixedEmbedding.mixedSpace E)) = ⊤ →
    DiscreteTopology (eLat E L c) ∧ Submodule.span ℝ (eLat E L c : Set (CV E)) = ⊤ ∧
      ZLattice.covolume (eLat E L c) =
        ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (S6.frameLat E L c)
def TracePairing : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (c : ℝ) (l t : E), 0 < g → c ≠ 0 →
    inner ℝ (dm E g c l) (semb E c t) = ((Algebra.trace ℚ E (l * t / g) : ℚ) : ℝ)
def TraceDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E) (g : ℕ) (c : ℝ),
    0 < g → c ≠ 0 → (∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L) →
    ∀ μ : CV E, μ ∈ Formalism.H.dual (eLat E L c) ↔ ∃ l ∈ S6.dualLat E g L, dm E g c l = μ
def BlockFrame : Prop :=
  S6.LatticesGeneral → EuclidFrame →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], S6.Unram E →
      ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
        DiscreteTopology (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν))) ∧
        Submodule.span ℝ (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν)) : Set (CV E)) = ⊤ ∧
        ZLattice.covolume (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν))) =
          (S6.rd E / 2) ^ S6.deg E * (g : ℝ) ^ (3 * S6.deg E)
open scoped Classical in

def DualCovolume : Prop :=
  S6.DegreeFacts → S6.PowConjStable → S6.UnramRelative → S6.Between → S6.IndexCore → S6.DualSubset →
    S6.DualSupset → S6.NormIdl → S6.CovolumeIndex →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], S6.Unram E →
      ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
        ZLattice.covolume (E := mixedEmbedding.mixedSpace E)
            (S6.frameLat E (S6.dualLat E g (S6.perLat E g ν s)) (S6.rd E ^ (ν + 1))) =
          (S6.rd E / 2 / g) ^ S6.deg E
open scoped Classical in

def DualMeasureBound : Prop :=
  S6.DegreeFacts → S6.PowConjStable → S6.UnramRelative → S6.Between → S6.IndexCore → S6.DualSubset →
    S6.DualSupset → S6.NormIdl → S6.CovolumeIndex →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], S6.Unram E →
      ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
        ZLattice.covolume (E := mixedEmbedding.mixedSpace E)
            (S6.frameLat E (S6.dualLat E g (S6.perLat E g ν s)) 1) =
          ((g : ℝ) * (S6.rd E / 2)) ^ S6.deg E * (FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ) ∧
        (2 ≤ S6.rd E →
          (ZLattice.covolume (E := mixedEmbedding.mixedSpace E)
              (S6.frameLat E (S6.dualLat E g (S6.perLat E g ν s)) 1))⁻¹ ≤
            ((FractionalIdeal.absNorm (S6.dualIdl E g ν) : ℝ))⁻¹)
def DualCovolumeCV : Prop :=
  S6.LatticesGeneral → EuclidFrame → BlockFrame →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.H.DualIsLattice (CV E) →
      Formalism.H.CovolumeDual (CV E) → S6.Unram E → ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
        ZLattice.covolume (Formalism.H.dual (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν)))) =
          ((S6.rd E / 2) ^ S6.deg E * (g : ℝ) ^ (3 * S6.deg E))⁻¹
section Poisson
open MeasureTheory Formalism.H
open scoped FourierTransform
def PoissonJoint : Prop :=
  F7.PoissonStepText →
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (π : ι → V →L[ℝ] ℂ),
    (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (E : Type) [AddCommGroup E]
      (emb : E →+ V) (dmap : E → V) (La Lad : AddSubgroup E) (φ : V → ℝ) (Cφ : ℝ) (nh : E → ℂ),
      Function.Injective emb → (∀ t ∈ La, emb t ∈ Λ) → dmap 0 = 0 →
      (∀ μ ∈ dual Λ, ∃ l ∈ Lad, dmap l = μ) →
      Continuous φ → (∀ c, |φ c| ≤ Cφ * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) → (∀ c, 0 ≤ φ c) →
      (∀ l, nh l = ((ZLattice.covolume Λ : ℝ) : ℂ)⁻¹ * (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) (dmap l)) →
      ∀ (t₀ : E) (B : ℝ),
        (∀ L : Finset E, (∀ l ∈ L, l ∈ Lad ∧ l ≠ 0) → ∑ l ∈ L, ‖nh l‖ ≤ B) →
        ∀ S : Finset E, (∀ t ∈ S, t - t₀ ∈ La) → ∑ t ∈ S, φ (emb t) ≤ ‖nh 0‖ + B
def TransformAtZero : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (φ : V → ℝ),
    (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) 0 = ∫ v, (φ v : ℂ)
def Frames {E : Type} [Field E] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (r : ℕ) (La Lad : ℕ → AddSubgroup E) (Λ : ℕ → Submodule ℤ V) (emb : ℕ → E →+ V)
    (dmap : ℕ → E → V) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r + 1 → Function.Injective (emb i) ∧ (∀ t ∈ La i, emb i t ∈ Λ i) ∧ dmap i 0 = 0 ∧
    ∀ μ ∈ dual (Λ i), ∃ l ∈ Lad i, dmap i l = μ
def WaveFn {E W : Type} [Field E] (D : TB.Data E W) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] {ι : Type}
    [Fintype ι] (π : ι → V →L[ℝ] ℂ) (Λ : ℕ → Submodule ℤ V) (emb : ℕ → E →+ V)
    (dmap : ℕ → E → V) : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ D.r + 1 → ∀ (w : W) (Y : Finset (TB.Pt E)),
    (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
    ∃ (φ : V → ℝ) (Cφ : ℝ), Continuous φ ∧ (∀ c, |φ c| ≤ Cφ * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) ∧
      (∀ c, 0 ≤ φ c) ∧ (∀ t : E, t ≠ 0 → (D.Nst ε i 1 w Y κ t t).re = φ (emb i t)) ∧
      ∀ l, D.Nhat ε i w Y κ l =
        ((ZLattice.covolume (Λ i) : ℝ) : ℂ)⁻¹ * (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) (dmap i l)
def PoissonStepJoint : Prop :=
  F7.PoissonStepText → PoissonJoint →
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (ι : Type)
    [Fintype ι] (π : ι → V →L[ℝ] ℂ), (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : ℕ → Submodule ℤ V) [∀ i, DiscreteTopology (Λ i)] [∀ i, IsZLattice ℝ (Λ i)]
      (emb : ℕ → E →+ V) (dmap : ℕ → E → V),
      Frames D.r (fun i => D.La i 1) D.Lad Λ emb dmap → WaveFn D π Λ emb dmap → D.PoissonStep
def WaveFnTA {E : Type} [Field E] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} (Φ : W → TA.Pt E → H)
    (tr : W → Finset (TA.Pt E) → (TA.Pt E → TA.Pt E → ℂ) → E → ℂ) (i : ℕ) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (Λ : Submodule ℤ V)
    (emb : E →+ V) (dmap : E → V) : Prop :=
  ∀ (w : W) (Hd : Finset (TA.Pt E)) (kap : TA.Pt E → TA.Pt E → ℂ), (∀ h ∈ Hd, TA.IsPt (i - 1) h) →
    TA.PSDOn Hd kap →
    ∃ (φ : V → ℝ) (Cφ : ℝ), Continuous φ ∧ (∀ c, |φ c| ≤ Cφ * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) ∧
      (∀ c, 0 ≤ φ c) ∧ (∀ t : E, t ≠ 0 → (TA.Nst (Φ w) Hd kap 1 t t).re = φ (emb t)) ∧
      ∀ l, tr w Hd kap l =
        ((ZLattice.covolume Λ : ℝ) : ℂ)⁻¹ * (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) (dmap l)
def PoissonJointTA : Prop :=
  F7.PoissonStepText → PoissonJoint →
  ∀ (E : Type) [Field E] [DecidableEq E] (D : TA.Data E) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : Type) [Fintype W] (Φ : W → TA.Pt E → H)
    (tr : W → Finset (TA.Pt E) → (TA.Pt E → TA.Pt E → ℂ) → E → ℂ) (i : ℕ) (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (π : ι → V →L[ℝ] ℂ),
    (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (emb : E →+ V) (dmap : E → V),
      Function.Injective emb → (∀ t ∈ D.La i 1, emb t ∈ Λ) → dmap 0 = 0 →
      (∀ μ ∈ dual Λ, ∃ l ∈ D.Lv i, dmap l = μ) → WaveFnTA Φ tr i π Λ emb dmap →
      TA.Poisson D Φ tr i
def PoissonAgree : Prop :=
  PSDAgree → PSDTranspose →
  ∀ (E W : Type) [Field E] [DecidableEq E] [Fintype W] (D : TB.Data E W) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : W → TA.Pt E → H) (ε : ℝ) (i : ℕ),
    0 < ε → 1 ≤ i → i ≤ D.r + 1 → (∀ w, D.wt w ≠ 0) →
    (∀ w p q, D.gram ε i w p q = (D.wt w : ℂ) * inner ℂ (Φ w q) (Φ w p)) → D.PoissonStep →
    TA.Poisson (toTA D) Φ (fun w Hd kap => D.Nhat ε i w Hd (fun h h' => kap h' h)) i
def BlockPoissonFrame : Prop :=
  EmbFacts → TraceDual → S6.TwIsFLattice → S6.PowConjStable →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g r : ℕ), 0 < g →
      Frames r (fun i => LaB E g r i 1) (fun i => LadB E g r i)
        (fun i => eLat E (S6.perLat E g (S6.nuBlock r i 1) 1) (S6.rd E ^ (-(S6.nuBlock r i 1))))
        (fun i => semb E (S6.rd E ^ (-(S6.nuBlock r i 1))))
        (fun i => dm E g (S6.rd E ^ (-(S6.nuBlock r i 1))))
end Poisson
def XIsLamOne : Prop :=
  ∀ (m i : ℕ) (C ka N I A g B : ℝ),
    Sz.xThreshold m i C ka N I A = Sz.lamThreshold m i 1 C ka N I A ∧
      Sz.xHat i C ka N I g B = Sz.lamHat i 1 C ka N I g B
def FrameProducts : Prop :=
  ∀ (r i s : ℕ) (C rd g N I A TT : ℝ), 1 ≤ i → 1 ≤ s → 0 < rd → 0 < g →
    Sz.lamThreshold (2 * r + 2) i s C (2 * Real.pi / g) N I A * (g * rd ^ (S6.nuBlock r i s + 1)) =
      Sz.lamHat i s C (2 * Real.pi / rd) N I g
        (g ^ (2 * r + 2) * (((2 * Real.pi / rd) ^ (2 * r + 2 - 1))⁻¹ * A)) ∧
    √(Sz.lamPrimeSq (2 * r + 2) i C (2 * Real.pi / g) N I A TT) *
        (g * rd ^ (S6.nuBlock r i ((r : ℤ) + 2 - i))) =
      Sz.lamPrimeHat i C (2 * Real.pi / rd) N I g
        (g ^ (2 * r + 2) * (((2 * Real.pi / rd) ^ (2 * r + 2 - 1))⁻¹ * A)) TT
section TransportedAlt
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
def supA (one : Bool) (w : ι) : ℝ :=
  (if one then G.cutSupLong de de' T T' l w else G.supI de de' T T' l w) /
    (G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹)
def thrS (b s : ℕ) (w : ι) : ℝ :=
  Sz.lamThreshold G.m b s C (2 * Real.pi / G.g) G.N G.lenI
    (supA G de de' T T' l (decide (b = 1 ∧ s = 1)) w)
def thrP (b : ℕ) (w : ι) : ℝ :=
  √(Sz.lamPrimeSq G.m b C (2 * Real.pi / G.g) G.N G.lenI (supA G de de' T T' l false w) (T * T'))
end TransportedAlt
def SupAIsCore : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι),
    0 < G.g → 0 < G.ka →
    supA G de de' T T' l false w =
      sSup ((fun Y => (G.place w).core de de' T T' Y) '' (G.place w).cutI l) ∧
    supA G de de' T T' l true w =
      sSup ((fun Y => (G.place w).core de de' T T' Y) '' (G.place w).cutIntervalLong l G.N)
def ThresholdsMonotone : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C C' : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ),
    0 ≤ C → C ≤ C' → 0 < G.g → 0 < G.v → 0 < G.lenI → ∀ (b s : ℕ) (w : ι),
    0 ≤ thrS G C de de' T T' l b s w ∧ thrS G C de de' T T' l b s w ≤ thrS G C' de de' T T' l b s w ∧
    0 ≤ thrP G C de de' T T' l b w ∧ thrP G C de de' T T' l b w ≤ thrP G C' de de' T T' l b w
def Inst {E W : Type} [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
    (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ)
    (T T' : ℝ) (l : ℕ) : Prop :=
  D.r = G.r ∧ D.K = 5 ∧ PlacesOf D e ∧ G.v = S6.rd E / 2 ∧
  (∀ b s, D.La b s = LaB E (G.g1 * G.g2) G.r b s) ∧
  (∀ b s, D.Lap b s = LapB E (G.g1 * G.g2) G.r b s) ∧
  (∀ b, D.Lad b = LadB E (G.g1 * G.g2) G.r b) ∧
  (∀ b v, D.szD b v = thrS G C de de' T T' l b 1 (e v)) ∧
  (∀ b s v, D.szL b s v =
    if b + s ≤ G.r + 1 then thrS G C de de' T T' l b (s + 1) (e v)
    else 2 * thrP G C de de' T T' l b (e v)) ∧
  (∀ b s, D.vol b s = (∏ w, thrS G C de de' T T' l b s w) ^ 2 /
    (FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ))
def InstSizes : Prop :=
  S6.LatticesGeneral → S6.IdealsMatch → S6.NormIdl → S6.DegreeFacts → FrameProducts → XIsLamOne →
    ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ)
      (T T' : ℝ) (l : ℕ) (Θ : ℝ),
      S6.Unram E → Inst D e G C de de' T T' l → 0 < G.g1 → 0 < G.g2 → 0 ≤ C → 0 < G.lenI → 0 < Θ →
      IsGreatest (G.thrSet C de de' T T' l) ((Θ ^ G.f)⁻¹) →
      D.SizesBelow Θ ∧
      IdealSizes D (fun i => S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r i 1))
        (fun b s => S6.liftIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) Θ 2 ∧
      (D.Ntop : ℝ) = G.N
def InstLatticeSums : Prop :=
  LatticeSumsJoint → InstSizes →
  Formalism.SA.C.BoxSum → S6.LatticesGeneral → S6.IdealsMatch → S6.NormIdl → S6.DegreeFacts → FrameProducts →
    XIsLamOne → ∃ C₁ : ℝ, 1 ≤ C₁ ∧
    ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ)
      (T T' : ℝ) (l : ℕ) (Θ : ℝ),
      S6.Unram E → Inst D e G C de de' T T' l → 0 < G.g1 → 0 < G.g2 → 0 ≤ C → 0 < G.lenI → 4 < Θ →
      IsGreatest (G.thrSet C de de' T T' l) ((Θ ^ G.f)⁻¹) →
      D.SizesBelow Θ ∧ D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f)
def SzHyp {ι : Type} [Fintype ι] (G : Sz.Glob ι) (CA C0 CG CDel cT Cb bb C' Th : ℝ)
    (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ) : Prop :=
  G.Hyp bb CDel Cb ∧ Sz.IsWord G.k de ∧ Sz.IsWord G.k de' ∧ 1 ≤ l ∧ l + 2 ≤ G.k ∧ de l ≠ de' l ∧
  bb ^ (cT * G.m) ≤ T ∧ bb ^ (cT * G.m) ≤ T' ∧
  8 * CG ≤ C' ∧ C' * (G.m : ℝ) ^ 5 * G.f * Real.log bb ≤ G.k ∧
  (G.size de T du).MassRatios ∧ (G.size de T du).LBound ∧
  (G.size de T du).ColumnCount ∧ (G.size de' T' du').ColumnCount ∧
  (G.size de T du).ChoiceOfT C0 (Real.exp (CG * (G.m : ℝ) ^ 5 * G.f * Real.log bb)) ∧
  (G.size de' T' du').ChoiceOfT C0 (Real.exp (CG * (G.m : ℝ) ^ 5 * G.f * Real.log bb)) ∧
  (∀ w, Sz.FormalDegreeLower (G.place w) (1 / 2) ((G.size de T du).VV w)) ∧
  0 < Th ∧ IsGreatest (G.thrSet CA de de' T T' l) ((Th ^ G.f)⁻¹)
def SizesToRecursion : Prop :=
  Sz.SizesMain →
  ∀ (CA C0 CG CDel cT Cb C C' : ℝ), 1 ≤ CA → 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb →
    1 < cT * Cb → 0 ≤ C → C ≤ CA →
    ∃ k0 : ℕ, ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (bb Cp Cf Th : ℝ) (de de' : ℕ → ℝ) (T T' : ℕ)
      (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      C' ≤ Th ∧ 4 < Th ∧ (G.r : ℝ) * (C / Th) ^ G.f ≤ 1 ∧ ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ 1 ∧
        C * ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ (bb ^ 7)⁻¹
def GlobPositive : Prop :=
  ∀ CDel Cb : ℝ, 4 < CDel → 0 < Cb → ∃ k0 : ℕ, ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (bb : ℝ),
    k0 ≤ G.k → G.Hyp bb CDel Cb → 0 < G.g1 ∧ 0 < G.g2 ∧ 0 < G.lenI
def MajMono : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (ρ ρ' : Fin D.f → ℝ) (l : E),
    (∀ v, 0 ≤ ρ v ∧ ρ v ≤ ρ' v) → (∀ v, 0 ≤ D.av v l) → D.maj ρ l ≤ D.maj ρ' l
def withSizes {E W : Type} [Field E] (D : TB.Data E W) (szD' : ℕ → Fin D.f → ℝ)
    (szL' : ℕ → ℕ → Fin D.f → ℝ) (vol' : ℕ → ℕ → ℝ) : TB.Data E W :=
  { D with szD := szD', szL := szL', vol := vol' }
def EstimatesMono : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (szD' : ℕ → Fin D.f → ℝ) (szL' : ℕ → ℕ → Fin D.f → ℝ)
    (vol' : ℕ → ℕ → ℝ) (C₄ : ℝ), 0 ≤ C₄ → (∀ v l, 0 ≤ D.av v l) →
    (∀ i v, 0 ≤ D.szD i v ∧ D.szD i v ≤ szD' i v) → (∀ b s v, 0 ≤ D.szL b s v ∧ D.szL b s v ≤ szL' b s v) →
    (∀ b s, 0 ≤ D.vol b s ∧ D.vol b s ≤ vol' b s) → D.GramPSD → D.WordsPos →
    (D.EstWave → (withSizes D szD' szL' vol').EstWave) ∧
    (D.EstLift → (withSizes D szD' szL' vol').EstLift) ∧
    (D.EstBlock C₄ → (withSizes D szD' szL' vol').EstBlock C₄)
def RecHyp {E W : Type} [Field E] (D : TB.Data E W) (C₁ C₄ Θ jn : ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) : Prop :=
  4 ≤ D.K ∧ 1 ≤ D.f ∧ 0 < Θ ∧ D.SizesBelow Θ ∧ D.GramPSD ∧ D.KernelPSD ∧ D.WordsPos ∧ D.KernelSupport ∧
  D.ThetaDomination ∧ D.EstWave ∧ D.PoissonStep ∧ D.EstLift ∧ D.EstBlock C₄ ∧
  D.LatticeSums ((C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) ∧ D.EstE jn ∧ D.Cutoff Vt ∧ D.LeadingDomination Vt c
def RecursionGivesBounds : Prop :=
  TB.TheoremA → ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
    ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
      RecHyp D C₁ C₄ Θ jn Vt c → C' ≤ Θ → (D.r : ℝ) * (C / Θ) ^ D.f ≤ 1 →
      (∀ i ∈ Icc 1 (D.r + 1), D.e i = 0) →
      ∀ (P : Type) [Fintype P] (B : S3.MassData P), B.IntN = jn →
        B.δ = C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f →
        (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) → B.Smod ≤ M) →
        B.InTheoremA
def RecursionGivesForm : Prop :=
  TB.TheoremA → ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
    ∀ (E W : Type) [Field E] (D : TB.Data E W) (Θ jn : ℝ) (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
      RecHyp D C₁ C₄ Θ jn Vt c → C' ≤ Θ → (D.r : ℝ) * (C / Θ) ^ D.f ≤ 1 →
      (∀ i ∈ Icc 1 D.r, D.e i = 0) →
      ∀ (P : Type) [Fintype P] (B : S3.MassData P), 1 + D.e (D.r + 1) = B.e1 → B.IntN = jn →
        B.δ = C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f →
        (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) →
          B.c0 * B.c0' * B.KV ≤ B.n0c * M) →
        B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN)
def ProductOfE : Prop :=
  ∀ (r : ℕ) (e : ℕ → ℝ) (sd : ℝ), (∀ i ∈ Icc 1 r, e i = 0) → 1 + e (r + 1) = sd →
    ∏ i ∈ Icc 1 (r + 1), (1 + e i) = sd
def TopE : Prop :=
  ∀ sd e : ℝ, 1 + e = max sd 1 → sd ≤ 2 → 0 ≤ e ∧ e ≤ 1 ∧ sd ≤ 1 + e
def OnceOnly : Prop :=
  ∀ (P : Type) [Fintype P] (B : S3.MassData P), B.Pos → B.InKernel → B.InTheoremA →
    B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.supdens * (B.n0c * B.IntN)
def FormGivesMain : Prop :=
  S3.MainTheorem → ∀ (P : Type) [Fintype P] (B : S3.MassData P), B.Pos → 0 < B.e1 → 0 ≤ B.KV → B.InTwoA →
    B.InForm → B.InMass → B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN) →
    B.InJacMod → B.InNu → B.InInfinity → B.InVolumes → B.InLevelS → B.InMasses → B.InColumns →
    B.InOrdinary → B.InTyped → B.InIndices →
    B.GS = B.tt * B.Gam1 * B.Sig ∧
    B.GS ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) ∧
    B.Kgs2 ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar)
def MainJoint : Prop :=
  TB.TheoremA → Sz.SizesMain → ∀ C₁ C₄ Cthr : ℝ, 1 ≤ C₁ → 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (bb Cp Cf Th : ℝ) (de de' : ℕ → ℝ) (T T' : ℕ)
      (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      ∀ (E W : Type) [Field E] (D : TB.Data E W) (jn : ℝ) (H : Type) [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
        D.r = G.r → D.f = G.f → RecHyp D C₁ C₄ Th jn Vt c → (∀ i ∈ Icc 1 (D.r + 1), D.e i = 0) →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), B.IntN = jn →
          B.δ = C * ((D.r : ℝ) + 1) * (C / Th) ^ D.f →
          (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) → B.Smod ≤ M) →
          B.InTheoremA ∧ B.δ ≤ (bb ^ 7)⁻¹
def MainJointForm : Prop :=
  TB.TheoremA → Sz.SizesMain → ∀ C₁ C₄ Cthr : ℝ, 1 ≤ C₁ → 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (bb Cp Cf Th : ℝ) (de de' : ℕ → ℝ) (T T' : ℕ)
      (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      ∀ (E W : Type) [Field E] (D : TB.Data E W) (jn : ℝ) (H : Type) [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
        D.r = G.r → D.f = G.f → RecHyp D C₁ C₄ Th jn Vt c → (∀ i ∈ Icc 1 D.r, D.e i = 0) →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), 1 + D.e (D.r + 1) = B.e1 → B.IntN = jn →
          B.δ = C * ((D.r : ℝ) + 1) * (C / Th) ^ D.f →
          (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) →
            B.c0 * B.c0' * B.KV ≤ B.n0c * M) →
          B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN) ∧ 0 ≤ B.δ ∧ B.δ ≤ (bb ^ 7)⁻¹
def RecHypInst {E W : Type} [Field E] (D : TB.Data E W) (C₄ jn : ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) : Prop :=
  D.GramPSD ∧ D.KernelPSD ∧ D.WordsPos ∧ D.KernelSupport ∧ D.ThetaDomination ∧ D.EstWave ∧ D.PoissonStep ∧ D.EstLift ∧
  D.EstBlock C₄ ∧ D.EstE jn ∧ D.Cutoff Vt ∧ D.LeadingDomination Vt c
def MainJointInst : Prop :=
  TB.TheoremA → Sz.SizesMain → Formalism.SA.C.BoxSum → S6.LatticesGeneral → S6.IdealsMatch → S6.NormIdl →
    S6.DegreeFacts → ∀ C₄ Cthr : ℝ, 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (bb Cp Cf Th : ℝ)
      (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      S6.Unram E → Inst D e G CA de de' T T' l →
      ∀ (jn : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ),
        RecHypInst D C₄ jn Vt c → (∀ i ∈ Icc 1 D.r, D.e i = 0) →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), 1 + D.e (D.r + 1) = B.e1 → B.IntN = jn →
          B.δ = C * ((D.r : ℝ) + 1) * (C / Th) ^ D.f →
          (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) →
            B.c0 * B.c0' * B.KV ≤ B.n0c * M) →
          B.c0 * B.c0' * B.KV ≤ (1 + B.δ) * B.e1 * (B.n0c * B.IntN) ∧ 0 ≤ B.δ ∧ B.δ ≤ (bb ^ 7)⁻¹
structure LocSys (E α : Type) [Field E] where

  N : E → E → α → α → ℂ

  Th : E → α → α → ℂ

  B : α → α → ℂ

  L : AddSubgroup E

  L' : AddSubgroup E
namespace LocSys
variable {E α : Type} [Field E]
def Ok (S : LocSys E α) (F : Finset α) : Prop :=
  (∀ t t' : E, t ≠ 0 → t' ≠ 0 → ∀ h ∈ F, ∀ h' ∈ F, S.N t t' h h' ≠ 0 → t⁻¹ - t'⁻¹ ∈ S.L') ∧
  (∀ t : E, t ≠ 0 → TB.PSDOn F (S.N t t)) ∧
  (∀ t t' : E, t - t' ∈ S.L → ∀ h ∈ F, ∀ h' ∈ F, S.Th t h h' = S.Th t' h h') ∧
  (∀ t : E, TB.PSDOn F (S.Th t)) ∧
  (∀ t : E, t ≠ 0 → TB.PSDOn F (fun h h' => S.Th t h h' - S.N t t h h')) ∧
  (∀ R : Finset E, (∀ t ∈ R, ∀ t' ∈ R, t - t' ∈ S.L → t = t') →
    TB.PSDOn F (fun h h' => S.B h h' - ∑ t ∈ R, S.Th t h h'))
end LocSys
def prodSys {E α P : Type} [Field E] [Fintype P] (S : P → LocSys E α) : LocSys E α where
  N := fun t t' h h' => ∏ p, (S p).N t t' h h'
  Th := fun t h h' => ∏ p, (S p).Th t h h'
  B := fun h h' => ∏ p, (S p).B h h'
  L := ⨅ p, (S p).L
  L' := ⨅ p, (S p).L'
def scaleSys {E α : Type} [Field E] (a : α → ℝ) (S : LocSys E α) : LocSys E α where
  N := fun t t' h h' => (a h : ℂ) * a h' * S.N t t' h h'
  Th := fun t h h' => (a h : ℂ) * a h' * S.Th t h h'
  B := fun h h' => (a h : ℂ) * a h' * S.B h h'
  L := S.L
  L' := S.L'
def phaseSys {E α : Type} [Field E] (d : E → ℂ) (S : LocSys E α) : LocSys E α where
  N := fun t t' h h' => d t * conj (d t') * S.N t t' h h'
  Th := S.Th
  B := S.B
  L := S.L
  L' := S.L'
def SchurProduct : Prop :=
  ∀ (α P : Type) [Fintype P] (F : Finset α) (k : P → α → α → ℂ), (∀ p, TB.PSDOn F (k p)) →
    TB.PSDOn F (fun x y => ∏ p, k p x y)
def ProductDomination : Prop :=
  ∀ (α P : Type) [Fintype P] (F : Finset α) (k K : P → α → α → ℂ), (∀ p, TB.PSDOn F (k p)) →
    (∀ p, TB.PSDOn F (fun x y => K p x y - k p x y)) →
    TB.PSDOn F (fun x y => ∏ p, K p x y - ∏ p, k p x y)
def DiagScale : Prop :=
  ∀ (α : Type) (F : Finset α) (k : α → α → ℂ) (a : α → ℝ), TB.PSDOn F k →
    TB.PSDOn F (fun x y => (a x : ℂ) * a y * k x y)
def ProductLemma : Prop :=
  ∀ (E α P : Type) [Field E] [Fintype P] (S : P → LocSys E α) (F : Finset α),
    (∀ p, (S p).Ok F) → (prodSys S).Ok F
def ScaleOk : Prop :=
  ∀ (E α : Type) [Field E] (a : α → ℝ) (S : LocSys E α) (F : Finset α), S.Ok F → (scaleSys a S).Ok F
def PhaseOk : Prop :=
  ∀ (E α : Type) [Field E] (d : E → ℂ) (S : LocSys E α) (F : Finset α), (∀ t, ‖d t‖ = 1) → S.Ok F →
    (phaseSys d S).Ok F
open Classical in

def OutsideOk : Prop :=
  ∀ (E α : Type) [Field E] (L : AddSubgroup E) (F : Finset α),
    (∀ t t' : E, t - t' ∈ L → (if t ∈ L then (1 : ℂ) else 0) = if t' ∈ L then 1 else 0) ∧
    (∀ t : E, TB.PSDOn F (fun _ _ : α => if t ∈ L then (1 : ℂ) else 0)) ∧
    (∀ R : Finset E, (∀ t ∈ R, ∀ t' ∈ R, t - t' ∈ L → t = t') →
      TB.PSDOn F (fun _ _ : α => (1 : ℂ) - ∑ t ∈ R, if t ∈ L then (1 : ℂ) else 0))
open Classical in

def OutsideSysOk : Prop :=
  ∀ (E α : Type) [Field E] (N : E → E → α → α → ℂ) (L L' : AddSubgroup E) (F : Finset α),
    (∀ t t' : E, t ≠ 0 → t' ≠ 0 → ∀ h ∈ F, ∀ h' ∈ F, N t t' h h' ≠ 0 → t⁻¹ - t'⁻¹ ∈ L') →
    (∀ t : E, t ≠ 0 → TB.PSDOn F (N t t)) →
    (∀ t : E, t ≠ 0 → TB.PSDOn F (fun h h' => (if t ∈ L then (1 : ℂ) else 0) - N t t h h')) →
    (LocSys.mk N (fun t _ _ => if t ∈ L then 1 else 0) (fun _ _ => 1) L L').Ok F
open Classical in

def OutsideDomination : Prop :=
  ProductDomination →
  ∀ (E α P : Type) [Field E] [Fintype P] (k : P → α → α → ℂ) (L : P → AddSubgroup E) (t : E)
    (F : Finset α), (∀ p, TB.PSDOn F (k p)) →
    (∀ p, TB.PSDOn F (fun h h' => (if t ∈ L p then (1 : ℂ) else 0) - k p h h')) →
    TB.PSDOn F (fun h h' => (if t ∈ ⨅ p, L p then (1 : ℂ) else 0) - ∏ p, k p h h')
def UniformMajorant : Prop :=
  ∀ (E α : Type) [Field E] (N : E → E → α → α → ℂ) (B : α → α → ℂ) (L L' : AddSubgroup E),
    (∀ F : Finset α, ∃ Th, (LocSys.mk N Th B L L').Ok F) →
    ∃ Th, ∀ F : Finset α, (LocSys.mk N Th B L L').Ok F
def UniformMajorantOn : Prop :=
  ∀ (E α : Type) [Field E] (A : Set α) (N : E → E → α → α → ℂ) (B : α → α → ℂ) (L L' : AddSubgroup E),
    (∀ F : Finset α, (∀ h ∈ F, h ∈ A) → ∃ Th, (LocSys.mk N Th B L L').Ok F) →
    ∃ Th, (∀ F : Finset α, (∀ h ∈ F, h ∈ A) → (LocSys.mk N Th B L L').Ok F) ∧
      (∀ t h h', ¬ (h ∈ A ∧ h' ∈ A) → Th t h h' = 0) ∧ ∀ t (F : Finset α), TB.PSDOn F (Th t)
open Classical in

def pullSys {E α K : Type} [Field E] [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (s : ℕ)
    (σ : E →+* K) (u : Kˣ) (η : α → A5.Point K) (Θ : K → A5.Point K → A5.Point K → ℂ) :
    LocSys E α where
  N := fun t t' h h' =>
    if ht : t ≠ 0 ∧ t' ≠ 0 then
      A5.Ns R ψ s (η h) (η h') (u * Units.map (σ : E →* K) (Units.mk0 t ht.1))
        (u * Units.map (σ : E →* K) (Units.mk0 t' ht.2))
    else 0
  Th := fun t h h' => Θ ((u : K) * σ t) (η h) (η h')
  B := fun h h' =>
    ((A5.cSize R (η h) ^ s * A5.cSize R (η h') ^ s : ℝ) : ℂ) * A5.N0 R ψ (η h) (η h')
  L := R.toAddSubgroup.comap ((AddMonoidHom.mulLeft (u : K)).comp σ.toAddMonoidHom)
  L' := R.toAddSubgroup.comap ((AddMonoidHom.mulLeft ((u⁻¹ : Kˣ) : K)).comp σ.toAddMonoidHom)
open Classical in

def LocalPullback : Prop :=
  PSDAgree → A5.A2 →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), A5.LocalDatum K R ψ →
    ∀ (E α : Type) [Field E] (s m : ℕ) (σ : E →+* K) (u : Kˣ) (η : α → A5.Point K) (F : Finset α)
      (Θ : K → A5.Point K → A5.Point K → ℂ),
      1 ≤ s → (∀ h ∈ F, (η h).1.sum = m) → A5.ThetaProps R ψ s (F.image η) Θ →
      (pullSys R ψ s σ u η Θ).Ok F
open Classical in

def LocalUnitHeads : Prop :=
  PSDAgree → A5.BaseKernelOne →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), A5.LocalDatum K R ψ →
    ∀ (E α : Type) [Field E] (s m : ℕ) (σ : E →+* K) (u : Kˣ) (η : α → A5.Point K) (F : Finset α)
      (Θ : K → A5.Point K → A5.Point K → ℂ),
      (∀ h ∈ F, (η h).1.sum = m) → (∀ h ∈ F, A5.InGLR R (η h)) → A5.ThetaProps R ψ s (F.image η) Θ →
      ∀ t : E, t ≠ 0 → TB.PSDOn F (fun h h' =>
        (if t ∈ (pullSys R ψ s σ u η Θ).L then (1 : ℂ) else 0) - (pullSys R ψ s σ u η Θ).N t t h h')
open Classical in

def topSys {E α K : Type} [Field E] [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (σ : E →+* K)
    (u : Kˣ) (τ₀ : K) (η : α → A5.Point K) (Θ : K → A5.Point K → A5.Point K → ℂ) : LocSys E α where
  N := fun t t' h h' => if t = t' then Θ ((u : K) * σ t - τ₀) (η h) (η h') else 0
  Th := fun t h h' => Θ ((u : K) * σ t - τ₀) (η h) (η h')
  B := fun h h' => ((A5.cSize R (η h) ^ 1 * A5.cSize R (η h') ^ 1 : ℝ) : ℂ) * A5.N0 R ψ (η h) (η h')
  L := R.toAddSubgroup.comap ((AddMonoidHom.mulLeft (u : K)).comp σ.toAddMonoidHom)
  L' := ⊥
open Classical in

def TopPullback : Prop :=
  PSDAgree →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), A5.LocalDatum K R ψ →
    ∀ (E α : Type) [Field E] (σ : E →+* K) (u : Kˣ) (τ₀ : K) (η : α → A5.Point K) (F : Finset α)
      (Θ : K → A5.Point K → A5.Point K → ℂ),
      A5.ThetaProps R ψ 1 (F.image η) Θ → (topSys R ψ σ u τ₀ η Θ).Ok F
def sysOf {E W : Type} [Field E] (D : TB.Data E W) (i s : ℕ) : LocSys E (TB.Pt E) where
  N := fun t t' h h' => D.Kr i (TB.join h s t) (TB.join h' s t')
  Th := D.Th i s
  B := fun h h' => (1 + (D.e i : ℂ)) * D.Kr (i - s) h h'
  L := D.La (i - s + 1) s
  L' := D.Lap (i - s + 1) s
def AxiomsFromSystems : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W),
    (∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) →
      (sysOf D i s).Ok Y) →
    (∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1) →
    (∀ i s t h h', ¬ (TB.level h = i - s ∧ TB.level h' = i - s) → D.Th i s t h h' = 0) →
    (∀ (h h' : TB.Pt E) (t t' : E), TB.level h = D.r → TB.level h' = D.r → t ≠ 0 → t' ≠ 0 → t ≠ t' →
      D.Kr (D.r + 1) (TB.join h 1 t) (TB.join h' 1 t') = 0) →
    D.KernelSupport ∧ D.ThetaDomination
def GlobalOfLocal : Prop :=
  ProductLemma → ScaleOk →
  ∀ (E W P : Type) [Field E] [Fintype P] (D : TB.Data E W) (i s : ℕ) (S : P → LocSys E (TB.Pt E))
    (a : TB.Pt E → ℝ) (Y : Finset (TB.Pt E)),
    (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
      (sysOf D i s).N t t' h h' = (scaleSys a (prodSys S)).N t t' h h') →
    (∀ h ∈ Y, ∀ h' ∈ Y, (sysOf D i s).B h h' = (scaleSys a (prodSys S)).B h h') →
    (sysOf D i s).L = ⨅ p, (S p).L → (⨅ p, (S p).L') ≤ (sysOf D i s).L' → (∀ p, (S p).Ok Y) →
    ∃ Th, (LocSys.mk (sysOf D i s).N Th (sysOf D i s).B (sysOf D i s).L (sysOf D i s).L').Ok Y
def withTh {E W : Type} [Field E] (D : TB.Data E W)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) : TB.Data E W :=
  { D with Th := Th }
def AxiomsFromFamilies : Prop :=
  UniformMajorantOn → AxiomsFromSystems →
  ∀ (E W : Type) [Field E] (D : TB.Data E W),
    (∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) →
      ∃ Th, (LocSys.mk (sysOf D i s).N Th (sysOf D i s).B (sysOf D i s).L (sysOf D i s).L').Ok Y) →
    (∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1) →
    (∀ (h h' : TB.Pt E) (t t' : E), TB.level h = D.r → TB.level h' = D.r → t ≠ 0 → t' ≠ 0 → t ≠ t' →
      D.Kr (D.r + 1) (TB.join h 1 t) (TB.join h' 1 t') = 0) →
    ∃ Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ, (withTh D Th).KernelSupport ∧ (withTh D Th).ThetaDomination ∧
      ∀ i s t (Y : Finset (TB.Pt E)), TB.PSDOn Y (Th i s t)
def KernelOfLocal : Prop :=
  SchurProduct → DiagScale →
  ∀ (α P : Type) [Fintype P] (Y : Finset α) (K : α → α → ℂ) (k : P → α → α → ℂ) (a : α → ℝ),
    (∀ x ∈ Y, ∀ y ∈ Y, K x y = (a x : ℂ) * a y * ∏ p, k p x y) → (∀ p, TB.PSDOn Y (k p)) →
    TB.PSDOn Y K
def LocalKernelPSD : Prop :=
  PSDAgree → A5.KpGram →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), A5.LocalDatum K R ψ →
    ∀ (α : Type) (η : α → A5.Point K) (Y : Finset α), TB.PSDOn Y (fun x y => A5.Kp R ψ (η x) (η y))
def IntersectionOfLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E), S6.IsFLattice E L →
    ∀ t : E, t ∈ L ↔ ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L
def LatticeOfLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E), S6.IsFLattice E L →
    ∀ (Q : Type) [Fintype Q] (pl : Q → Set (Ideal (𝓞 (maximalRealSubfield E))))
      (M : Q → AddSubgroup E),
      (∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → ∃ p, P ∈ pl p) →
      (∀ p t, t ∈ M p ↔ ∀ P ∈ pl p, P.IsMaximal → t ∈ S6.locAt E P L) →
      L.toAddSubgroup = ⨅ p, M p
def PullLatticeTyped : Prop :=
  S6.TypedModel →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    S6.PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ S6.locAt E P (S6.zsub E 1) ↔ σ x ∈ o ∧ σ (IsCMField.complexConj E x) ∈ o) →
      ∀ (R : Subring (K × K)) (u : (K × K)ˣ) (α : Type) (ψ : AddChar (K × K) ℂ)
        (η : α → A5.Point (K × K)) (Θ : K × K → A5.Point (K × K) → A5.Point (K × K) → ℂ),
        (∀ a, a ∈ R ↔ a ∈ Formalism.FourierDecayAlt.I.orderR o (g : K)) →
        (u : K × K) = ((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) →
        ∀ t : E,
          t ∈ (pullSys R ψ s (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) u η Θ).L ↔
            t ∈ S6.locAt E P (S6.perLat E g ν s)
def PullLatticeTypedUnit : Prop :=
  S6.TypedModel →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    S6.PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ S6.locAt E P (S6.zsub E 1) ↔ σ x ∈ o ∧ σ (IsCMField.complexConj E x) ∈ o) →
      ∀ (R : Subring (K × K)) (u c : (K × K)ˣ) (α : Type) (ψ : AddChar (K × K) ℂ)
        (η : α → A5.Point (K × K)) (Θ : K × K → A5.Point (K × K) → A5.Point (K × K) → ℂ),
        (∀ a, a ∈ R ↔ a ∈ Formalism.FourierDecayAlt.I.orderR o (g : K)) →
        (c : K × K) ∈ R → ((c⁻¹ : (K × K)ˣ) : K × K) ∈ R →
        (u : K × K) = (c : K × K) * ((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) →
        ∀ t : E,
          t ∈ (pullSys R ψ s (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) u η Θ).L ↔
            t ∈ S6.locAt E P (S6.perLat E g ν s)
def PullLiftTyped : Prop :=
  S6.TypedModel →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    S6.PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ S6.locAt E P (S6.zsub E 1) ↔ σ x ∈ o ∧ σ (IsCMField.complexConj E x) ∈ o) →
      ∀ (R : Subring (K × K)) (u : (K × K)ˣ) (α : Type) (ψ : AddChar (K × K) ℂ)
        (η : α → A5.Point (K × K)) (Θ : K × K → A5.Point (K × K) → A5.Point (K × K) → ℂ),
        (∀ a, a ∈ R ↔ a ∈ Formalism.FourierDecayAlt.I.orderR o (g : K)) →
        (u : K × K) = ((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) →
        ∀ x : E,
          x ∈ (pullSys R ψ s (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) u η Θ).L' ↔
            x ∈ S6.locAt E P (S6.liftLat E g ν s)
def PullLiftTypedUnit : Prop :=
  S6.TypedModel →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    S6.PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ S6.locAt E P (S6.zsub E 1) ↔ σ x ∈ o ∧ σ (IsCMField.complexConj E x) ∈ o) →
      ∀ (R : Subring (K × K)) (u c : (K × K)ˣ) (α : Type) (ψ : AddChar (K × K) ℂ)
        (η : α → A5.Point (K × K)) (Θ : K × K → A5.Point (K × K) → A5.Point (K × K) → ℂ),
        (∀ a, a ∈ R ↔ a ∈ Formalism.FourierDecayAlt.I.orderR o (g : K)) →
        (c : K × K) ∈ R → ((c⁻¹ : (K × K)ˣ) : K × K) ∈ R →
        (u : K × K) = (c : K × K) * ((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) →
        ∀ x : E,
          x ∈ (pullSys R ψ s (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) u η Θ).L' ↔
            x ∈ S6.locAt E P (S6.liftLat E g ν s)
def TopIsLocalKernel : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (E α : Type) [Field E] (m : ℕ)
    (σ : E →+* K) (u : Kˣ) (τ₀ : K) (η : α → A5.Point K) (Θ : K → A5.Point K → A5.Point K → ℂ),
    (∀ (c : Kˣ) (h h' : A5.Point K), h.1.sum = m → h'.1.sum = m →
      Θ (c : K) h h' = A5.Ns R ψ 1 h h' c c) →
    ∀ (t : E) (c : Kˣ), (c : K) = (u : K) * σ t - τ₀ → ∀ h h', (η h).1.sum = m → (η h').1.sum = m →
      (topSys R ψ σ u τ₀ η Θ).N t t h h' = A5.Ns R ψ 1 (η h) (η h') c c
open Classical in

def TopUnitHeads : Prop :=
  PSDAgree → A5.BaseKernelOne →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), A5.LocalDatum K R ψ →
    ∀ (E α : Type) [Field E] (m : ℕ) (σ : E →+* K) (u : Kˣ) (τ₀ : K) (η : α → A5.Point K)
      (F : Finset α) (Θ : K → A5.Point K → A5.Point K → ℂ),
      (∀ h ∈ F, (η h).1.sum = m) → (∀ h ∈ F, A5.InGLR R (η h)) → τ₀ ∈ R →
      A5.ThetaProps R ψ 1 (F.image η) Θ →
      ∀ t : E, TB.PSDOn F (fun h h' =>
        (if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) - (topSys R ψ σ u τ₀ η Θ).N t t h h')
def DiagPhase : Prop :=
  ∀ (α : Type) (F : Finset α) (k : α → α → ℂ) (d : α → ℂ), TB.PSDOn F k →
    TB.PSDOn F (fun x y => d x * conj (d y) * k x y)
def BlockDiagPSD : Prop :=
  ∀ (α β : Type) [DecidableEq β] (F : Finset α) (c : α → β) (k : α → α → ℂ),
    (∀ b, TB.PSDOn (F.filter fun x => c x = b) k) →
    TB.PSDOn F (fun x y => if c x = c y then k x y else 0)
def MinShape : Prop :=
  ∀ (f K : ℕ) (l x : Fin f → ℝ) (X : ℝ) (M : Finset (Fin f) → ℝ), (∀ v, 0 < l v) → (∀ v, 0 ≤ x v) →
    (∀ A : Finset (Fin f), (∏ v ∈ A, l v ^ K) * X ≤ (∏ v ∈ A, x v ^ K) * M A) →
    X ≤ (∏ v, min 1 ((x v / l v) ^ K)) * M (univ.filter fun v => x v < l v)
def ChebToThreshold : Prop :=
  ∀ (L f d : ℕ) (pl : Fin L → Fin f) (sa al bt : Fin L → ℝ) (κ len : ℝ) (lv be : Fin f → ℝ)
    (X B Mx : ℝ), 0 < κ → 0 < len → (∀ a, bt a - al a = len) →
    (∀ a, sa a = κ ^ (1 - (d : ℤ)) * lv (pl a)) →
    (∏ a, sa a) * X ≤ (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * B →
    B ≤ (∏ a, κ * be (pl a)) * Mx →
    (∏ a, lv (pl a)) * X ≤ (∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ d) * Mx
def ThresholdBelow : Prop :=
  ∀ (m i s : ℕ) (C c c₂ κ N I A : ℝ), 0 < κ → 0 < N → 0 < I → 0 ≤ A → 0 < c → 0 ≤ c₂ → 4 * c ≤ C →
    c₂ / 2 ≤ C →
    (1 / 2) * (c₂ * ((κ ^ (m - 1))⁻¹ * A)) * (4 * κ / (I / (c * N))) ^ (2 * (i - 1) + s - 1) ≤
      Sz.lamThreshold m i s C κ N I A
def ThresholdBelowOne : Prop :=
  ∀ (m : ℕ) (C c₂ κ N I A : ℝ), 0 < κ → 0 ≤ A → c₂ ≤ C →
    c₂ * ((κ ^ (m - 1))⁻¹ * A) ≤ Sz.lamThreshold m 1 1 C κ N I A
def LettersAtPlaces : Prop :=
  ∀ (L f K : ℕ) (pl : Fin L → Fin f) (A : Finset (Fin f)) (φ : Fin f → ℝ),
    (∀ v, (univ.filter fun a => pl a = v).card = if v ∈ A then K else 0) →
    ∏ a, φ (pl a) = ∏ v ∈ A, φ v ^ K
def WaveLetters : Prop :=
  F7.PlaneWaveWordCheb → ChebToThreshold →
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : F7.Sesq M) (n L f : ℕ) (pl : Fin L → Fin f) (dat : Fin L → F7.Dat R)
    (α β : Fin L → ℝ) (X X' : M) (κ len Mx : ℝ) (lv be : Fin f → ℝ),
    1 ≤ n → 0 < κ → 0 < len → (∀ a, β a - α a = len) →
    (∀ a, F7.Shape n (dat a).A (dat a).B ∧ F7.Shape n (dat a).Av (dat a).Bv) →
    (∀ a, ‖(dat a).s‖ = κ ^ (1 - ((2 * n : ℕ) : ℤ)) * lv (pl a)) →
    (∀ j : Fin L → Fin (2 * n + 1),
      ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, Formalism.SA.C.chebPt (α a) (β a) (2 * n) (j a))) 1 1‖ ≤
        (∏ a, κ * be (pl a)) * Mx) →
    (∏ a, lv (pl a)) * ‖Ξ X X'‖ ≤ (∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ (2 * n)) * Mx
def WaveLettersOne : Prop :=
  F7.PlaneWaveWord →
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : F7.Sesq M) (L f : ℕ) (pl : Fin L → Fin f) (dat : Fin L → F7.Dat R)
    (y : Fin L → ℝ) (X X' : M) (κ Mx : ℝ) (lv be : Fin f → ℝ),
    0 < κ → (∀ a, F7.Shape 0 (dat a).A (dat a).B ∧ F7.Shape 0 (dat a).Av (dat a).Bv) →
    (∀ a, ‖(dat a).s‖ = κ * lv (pl a)) →
    ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, y a)) 1 1‖ ≤ (∏ a, κ * be (pl a)) * Mx →
    (∏ a, lv (pl a)) * ‖Ξ X X'‖ ≤ (∏ a, be (pl a)) * Mx
def LiftLetters : Prop :=
  F7.LiftWordCheb → ChebToThreshold →
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : F7.Sesq M) (n s L f : ℕ) (pl : Fin L → Fin f) (dat : Fin L → F7.Dat R)
    (A₀ A₀v : Fin L → Polynomial R) (e t t' : Fin L → ℂ) (α β : Fin L → ℝ) (X X' : M)
    (κ len Mx : ℝ) (ov be : Fin f → ℝ),
    1 ≤ s → 0 < κ → 0 < len → (∀ a, β a - α a = len) →
    (∀ a, (dat a).s = 0) → (∀ a, e a = 1 ∨ e a = -1) → (∀ a, t a ≠ 0 ∧ t' a ≠ 0) →
    (∀ a, (dat a).A.Monic ∧ (dat a).A.natDegree = n + s ∧
      (dat a).Av.Monic ∧ (dat a).Av.natDegree = n + s) →
    (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n ∧ (A₀v a).Monic ∧ (A₀v a).natDegree = n) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (F7.evR (dat a).B Y • Q • X) (Q' • X') =
      Ξ ((e a * (t a)⁻¹) • F7.evR (A₀ a) Y • Q • X) (Q' • X')) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (Q • X) (F7.evR (dat a).Bv Y • Q' • X') =
      Ξ (Q • X) ((e a * (starRingEnd ℂ (t' a))⁻¹) • F7.evR (A₀v a) Y • Q' • X')) →
    (∀ a, ‖1 / t a - 1 / t' a‖ = κ ^ (1 - ((2 * n + s : ℕ) : ℤ)) * ov (pl a)) →
    (∀ j : Fin L → Fin (2 * n + s + 1),
      ‖F7.Fw Ξ X X'
          (List.ofFn fun a => (dat a, Formalism.SA.C.chebPt (α a) (β a) (2 * n + s) (j a))) 1 1‖ ≤
        (∏ a, κ * be (pl a)) * Mx) →
    (∏ a, ov (pl a)) * ‖Ξ X X'‖ ≤ (∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ (2 * n + s)) * Mx
def WaveLettersMix : Prop :=
  F7.PlaneWaveWord → F7.ChebSharp →
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : F7.Sesq M) (n L f : ℕ) (pl : Fin L → Fin f) (dat : Fin L → F7.Dat R)
    (α β : Fin L → ℝ) (X X' : M) (κ len : ℝ) (Mj : (Fin L → Fin (2 * n + 1)) → ℝ) (lv be : Fin f → ℝ),
    1 ≤ n → 0 < κ → 0 < len → (∀ a, β a - α a = len) →
    (∀ a, F7.Shape n (dat a).A (dat a).B ∧ F7.Shape n (dat a).Av (dat a).Bv) →
    (∀ a, ‖(dat a).s‖ = κ ^ (1 - ((2 * n : ℕ) : ℤ)) * lv (pl a)) →
    (∀ j : Fin L → Fin (2 * n + 1),
      ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, Formalism.SA.C.chebPt (α a) (β a) (2 * n) (j a))) 1 1‖ ≤
        (∏ a, κ * be (pl a)) * Mj j) →
    (∀ j, 0 ≤ F7.thGrid (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) j) ∧
    ∑ j, F7.thGrid (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) j = 1 ∧
    (∏ a, lv (pl a)) * ‖Ξ X X'‖ ≤ (∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ (2 * n)) *
      ∑ j, F7.thGrid (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) j * Mj j
def LiftLettersMix : Prop :=
  F7.LiftWord → F7.ChebSharp →
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : F7.Sesq M) (n s L f : ℕ) (pl : Fin L → Fin f) (dat : Fin L → F7.Dat R)
    (A₀ A₀v : Fin L → Polynomial R) (e t t' : Fin L → ℂ) (α β : Fin L → ℝ) (X X' : M)
    (κ len : ℝ) (Mj : (Fin L → Fin (2 * n + s + 1)) → ℝ) (ov be : Fin f → ℝ),
    1 ≤ s → 0 < κ → 0 < len → (∀ a, β a - α a = len) →
    (∀ a, (dat a).s = 0) → (∀ a, e a = 1 ∨ e a = -1) → (∀ a, t a ≠ 0 ∧ t' a ≠ 0) →
    (∀ a, (dat a).A.Monic ∧ (dat a).A.natDegree = n + s ∧
      (dat a).Av.Monic ∧ (dat a).Av.natDegree = n + s) →
    (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n ∧ (A₀v a).Monic ∧ (A₀v a).natDegree = n) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (F7.evR (dat a).B Y • Q • X) (Q' • X') =
      Ξ ((e a * (t a)⁻¹) • F7.evR (A₀ a) Y • Q • X) (Q' • X')) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (Q • X) (F7.evR (dat a).Bv Y • Q' • X') =
      Ξ (Q • X) ((e a * (starRingEnd ℂ (t' a))⁻¹) • F7.evR (A₀v a) Y • Q' • X')) →
    (∀ a, ‖1 / t a - 1 / t' a‖ = κ ^ (1 - ((2 * n + s : ℕ) : ℤ)) * ov (pl a)) →
    (∀ j : Fin L → Fin (2 * n + s + 1),
      ‖F7.Fw Ξ X X'
          (List.ofFn fun a => (dat a, Formalism.SA.C.chebPt (α a) (β a) (2 * n + s) (j a))) 1 1‖ ≤
        (∏ a, κ * be (pl a)) * Mj j) →
    (∀ j, 0 ≤ F7.thGrid (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) j) ∧
    ∑ j, F7.thGrid (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) j = 1 ∧
    (∏ a, ov (pl a)) * ‖Ξ X X'‖ ≤ (∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ (2 * n + s)) *
      ∑ j, F7.thGrid (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) j * Mj j
end
end Formalism.FourierDecayAlt.J


