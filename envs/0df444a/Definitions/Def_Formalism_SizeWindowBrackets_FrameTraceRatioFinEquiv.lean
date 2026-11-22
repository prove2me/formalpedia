-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
-- name    : Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:23.536732+00:00
-- url     : https://prove2.me/theorems/9d55e03e-ce58-4791-8c39-dc090303464b
-- title:
--   Frame Trace Ratio Fin Equiv
-- statement:
--   Definitions and structural lemmas for Frame Trace Ratio Fin Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_SlopeExcessBoundExponentZero
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
def KpG {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i j : I) :
    Matrix (ι i) (ι j) ℂ :=
  ((Real.sqrt (ga i * ga j) : ℝ) : ℂ) • ((B i)ᴴ * B j)
def KdG {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I) :
    Matrix (ι i) (ι i) ℂ :=
  KpG B ga i i
def QmG {I α : Type} [Fintype I] {ι : I → Type} [∀ i, Fintype (ι i)] (B : ∀ i, Matrix α (ι i) ℂ)
    (ga : I → ℝ) : Matrix α α ℂ :=
  ∑ i, ((ga i : ℝ) : ℂ) • (B i * (B i)ᴴ)
def RsG {I : Type} [Fintype I] (ι : I → Type) [∀ i, Fintype (ι i)] : ℝ :=
  ∑ i, (Fintype.card (ι i) : ℝ)
def InputSG {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ i j, i ≠ j → hsSq (KpG B ga i j)
      ≤ (1 + η0) * (Fintype.card (ι i) : ℝ) * (Fintype.card (ι j) : ℝ) / Dstar) ∧
  (∀ i, hsSq (KdG B ga i - 1) ≤ e0 * (Fintype.card (ι i) : ℝ)) ∧
  (Fintype.card α : ℝ) ≤ (1 + η1) * Dstar
def toFin {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) :
    ∀ i, Matrix (Fin (Fintype.card α)) (Fin (Fintype.card (ι i))) ℂ :=
  fun i => Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin (ι i)) (B i)
def toFinV {I : Type} {ιf ι : I → Type} [∀ i, Fintype (ιf i)] [∀ i, Fintype (ι i)]
    (V : ∀ i, Matrix (ιf i) (ι i) ℂ) :
    ∀ i, Matrix (Fin (Fintype.card (ιf i))) (Fin (Fintype.card (ι i))) ℂ :=
  fun i => Matrix.reindex (Fintype.equivFin (ιf i)) (Fintype.equivFin (ι i)) (V i)
def FrameDeviationLinear {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (e : ℝ) : Prop :=
  (∑ i, hs2 (frK (ga i) (Matrix.toEuclideanLin (B i)) - LinearMap.id)) ≤
    e * ∑ i, (Fintype.card (ι i) : ℝ)
def FrameTraceRatioLinear {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (η : ℝ) : Prop :=
  (LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)) ∘ₗ
       frQ ga (fun i => Matrix.toEuclideanLin (B i)))).re ≤
    (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)))).re ^ 2 / (Fintype.card α : ℝ)
def LatGeom {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (δ : ℝ) : Prop :=
  (∀ w, IsUnit (X' w).det) ∧ (∀ i w, IsUnit (X i w).det) ∧ (∀ i, IsUnit (Y i).det) ∧
  IsUnit Y'.det ∧
  cc.FG ∧ Submodule.span K (cc : Set W) = ⊤ ∧
  (∀ i, (N i).FG) ∧ (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) ∧
  0 < ∑ i, Fintype.card (ι i) ∧ (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) ∧
  (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) ∧
  0 ≤ δ ∧ δ < 1 ∧ (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) ∧
  (∀ i (k : κ) (j : ι i),
    Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
def LatNum {K W κ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (h : I → ℝ) (s u HH : ℝ) : Prop :=
  s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
    ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) ∧
  0 ≤ u ∧ (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) ∧
  s - muMinDef b' X' cc ≤ HH ∧ 0 ≤ HH
def BridgeHS : Prop :=
  ∀ (I α : Type) [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I), 0 ≤ ga i →
    hs2 (frK (ga i) (Matrix.toEuclideanLin (B i)) - LinearMap.id) = hsSq (KdG B ga i - 1)
def BridgeQ : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] [DecidableEq α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ),
    LinearMap.trace ℂ (EuclideanSpace ℂ α) (frQ ga (fun i => Matrix.toEuclideanLin (B i)))
      = (QmG B ga).trace ∧
    LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)) ∘ₗ
       frQ ga (fun i => Matrix.toEuclideanLin (B i))) = (QmG B ga * QmG B ga).trace
def BridgeFin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ),
    (∀ i j, hsSq (HilbertSchmidtNormSquare.Kp (toFin B) ga i j) = hsSq (KpG B ga i j)) ∧
    (∀ i, hsSq (HilbertSchmidtNormSquare.Kd (toFin B) ga i - 1) = hsSq (KdG B ga i - 1)) ∧
    (HilbertSchmidtNormSquare.Qm (toFin B) ga).trace = (QmG B ga).trace ∧
    (HilbertSchmidtNormSquare.Qm (toFin B) ga * HilbertSchmidtNormSquare.Qm (toFin B) ga).trace = (QmG B ga * QmG B ga).trace ∧
    HilbertSchmidtNormSquare.Rs (fun i => Fintype.card (ι i)) = RsG ι
def BridgeInputS : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar η0 η1 e0 : ℝ),
    HilbertSchmidtNormSquare.InputS (toFin B) ga Dstar η0 η1 e0 ↔ InputSG B ga Dstar η0 η1 e0
def BridgeRam : Prop :=
  ∀ (I α : Type) [Fintype α] (ιf ι : I → Type) [∀ i, Fintype (ιf i)] [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (Bf : ∀ i, Matrix α (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ),
    toFin (fun i => Bf i * Vr i) = HilbertSchmidtNormSquare.Bram (toFin Bf) (toFinV Vr) ∧
    (HilbertSchmidtNormSquare.Isom (toFinV Vr) ↔ ∀ i, (Vr i)ᴴ * Vr i = 1)
def FrameTraceRatioFinEquiv : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (η : ℝ),
    HilbertSchmidtNormSquare.F1 (toFin B) ga η ↔ FrameTraceRatioLinear B ga η
def FrameDeviationFinEquiv : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (e : ℝ), (∀ i, 0 ≤ ga i) →
    (HilbertSchmidtNormSquare.F2 (toFin B) ga e ↔ FrameDeviationLinear B ga e)
def BridgeConcl : Prop :=
  ∀ s mu logI δ u HH η e : ℝ,
    (s - logI - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ mu) ↔
      PhiMonotonicityLemmas.ConclF s mu logI δ u HH η e
def CorLin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar sg η0 η1 e0 : ℝ),
    (∀ i, 0 ≤ ga i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ RsG ι →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputSG B ga Dstar η0 η1 e0 →
    FrameTraceRatioLinear B ga (5 * sg) ∧ FrameDeviationLinear B ga e0 ∧ e0 ≤ 1 / 4 ∧ 0 < ∑ i, Fintype.card (ι i)
def RamLin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ιf ι : I → Type) [∀ i, Fintype (ιf i)]
    [∀ i, DecidableEq (ιf i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (Bf : ∀ i, Matrix α (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ) (ga : I → ℝ)
    (Dstar sg η0 η1 e0 de : ℝ),
    (∀ i, (Vr i)ᴴ * Vr i = 1) → (∀ i, 0 ≤ ga i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 20 →
    Dstar / sg ≤ RsG ιf → -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf ga Dstar η0 η1 e0 →
    FrameTraceRatioLinear (fun i => Bf i * Vr i) ga (5 * sg + 3 * Real.sqrt de) ∧
    FrameDeviationLinear (fun i => Bf i * Vr i) ga (2 * e0) ∧ 2 * e0 ≤ 1 / 4 ∧ 0 < ∑ i, Fintype.card (ι i)
def TheoremFLat : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → FrameDeviationLinear Ball γ e → 0 ≤ e → e ≤ 1 / 4 → FrameTraceRatioLinear Ball γ η → 0 ≤ η →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc
def JointA : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH δ Dstar sg η0 η1 e0 : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ RsG ι →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputSG Ball γ Dstar η0 η1 e0 →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (5 * sg + 4 * Real.sqrt e0) * HH)
      ≤ muDef b' X' cc
def JointARam : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u HH δ Dstar sg η0 η1 e0 de : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc
def JointB : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u U HH δ Dstar sg η0 η1 e0 bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ RsG ι →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 4 * Real.sqrt e0 ≤ sg →
    InputSG Ball γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → u ≤ U → δ ≤ 1 / 7 →
    s ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ)
      + 5 * (c + 1) * Real.log x * (U + bb) + 7 * bb
def JointBRam : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → u ≤ U → δ ≤ 1 / 7 →
    s ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ)
      + 5 * (c + 1) * Real.log x * (U + bb) + 7 * bb
def JointBPow : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → x ^ (-c) ≤ 1 / 20 → Dstar * x ^ c ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ x ^ (-c) / 2 → η1 ≤ x ^ (-c) / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-c) →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ x ^ c * bb → u ≤ U → δ ≤ 1 / 7 →
    s ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ)
      + 5 * (c + 1) * Real.log x * (U + bb) + 7 * bb
def JointBSharp : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u cU Wd HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → u ≤ cU * Wd → bb ≤ Wd → δ ≤ 1 / 7 →
    s ≤ muDef b' X' cc + 5 * (c + 1) * (cU + 1) * Real.log x * Wd + 7 * bb
def JointC : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (muMaxM muM dr BE : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → (∀ i, 0 < Fintype.card (ι i)) →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, 0 ≤ dr i) →
    WeightedMeanLemmas.Slopes2ge (fun i => muMaxDef (b i) (X i) (N i)) (fun i => muDef (b i) (X i) (N i))
      muMaxM muM dr BE Sg0 →
    (∀ i, muMaxM i ≤ A) → (∀ i, -A' ≤ muM i) → (∀ i j, |h i - h j| ≤ Vh) →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → δ ≤ 1 / 7 →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ)
        + 5 * (c + 1) * Real.log x
          * (A + A' + Vh + WeightedMeanLemmas.wmean (fun i => (Fintype.card (ι i) : ℝ)) (fun i => dr i + BE i) + bb)
        + 7 * bb
def JointCSharp : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (muMaxM muM dr BE : I → ℝ) (Sg0 A A' Vh cU Wd HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → (∀ i, 0 < Fintype.card (ι i)) →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, 0 ≤ dr i) →
    WeightedMeanLemmas.Slopes2ge (fun i => muMaxDef (b i) (X i) (N i)) (fun i => muDef (b i) (X i) (N i))
      muMaxM muM dr BE Sg0 →
    (∀ i, muMaxM i ≤ A) → (∀ i, -A' ≤ muM i) → (∀ i j, |h i - h j| ≤ Vh) →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → δ ≤ 1 / 7 →
    A + A' + Vh + WeightedMeanLemmas.wmean (fun i => (Fintype.card (ι i) : ℝ)) (fun i => dr i + BE i) ≤ cU * Wd →
    bb ≤ Wd →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      ≤ muDef b' X' cc + 5 * (c + 1) * (cU + 1) * Real.log x * Wd + 7 * bb
def JointD : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (σ τ : I → slopeLatticeData.FinPl K →₀ ℤ) (M N0 : ∀ i, Submodule (𝓞 K) (V i)) (β : I → slopeLatticeData.FinPl K → ℝ)
    (dr : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → (∀ i, 0 < Fintype.card (ι i)) →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, N i = slopeLatticeData.modLat (σ i) (N0 i)) → (∀ i, (M i).FG) → (∀ i, M i ≠ ⊥) →
    (∀ i, N0 i ≤ Formalism.HermitianLatticesTheory.idealSmul
      ((slopeLatticeData.idealPow (τ i) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M i)) →
    (∀ i, rkK (N0 i) = rkK (M i)) →
    (∀ i (w : slopeLatticeData.FinPl K), ((slopeLatticeData.lenAt w (Formalism.HermitianLatticesTheory.idealSmul
      ((slopeLatticeData.idealPow (τ i) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M i))
        (N0 i)).toNat : ℝ) = (rkK (M i) : ℝ) * β i w) →
    (∀ i, slopeLatticeData.sgSum (σ i) (τ i) = Sg0 - dr i) → (∀ i, 0 ≤ dr i) →
    (∀ i, muMaxDef (b i) (X i) (M i) ≤ A) → (∀ i, -A' ≤ muDef (b i) (X i) (M i)) →
    (∀ i j, |h i - h j| ≤ Vh) →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → δ ≤ 1 / 7 →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ)
        + 5 * (c + 1) * Real.log x
          * (A + A' + Vh + WeightedMeanLemmas.wmean (fun i => (Fintype.card (ι i) : ℝ))
              (fun i => dr i + ∑ᶠ w : slopeLatticeData.FinPl K, 2 * slopeLatticeData.ell w * β i w) + bb)
        + 7 * bb
def JointDSharp : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (σ τ : I → slopeLatticeData.FinPl K →₀ ℤ) (M N0 : ∀ i, Submodule (𝓞 K) (V i)) (β : I → slopeLatticeData.FinPl K → ℝ)
    (dr : I → ℝ) (Sg0 A A' Vh cU Wd HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → (∀ i, 0 < Fintype.card (ι i)) →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, N i = slopeLatticeData.modLat (σ i) (N0 i)) → (∀ i, (M i).FG) → (∀ i, M i ≠ ⊥) →
    (∀ i, N0 i ≤ Formalism.HermitianLatticesTheory.idealSmul
      ((slopeLatticeData.idealPow (τ i) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M i)) →
    (∀ i, rkK (N0 i) = rkK (M i)) →
    (∀ i (w : slopeLatticeData.FinPl K), ((slopeLatticeData.lenAt w (Formalism.HermitianLatticesTheory.idealSmul
      ((slopeLatticeData.idealPow (τ i) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M i))
        (N0 i)).toNat : ℝ) = (rkK (M i) : ℝ) * β i w) →
    (∀ i, slopeLatticeData.sgSum (σ i) (τ i) = Sg0 - dr i) → (∀ i, 0 ≤ dr i) →
    (∀ i, muMaxDef (b i) (X i) (M i) ≤ A) → (∀ i, -A' ≤ muDef (b i) (X i) (M i)) →
    (∀ i j, |h i - h j| ≤ Vh) →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → 0 ≤ de →
    3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    2 ≤ x → 0 ≤ c → 0 < bb → HH ≤ bb / sg → HH ≤ x ^ c * bb → δ ≤ 1 / 7 →
    A + A' + Vh + WeightedMeanLemmas.wmean (fun i => (Fintype.card (ι i) : ℝ))
      (fun i => dr i + ∑ᶠ w : slopeLatticeData.FinPl K, 2 * slopeLatticeData.ell w * β i w) ≤ cU * Wd →
    bb ≤ Wd →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      ≤ muDef b' X' cc + 5 * (c + 1) * (cU + 1) * Real.log x * Wd + 7 * bb
def RamRank : Prop :=
  ∀ (I : Type) [Fintype I] (ιf ι : I → Type) [∀ i, Fintype (ιf i)] [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ),
    (∀ i, (Vr i)ᴴ * Vr i = 1) → (∀ i, Fintype.card (ι i) ≤ Fintype.card (ιf i)) ∧ RsG ι ≤ RsG ιf
def WordsR : Prop :=
  ∀ (I : Type) [Fintype I] (ιf : I → Type) [∀ i, Fintype (ιf i)] (Dstar sg C0 Gam : ℝ),
    0 < Dstar → 0 < sg → 0 < C0 → 0 < Gam → C0 * Gam ^ 2 / sg ≤ (Fintype.card I : ℝ) →
    (∀ i, Dstar * (Gam ^ 2)⁻¹ / C0 ≤ (Fintype.card (ιf i) : ℝ)) → Dstar / sg ≤ RsG ιf
def JointModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v : InfinitePlace K),
    ∃ (h : Fin 20 → ℝ) (s u U HH bb : ℝ),
      LatGeom (κ₁ := Empty) (V := fun _ : Fin 20 => K) (ι := fun _ => Unit)
        (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)})
        (fun _ => Basis.singleton Unit K) (fun _ _ => 1) (fun _ => Submodule.span (𝓞 K) {(1 : K)})
        (fun _ => LinearMap.id) h v (fun _ => 1) 1 (fun _ => Matrix.of fun _ _ => 1) 0 ∧
      LatNum (V := fun _ : Fin 20 => K) (ι := fun _ => Unit)
        (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)})
        (fun _ => Basis.singleton Unit K) (fun _ _ => 1) (fun _ => Submodule.span (𝓞 K) {(1 : K)})
        h s u HH ∧
      (∀ _ : Fin 20, (Matrix.of fun _ _ => 1 : Matrix (Unit ⊕ Empty) Unit ℂ)
        = (Matrix.of fun _ _ => 1 : Matrix (Unit ⊕ Empty) Unit ℂ) * (1 : Matrix Unit Unit ℂ)) ∧
      ((1 : Matrix Unit Unit ℂ)ᴴ * (1 : Matrix Unit Unit ℂ) = 1) ∧
      (1 : ℝ) / (1 / 20) ≤ RsG (fun _ : Fin 20 => Unit) ∧
      3 * Real.sqrt 0 + 4 * Real.sqrt (2 * 0) ≤ (1 / 20 : ℝ) ∧
      ∑ _i : Fin 20, ((Fintype.card Unit : ℝ) - (Fintype.card Unit : ℝ))
        ≤ 0 * RsG (fun _ : Fin 20 => Unit) ∧
      InputSG (I := Fin 20) (ι := fun _ => Unit)
        (fun _ => (Matrix.of fun _ _ => 1 : Matrix (Unit ⊕ Empty) Unit ℂ)) (fun _ => 1) 1 0 0 0 ∧
      0 < bb ∧ HH ≤ bb / (1 / 20) ∧ HH ≤ (2 : ℝ) ^ (0 : ℝ) * bb ∧ u ≤ U
def JointDModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v : InfinitePlace K),
    ∃ (h : Fin 20 → ℝ) (HH bb A A' Vh : ℝ),
      LatGeom (κ₁ := Empty) (V := fun _ : Fin 20 => K) (ι := fun _ => Unit)
        (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)})
        (fun _ => Basis.singleton Unit K) (fun _ _ => 1) (fun _ => (Submodule.span (𝓞 K) {(1 : K)}))
        (fun _ => LinearMap.id) h v (fun _ => 1) 1 (fun _ => Matrix.of fun _ _ => 1) 0 ∧
      WeightedMeanLemmas.sF (fun _ : Fin 20 => (Fintype.card Unit : ℝ))
        (fun _ => muDef (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)})) h
        - muMinDef (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)}) ≤ HH ∧ 0 ≤ HH ∧
      (Submodule.span (𝓞 K) {(1 : K)}) = slopeLatticeData.modLat (0 : slopeLatticeData.FinPl K →₀ ℤ) (Submodule.span (𝓞 K) {(1 : K)}) ∧
      (Submodule.span (𝓞 K) {(1 : K)}).FG ∧ (Submodule.span (𝓞 K) {(1 : K)}) ≠ ⊥ ∧
      (Submodule.span (𝓞 K) {(1 : K)}) ≤ (Formalism.HermitianLatticesTheory.idealSmul
        ((slopeLatticeData.idealPow (0 : slopeLatticeData.FinPl K →₀ ℤ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
          Submodule (𝓞 K) K) (Submodule.span (𝓞 K) {(1 : K)})) ∧
      (∀ w : slopeLatticeData.FinPl K, ((slopeLatticeData.lenAt w (Formalism.HermitianLatticesTheory.idealSmul
        ((slopeLatticeData.idealPow (0 : slopeLatticeData.FinPl K →₀ ℤ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
          Submodule (𝓞 K) K) (Submodule.span (𝓞 K) {(1 : K)}))
        (Submodule.span (𝓞 K) {(1 : K)})).toNat : ℝ) = (rkK (Submodule.span (𝓞 K) {(1 : K)}) : ℝ) * 0) ∧
      slopeLatticeData.sgSum (0 : slopeLatticeData.FinPl K →₀ ℤ) 0 = 0 - 0 ∧
      muMaxDef (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)}) ≤ A ∧
      -A' ≤ muDef (Basis.singleton Unit K) (fun _ => 1) (Submodule.span (𝓞 K) {(1 : K)}) ∧
      (∀ i j, |h i - h j| ≤ Vh) ∧
      0 < bb ∧ HH ≤ bb / (1 / 20) ∧ HH ≤ (2 : ℝ) ^ (0 : ℝ) * bb
def BridgeHSSign : Prop :=
  hs2 (frK (-1 : ℝ) (Matrix.toEuclideanLin (1 : Matrix Unit Unit ℂ)) - LinearMap.id) = 4 ∧
  hsSq (KdG (I := Unit) (ι := fun _ => Unit) (fun _ => (1 : Matrix Unit Unit ℂ)) (fun _ => -1) ()
    - 1) = 0
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates


