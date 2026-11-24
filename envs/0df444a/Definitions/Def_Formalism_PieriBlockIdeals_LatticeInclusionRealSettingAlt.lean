-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
-- name    : Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:19.269081+00:00
-- url     : https://prove2.me/theorems/51826806-e291-4af0-a049-70bb71d1d8cd
-- title:
--   Lattice Inclusion Real Setting Alt
-- statement:
--   Definitions and structural lemmas for Lattice Inclusion Real Setting Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LatticeInclusionRealSettingAlt.lean

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
namespace Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
def cShort6 (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)) + (ecl : ℝ) +
    (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (I / (d0 l (xm - mB) : ℝ)) else 0) +
    (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))
def CPrimeLeShort6 : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ), 2 ≤ l → 0 ≤ I →
    cPrime l k j t q h ecl xm xp mB I ≤ cShort6 l k j t q h N' ecl xm xp mB I
def Short6LeCoarse : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ),
    cCoarse l k j t q h N' ecl xm xp mB I =
        cShort6 l k j t q h N' ecl xm xp mB I + 6 * ((q : ℝ) + 2 * (j : ℝ)) ∧
      cShort6 l k j t q h N' ecl xm xp mB I ≤ cCoarse l k j t q h N' ecl xm xp mB I
def Short6Mono : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ), Monotone (cShort6 l k j t q h N' ecl xm xp mB)
def Short6Nonneg : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ), 1 ≤ l → xm ≤ xp → 0 ≤ I →
    0 ≤ cShort6 l k j t q h N' ecl xm xp mB I
def cFloorShort6 (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ)
    (ecl i : ι → ℕ) (τ : ι) : ℕ :=
  ⌊cShort6 l k (j τ) t (q τ) h N (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊
def TheoremWTopShort6 : Prop :=
  LemmaDLastGraded →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloorShort6 l N k t h lam j q xm xp ecl i) τ) ∧
    sInf {J : ℕ | TopIncl O Γ jK l N lam S J} ≤
      ∑ τ, cTau T2 ex (cFloorShort6 l N k t h lam j q xm xp ecl i) τ
def kc (P : Par) : ℕ := P.k - 1
def h0 (P : Par) : ℕ := ⌊P.h⌋₊
structure Wts (ι : Type) where
  lam : ι → ℕ → ℕ
  T2 : Finset ι
  j : ι → ℕ
  q : ι → ℕ
  xm : ι → ℤ
  xp : ι → ℤ
  c : ι → ℝ
  e : ι → ℝ
  fr : ℕ → ι → ι
  cj : ℕ → ι → Bool
  Sp : Finset ℕ
namespace Wts
variable {ι : Type} (W : Wts ι) (P : Par)
def U (τ : ι) (a : ℕ) : ℤ := UN P.Nr (W.lam τ) a
def Uset (τ : ι) : Finset ℤ := (Finset.range P.Nr).image (W.U P τ)
def top (τ : ι) : ℤ := W.U P τ (kc P + W.j τ)
def bot (τ : ι) : ℤ := W.U P τ (kc P + W.j τ + P.t - 1)
def width (τ : ι) : ℤ := W.U P τ 0 - W.U P τ (P.Nr - 1)
def UsetF (τ : ι) (l : ℕ) : Finset ℤ :=
  if W.cj l τ then (W.Uset P (W.fr l τ)).image (fun u => (h0 P : ℤ) - u) else W.Uset P (W.fr l τ)
def botF (τ : ι) (l : ℕ) : ℤ :=
  if W.cj l τ then (h0 P : ℤ) - W.top P (W.fr l τ) else W.bot P (W.fr l τ)
structure Ok : Prop where
  anti : ∀ τ a b, a ≤ b → b < P.Nr → W.lam τ b ≤ W.lam τ a
  what₂ : ∀ τ, kc P + W.j τ + P.t + W.q τ = P.Nr
  block : ∀ τ a, kc P + W.j τ ≤ a → a < kc P + W.j τ + P.t → W.lam τ a = W.lam τ (kc P + W.j τ)
  centre : ∀ τ, (W.bot P τ : ℝ) + ((P.t : ℝ) - 1) / 2 - W.c τ = -W.e τ
  window : ∀ τ, W.c τ ≤ (W.xm τ : ℝ) ∧ W.xm τ ≤ W.xp τ ∧ (W.xp τ : ℝ) ≤ W.c τ + P.S
  cloud : ∀ τ a, a < kc P → W.xm τ ≤ W.U P τ a ∧ W.U P τ a ≤ W.xp τ
  low : ∀ τ a, a < P.Nr → ((kc P ≤ a ∧ a < kc P + W.j τ) ∨ kc P + W.j τ + P.t ≤ a) →
    2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |(W.U P τ a : ℝ) - W.c τ + W.e τ| ∧
      |(W.U P τ a : ℝ) - W.c τ + W.e τ| ≤ P.η
  thick : ∀ τ ∈ W.T2, P.Thick (W.e τ) ∧ (W.xp τ : ℝ) ≤ P.h
  other : ∀ τ, τ ∉ W.T2 →
    (P.Top (W.e τ) ∧ (W.width P τ : ℝ) ≤
      P.S + P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) + P.η + ((P.t : ℝ) - 1) / 2) ∨
    (P.Thin (W.e τ) ∧ (W.width P τ : ℝ) ≤ P.S + P.w'' + P.η + ((P.t : ℝ) - 1) / 2)
def ex (τ : ι) (l : ℕ) : ℕ := LA.exZ P.Nr P.Nr le_rfl (res P.Nr (W.lam τ)) l
def ecl (τ : ι) (l : ℕ) : ℕ := LA.exZ (kc P) (kc P) le_rfl (res (kc P) (W.lam τ)) l
def mw (τ : ι) (l : ℕ) : ℕ := mwCount l (W.bot P τ) P.t (P.kap l) (W.Uset P τ)
def mwF (τ : ι) (l : ℕ) : ℕ := mwCount l (W.botF P τ l) P.t (P.kap l) (W.UsetF P τ l)
def sizeData₂ (J : ℕ → ℕ) : SizeData₂ ι where
  T2 := W.T2
  Sp := W.Sp
  J := J
  ex := W.ex P
  ecl := W.ecl P
  mw := W.mw P
  mwF := W.mwF P
  q := W.q
  j := W.j
  xlo := W.xm
  xhi := W.xp
  maxB := W.top P
  hw := fun τ => (W.width P τ : ℝ)
def iW (l : ℕ) (τ : ι) : ℕ := ⌊(W.sizeData₂ P (fun _ => 0)).depth P τ l⌋₊
def WRange (l : ℕ) : Prop := P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h ∧ ¬ P.Excl l ∧ l ∉ W.Sp
def JA [Fintype ι] (l : ℕ) : ℕ := ∑ τ, W.ex P τ l
def JW [Fintype ι] [DecidableEq ι] (l : ℕ) : ℕ :=
  ∑ τ, cTau W.T2 (fun τ => W.ex P τ l)
    (cFloorShort6 l P.Nr (kc P) P.t (h0 P) W.lam W.j W.q W.xm W.xp (fun τ => W.ecl P τ l) (W.iW P l)) τ
open Classical in

def Jrec [Fintype ι] [DecidableEq ι] (l : ℕ) : ℕ :=
  if (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp then W.JA P l else W.JW P l
end Wts
structure HidaSetting (ι : Type) (N : ℕ) (lam : ι → ℕ → ℕ) : Type 1 where
  O : Type
  [cO : CommRing O]
  [dO : IsDomain O]
  [nO : IsNoetherianRing O]
  [lO : IsLocalRing O]
  [zO : CharZero O]
  A : Type
  [rA : Ring A]
  [aA : Algebra O A]
  G : Type
  [gG : Group G]
  Γ : Subgroup G
  K : Subgroup G
  jK : K →* A
  [mA : Module A (NablaT O N lam)]
  [sA : IsScalarTower O A (NablaT O N lam)]
  T : Type
  [cT : CommRing T]
  [aT : Algebra O T]
  [mT : Module T (Forms O Γ jK (NablaT O N lam))]
  [sT : IsScalarTower O T (Forms O Γ jK (NablaT O N lam))]
  S : Submonoid T
attribute [instance] HidaSetting.cO HidaSetting.dO HidaSetting.nO HidaSetting.lO HidaSetting.zO HidaSetting.rA HidaSetting.aA
  HidaSetting.gG HidaSetting.mA HidaSetting.sA HidaSetting.cT HidaSetting.aT HidaSetting.mT HidaSetting.sT
namespace HidaSetting
variable {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam)
def Incl (l J : ℕ) : Prop := TopIncl X.O X.Γ X.jK l N lam X.S J
def Jmin (l : ℕ) : ℕ := sInf {J : ℕ | X.Incl l J}
def FrameA [DecidableEq ι] (e : ι → (Fin N → ℕ) → X.A) : Prop :=
  (∀ (s : Finset ι) (a : X.A), ∀ x ∈ tensSub (chainB (DepthNonnegative.deltaIn X.O N lam) s),
    a • x ∈ tensSub (chainB (DepthNonnegative.deltaIn X.O N lam) s)) ∧
  (∀ τ w (x : ∀ τ, dualWeyl X.O N N (res N (lam τ))) (y : dualWeyl X.O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) X.O) =
      weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) X.O) →
    e τ w • PiTensorProduct.tprod X.O x = PiTensorProduct.tprod X.O (Function.update x τ y))
variable {Λ : Type} (L : Λ → Type) [∀ μ, AddCommGroup (L μ)] [∀ μ, Module X.O (L μ)]
  [∀ μ, Module X.A (L μ)] [∀ μ, IsScalarTower X.O X.A (L μ)]
  [∀ μ, Module X.T (Forms X.O X.Γ X.jK (L μ))]
def FrameT : Prop :=
  HeckeStable X.O X.Γ X.jK X.T (NablaT X.O N lam) ∧
    ∀ μ, HeckeNat X.O X.Γ X.jK X.T (NablaT X.O N lam) (L μ)
omit [∀ μ, Module X.T (Forms X.O X.Γ X.jK (L μ))] [∀ μ, IsScalarTower X.O X.A (L μ)]
  [∀ μ, Module X.O (L μ)] in

def SimpleFacts (ϖ : X.O) (e : ι → (Fin N → ℕ) → X.A) (hwt : Λ → ι → Fin N → ℕ) : Prop :=
  (∀ (Gm : Type) [AddCommGroup Gm] [Module X.A Gm], IsSimpleModule X.A Gm →
    IsSubquot X.A (NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ) Gm →
      ∃ μ, Nonempty (Gm ≃ₗ[X.A] L μ)) ∧
  (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0)
def FirstInputWeightElim (ϖ : X.O) (hwt : Λ → ι → Fin N → ℕ) (k : ℕ) (j : ι → ℕ) (T2 : Finset ι) (i : ι → ℕ) : Prop :=
  ∀ μ, IsSubquot X.A (NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ) (L μ) →
    ¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK (L μ))) →
    ∀ τ ∈ T2, depthAt N k j lam τ (hwt μ τ) ≤ (i τ : ℤ)
end HidaSetting
def HidaSetting.WInputs {ι : Type} [DecidableEq ι] {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam)
    (l k : ℕ) (j : ι → ℕ) (T2 : Finset ι) (i : ι → ℕ) : Prop :=
  ∃ (ϖ : X.O) (n₀ : ℕ) (e : ι → (Fin N → ℕ) → X.A) (Λ : Type) (L : Λ → Type)
    (_ : ∀ μ, AddCommGroup (L μ)) (_ : ∀ μ, Module X.O (L μ)) (_ : ∀ μ, Module X.A (L μ))
    (_ : ∀ μ, IsScalarTower X.O X.A (L μ)) (_ : ∀ μ, Module X.T (Forms X.O X.Γ X.jK (L μ)))
    (hwt : Λ → ι → Fin N → ℕ),
    Finite (X.O ⧸ Ideal.span {(l : X.O)}) ∧ (l : X.O) ∣ ϖ ^ n₀ ∧ X.FrameA e ∧ X.FrameT L ∧
      X.SimpleFacts L ϖ e hwt ∧ X.FirstInputWeightElim L ϖ hwt k j T2 i
def KapFloor : Prop := ∀ (P : Par) (l : ℕ), 1 ≤ l → P.kap l = h0 P / (l - 1)
def DepthNatLe : Prop :=
  ∀ (P : Par) (ι : Type) (W : Wts ι) (l : ℕ) (τ : ι), 0 ≤ P.h → 1 ≤ l →
    W.q τ * h0 P + (l * W.mwF P τ l + W.mw P τ l) * (P.t + 2 * (h0 P / (l - 1))) ≤ W.iW P l τ
def LamUEq : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℕ) (a : Fin N), LA.lamU N N (res N lam) a = UN N lam a
def RestNear : Prop :=
  ∀ P : Par, P.Hyp → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ τ,
    (∀ a, kc P ≤ a → a < P.Nr → |(W.U P τ a : ℝ) - W.c τ + W.e τ| ≤ P.η) ∧
    (∀ a, kc P + W.j τ ≤ a → a < kc P + W.j τ + P.t →
      W.U P τ a = W.bot P τ + ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℤ)) ∧
    W.top P τ = W.bot P τ + (P.t : ℤ) - 1 ∧ W.j τ + W.q τ = P.m ∧
    (∀ a b, a < b → b < P.Nr → W.U P τ b < W.U P τ a)
def ShapeWReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ τ ∈ W.T2,
    DepthNonnegative.Shape P.Nr (kc P) (W.j τ) P.t (W.q τ) (h0 P) (W.lam τ) (W.xm τ) (W.xp τ)
def ShapeAReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ τ ∈ W.T2,
    SL2BinomialLattices.Shape P.Nr (kc P) (h0 P) (W.xp τ - W.xm τ).toNat (W.U P τ (kc P) - W.U P τ (P.Nr - 1)).toNat
      (W.xm τ) (W.U P τ (P.Nr - 1)) (fun a : Fin P.Nr => W.U P τ a) ∧
    (((W.xp τ - W.xm τ).toNat : ℕ) : ℝ) ≤ P.S ∧
    (((W.U P τ (kc P) - W.U P τ (P.Nr - 1)).toNat : ℕ) : ℝ) ≤ 2 * P.η
def ThinAReal : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).ThinA P
def ThickAReal : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).ThickA P
def CloudAReal : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).CloudA P
def ShapeTReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).ShapeT P
def WidthsReal : Prop :=
  ∀ P : Par, ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ, (W.sizeData₂ P J).Widths P
def PlacesReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    Nonempty (Places (W.sizeData₂ P J) P) ∧ (W.sizeData₂ P J).NoWindow P
def Short6LeCW : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ (J : ℕ → ℕ), ∀ τ ∈ W.T2, ∀ l : ℕ,
    2 ≤ l →
    cShort6 l (kc P) (W.j τ) P.t (W.q τ) (h0 P) P.Nr (W.ecl P τ l) (W.xm τ) (W.xp τ) (W.top P τ)
      (W.iW P l τ : ℝ) ≤ (W.sizeData₂ P J).cW P τ l
def JWLe : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (J : ℕ → ℕ) (l : ℕ), 2 ≤ l →
    (W.JW P l : ℝ) ≤ ∑ τ, (if τ ∈ (W.sizeData₂ P J).T2 then
      min ((W.sizeData₂ P J).ex τ l : ℝ) ((W.sizeData₂ P J).cW P τ l) else ((W.sizeData₂ P J).ex τ l : ℝ))
def BeyondH : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) → P.h < (l : ℝ) →
    (∀ τ, W.ex P τ l = 0) ∧ W.JA P l = 0 ∧ W.JW P l = 0
def InclAReal : Prop :=
  ∀ (P : Par) (ι : Type) [Fintype ι] (W : Wts ι), W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam),
    l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    X.Incl l (W.JA P l) ∧ X.Incl l (X.Jmin l) ∧ X.Jmin l ≤ W.JA P l
def BoundAReal : Prop :=
  ∀ (P : Par) (ι : Type) [Fintype ι] (W : Wts ι), W.Ok P → ∀ X : ℕ → HidaSetting ι P.Nr W.lam,
    (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (W.sizeData₂ P (fun l => (X l).Jmin l)).BoundA P
def TopInputsReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) → P.lJ < (l : ℝ) →
    ∀ (ϖ : X.O) (n₀ : ℕ) (e : ι → (Fin P.Nr → ℕ) → X.A) (Λ : Type) (L : Λ → Type)
      [∀ μ, AddCommGroup (L μ)] [∀ μ, Module X.O (L μ)] [∀ μ, Module X.A (L μ)]
      [∀ μ, IsScalarTower X.O X.A (L μ)] [∀ μ, Module X.T (Forms X.O X.Γ X.jK (L μ))]
      (hwt : Λ → ι → Fin P.Nr → ℕ),
    Finite (X.O ⧸ Ideal.span {(l : X.O)}) → (l : X.O) ∣ ϖ ^ n₀ → X.FrameA e → X.FrameT L →
    X.SimpleFacts L ϖ e hwt → X.FirstInputWeightElim L ϖ hwt (kc P) W.j W.T2 (W.iW P l) →
    TopInputs X.O X.A X.Γ X.jK l P.Nr (kc P) P.t (h0 P) W.lam W.T2 W.j W.q W.xm W.xp
      (fun τ => W.ecl P τ l) (fun τ => W.ex P τ l) (W.iW P l) X.T X.S ϖ n₀ e L hwt
def InclWReal : Prop :=
  LemmaDGraded → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.JW P l) ∧ X.Jmin l ≤ W.JW P l
def RecIncl : Prop :=
  LA.LemmaAZ → LemmaDGraded → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    ∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec P l) ∧ (X l).Jmin l ≤ W.Jrec P l
def BoundWReal : Prop :=
  LA.LemmaAZ → LemmaDGraded → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (W.sizeData₂ P (fun l => (X l).Jmin l)).BoundW P
def InputsReal : Prop :=
  LA.LemmaAZ → LemmaDGraded → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (W.sizeData₂ P (fun l => (X l).Jmin l)).Inputs P
def InputsRec : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 → (W.sizeData₂ P (W.Jrec P)).Inputs P
def RecSum : Prop :=
  LA.LemmaAZ → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec P l : ℝ) * Real.log (l : ℝ) ≤
        totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CorollaryOfRecord : Prop :=
  LA.LemmaAZ → LemmaDGraded → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def LatticeLink {ι : Type} (P : Par) (W : Wts ι) (l : ℕ) (τ : ι) (w : Fin P.Nr → ℕ) : Prop :=
  ∃ (E : Type) (_ : Fintype E) (σ : Equiv.Perm E) (_ : Fact l.Prime) (O' F L' : Type) (_ : CommRing O')
    (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O')
    (_ : IsAdicComplete I O') (Wl : FrobeniusPeriodChange.WLat E P.t (kc P + W.j τ + P.t + W.q τ) O' F) (u : ℤ_[l]ˣ)
    (c : ℤ_[l]) (D : WorkedExample.Labels E (kc P + W.j τ + P.t + W.q τ)) (cst : E → ℤ) (ep : E → E)
    (J : E → Fin (kc P + W.j τ + P.t + W.q τ) → ℤ) (botJ : E → ℤ) (kap : E → Fin P.t → ℤ) (ζ : O')
    (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L') (inc : ι → E),
    D.Refl σ (h0 P) P.t ∧ D.Linked F P.t cst ∧ D.Carried ep J botJ ∧
    FrobeniusPeriodChange.NInputs Wl σ l (h0 P) u c J (fun i s => botJ i + ((s : ℕ) : ℤ)) kap I ζ em jj ∧
    (∀ τ' a, D.U (inc τ') a = W.U P τ' a) ∧ (∀ τ', D.bot (inc τ') = W.bot P τ') ∧
    σ (inc τ) = (if W.cj l τ then D.cc (inc (W.fr l τ)) else inc (W.fr l τ)) ∧
    (∀ (a : Fin (kc P + W.j τ + P.t + W.q τ)) (a' : Fin P.Nr), (a : ℕ) = (a' : ℕ) →
      D.U' (inc τ) a = (w a' : ℤ) + (P.Nr : ℤ) - 1 - ((a : ℕ) : ℤ)) ∧
    ∑ a, D.U (inc τ) a = ∑ a, D.U' (inc τ) a
def DepthOfLink : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) →
    ∀ (τ : ι) (w : Fin P.Nr → ℕ), LatticeLink P W l τ w →
      depthAt P.Nr (kc P) W.j W.lam τ w ≤ (W.iW P l τ : ℤ)
def FirstInputOfLink : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam),
    l.Prime → P.lJ < (l : ℝ) →
    ∀ (ϖ : X.O) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)] [∀ μ, Module X.O (L μ)]
      [∀ μ, Module X.A (L μ)] [∀ μ, IsScalarTower X.O X.A (L μ)]
      [∀ μ, Module X.T (Forms X.O X.Γ X.jK (L μ))] (hwt : Λ → ι → Fin P.Nr → ℕ),
    (∀ μ, IsSubquot X.A (NablaT X.O P.Nr W.lam ⧸ scaleSub X.A (NablaT X.O P.Nr W.lam) ϖ) (L μ) →
      ¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK (L μ))) →
      ∀ τ ∈ W.T2, LatticeLink P W l τ (hwt μ τ)) →
    X.FirstInputWeightElim L ϖ hwt (kc P) W.j W.T2 (W.iW P l)
def WInputsLink {ι : Type} [DecidableEq ι] (P : Par) (W : Wts ι) (X : HidaSetting ι P.Nr W.lam) (l : ℕ) : Prop :=
  ∃ (ϖ : X.O) (n₀ : ℕ) (e : ι → (Fin P.Nr → ℕ) → X.A) (Λ : Type) (L : Λ → Type)
    (_ : ∀ μ, AddCommGroup (L μ)) (_ : ∀ μ, Module X.O (L μ)) (_ : ∀ μ, Module X.A (L μ))
    (_ : ∀ μ, IsScalarTower X.O X.A (L μ)) (_ : ∀ μ, Module X.T (Forms X.O X.Γ X.jK (L μ)))
    (hwt : Λ → ι → Fin P.Nr → ℕ),
    Finite (X.O ⧸ Ideal.span {(l : X.O)}) ∧ (l : X.O) ∣ ϖ ^ n₀ ∧ X.FrameA e ∧ X.FrameT L ∧
      X.SimpleFacts L ϖ e hwt ∧
      ∀ μ, IsSubquot X.A (NablaT X.O P.Nr W.lam ⧸ scaleSub X.A (NablaT X.O P.Nr W.lam) ϖ) (L μ) →
        ¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK (L μ))) →
        ∀ τ ∈ W.T2, LatticeLink P W l τ (hwt μ τ)
def WInputsOfLink : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → P.lJ < (l : ℝ) → WInputsLink P W X l →
    X.WInputs l (kc P) W.j W.T2 (W.iW P l)
def CorollaryOfRecordLink : Prop :=
  LA.LemmaAZ → LemmaDGraded → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → WInputsLink P W (X l) l) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CoarseLeCW : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ (J : ℕ → ℕ), ∀ τ ∈ W.T2, ∀ l : ℕ,
    2 ≤ l →
    cCoarse l (kc P) (W.j τ) P.t (W.q τ) (h0 P) P.Nr (W.ecl P τ l) (W.xm τ) (W.xp τ) (W.top P τ)
      (W.iW P l τ : ℝ) ≤ (W.sizeData₂ P J).cW P τ l
def Wts.coarseWeightBound {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (l : ℕ) : ℕ :=
  ∑ τ, cTau W.T2 (fun τ => W.ex P τ l)
    (cFloorCoarse l P.Nr (kc P) P.t (h0 P) W.lam W.j W.q W.xm W.xp (fun τ => W.ecl P τ l) (W.iW P l)) τ
open Classical in

def Wts.Jrec7 {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (l : ℕ) : ℕ :=
  if (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp then W.JA P l else W.coarseWeightBound P l
def CoarseWeightBoundLe : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (J : ℕ → ℕ) (l : ℕ), 2 ≤ l →
    W.JW P l ≤ W.coarseWeightBound P l ∧
    (W.coarseWeightBound P l : ℝ) ≤ ∑ τ, (if τ ∈ (W.sizeData₂ P J).T2 then
      min ((W.sizeData₂ P J).ex τ l : ℝ) ((W.sizeData₂ P J).cW P τ l) else ((W.sizeData₂ P J).ex τ l : ℝ))
def HidaLatticeInclusionAtCoarseWeightBound : Prop :=
  LemmaDGraded → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.coarseWeightBound P l) ∧ X.Jmin l ≤ W.coarseWeightBound P l
def RecIncl7 : Prop :=
  LA.LemmaAZ → LemmaDGraded → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    ∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Jmin l ≤ W.Jrec7 P l
def InputsRec7 : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 → (W.sizeData₂ P (W.Jrec7 P)).Inputs P
def RecSum7 : Prop :=
  LA.LemmaAZ → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
        totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CorollaryOfRecord7 : Prop :=
  LA.LemmaAZ → LemmaDGraded → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CorollaryOfRecord7Link : Prop :=
  LA.LemmaAZ → LemmaDGraded → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → WInputsLink P W (X l) l) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def SixLeParameterProductAndQuotientBound : Prop :=
  ∀ P : Par, P.Hyp → 0 ≤ P.L →
    6 ≤ P.t * P.f * P.k ^ 3 * P.m ∧
      12 * P.L * P.b / ((P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3) ≤ 2 * (P.m : ℝ) * P.b * P.L
end Formalism.CohomologicalDescent.ShortWeightBounds


