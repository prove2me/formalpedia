-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementPN
-- name    : Formalism_HermitianCurvature_StatementPN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:43.110288+00:00
-- url     : https://prove2.me/theorems/4b5e86b8-a0ea-4cf1-aaf1-f6cbc4b31980
-- title:
--   Statement PN
-- statement:
--   Definitions and structural lemmas for Statement PN, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementPN.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.PN
open Finset NumberField
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Classical
def NormInputs {P : Type} [Fintype P] (B : S3.MassData P) : Prop :=
  B.Pos ∧ B.InJacMod ∧ B.InNu ∧ B.InInfinity ∧ B.InVolumes ∧ B.InLevelS ∧ B.InMasses ∧ B.InColumns ∧
  B.InOrdinary ∧ B.InTyped ∧ B.InIndices
def NormBound : Prop :=
  ∀ (P : Type) [Fintype P] (B : S3.MassData P), NormInputs B →
    B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN) ≤ B.d * B.d' / B.Dstar
def NormOfMain : Prop := S3.MainTheorem → NormBound
def NormOfLemmas : Prop := S3.JacobianConstant → S3.LocalProduct → S3.Columns → NormBound
def abelian₂ (rd : ℝ) (r k f : ℕ) : ℝ := rd ^ (2 * r * (r + 1) * (k - 1) * f)
def FrameInputs {P : Type} [Fintype P] (B : S3.MassData P) (rd g : ℝ) (r k f : ℕ) (Irat Ire : ℝ) : Prop :=
  0 < rd ∧ 0 < g ∧
  B.unitLevelVolume / B.volZZ =
    rd ^ (((f * (r + 1) * (8 * r ^ 2 + 10 * r + 3) : ℕ) : ℝ) / 3) * g ^ (f * (r + 1) * (2 * r + 3)) ∧
  (B.c0 * B.c0')⁻¹ * B.IntC = 2 ^ (f * (r + 1)) * Irat ∧
  Irat = abelian₂ rd r k f * rd ^ (((f * r * (r + 1) * (8 * r + 10) : ℕ) : ℝ) / 3) * Ire
def FramePassage : Prop :=
  ∀ (P : Type) [Fintype P] (B : S3.MassData P) (rd g : ℝ) (r k f : ℕ) (Irat Ire : ℝ), B.Pos → B.InJacMod →
    FrameInputs B rd g r k f Irat Ire →
    abelian₂ rd r k f * Ire =
      (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) * ((B.c0 * B.c0')⁻¹ * B.IntN)
def NormRe : Prop :=
  NormBound → FramePassage →
  ∀ (P : Type) [Fintype P] (B : S3.MassData P) (rd g : ℝ) (r k f : ℕ) (Irat Ire : ℝ), NormInputs B →
    FrameInputs B rd g r k f Irat Ire →
    B.Gam1 * (abelian₂ rd r k f * B.AA) * Ire ≤
      (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) * (B.d * B.d' / B.Dstar)
structure LocalNG (Cl Nu : Type) where

  P : Type
  [fP : Fintype P]

  Om : Finset P

  D : P → Type
  [fD : ∀ p, Fintype (D p)]

  wt : ∀ p, D p → ℝ

  aN : ∀ p, D p → ℂ

  aZ : ∀ p, D p → ℂ

  H : P → ℝ

  nn : P → ℝ

  ngen : P → ℝ

  q : P → ℕ

  V0 : ℝ

  rw : Cl → ℝ

  dat : Cl → Nu → Option (∀ p, D p)
attribute [instance] LocalNG.fP LocalNG.fD
namespace LocalNG
variable {Cl Nu : Type} (L : LocalNG Cl Nu)
def ampNG (d : ∀ p, L.D p) : ℂ :=
  ∑ A ∈ L.Om.powerset.filter (fun A => A.Nonempty),
    ∏ p, (if p ∈ A then L.aN p (d p) else L.aZ p (d p))
def a2 (c : Cl) (ν : Nu) : ℝ :=
  match L.dat c ν with
  | none => 0
  | some d => L.rw c * ‖L.ampNG d‖ ^ 2
def Htot : ℝ := ∏ p, L.H p
def ngenTot : ℝ := L.V0 * ∏ p, L.ngen p
def Basic : Prop :=
  (∀ p d, 0 ≤ L.wt p d) ∧ (∀ p, 1 ≤ L.H p) ∧ (∀ p, 2 ≤ L.q p) ∧ (∀ p ∈ L.Om, (L.q p : ℝ) ≤ L.H p) ∧
  (∀ p, 0 ≤ L.nn p) ∧ 0 ≤ L.V0 ∧ ∀ c, 0 ≤ L.rw c
def NGAt (C1 r k : ℕ) : Prop :=
  (∀ p ∈ L.Om, ∑ d, L.wt p d * ‖L.aN p d‖ ^ 2 ≤
    L.H p ^ (C1 * (r + 1) ^ 2) * ((L.q p : ℝ) ^ (k - 2 * r - 5))⁻¹ * L.nn p) ∧
  (∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ L.H p ^ (C1 * (r + 1) ^ 2) * L.nn p)
def MassRatioAt (C0 r : ℕ) : Prop :=
  (∀ p, p ∉ L.Om → L.nn p = L.ngen p) ∧
  (∀ p ∈ L.Om, L.nn p ≤ 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) * L.ngen p)
def Unfold : Prop :=
  ∀ (d : ∀ p, L.D p) (S : Finset (Cl × Nu)), (∀ x ∈ S, L.dat x.1 x.2 = some d) →
    ∑ x ∈ S, L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p)
end LocalNG
def e7 (C1 C0 r : ℕ) : ℕ := C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5
def ZpowForm : Prop :=
  ∀ q k r : ℕ, 1 ≤ q → 2 * r + 5 ≤ k →
    (q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ (k - 2 * r - 5))⁻¹
def MeanAmpJoint : Prop :=
  Formalism.HermitianLatticeCounting.S4.Step4 → Formalism.HermitianLatticeCounting.S4.OmCount →
  ∀ (Cl Nu : Type) (L : LocalNG Cl Nu) (C1 C0 r k : ℕ), L.Basic → L.NGAt C1 r k → L.MassRatioAt C0 r →
    L.Unfold → ∀ S : Finset (Cl × Nu),
      ∑ x ∈ S, L.a2 x.1 x.2 ≤ ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ * L.Htot ^ e7 C1 C0 r * L.ngenTot
def ClassSquaresSum : Prop :=
  ∀ (ι C V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (v : ι → V)
    (cl : ι → C), Summable (fun i => ‖v i‖) →
    Summable (fun c => ‖∑' i, ({i | cl i = c} : Set ι).indicator v i‖ ^ 2) ∧
    ∑' p : ι × ι, ({p | cl p.1 = cl p.2} : Set (ι × ι)).indicator
        (fun p => (inner ℂ (v p.1) (v p.2)).re) p =
      ∑' c, ‖∑' i, ({i | cl i = c} : Set ι).indicator v i‖ ^ 2
def ClassCS : Prop :=
  Formalism.HermitianLatticeCounting.S4.WeightedCS →
  ∀ (Cl J V : Type) [NormedAddCommGroup V] (U : Cl → J → V) (W : J → ℝ) (y : Cl → J → ℝ) (Sw M : ℝ),
    0 ≤ Sw → (∀ c j, U c j ≠ 0 → 0 < W j) → (∀ c j, ‖U c j‖ ^ 2 ≤ y c j) →
    (∀ (c : Cl) (T : Finset J), (∀ j ∈ T, U c j ≠ 0) → ∑ j ∈ T, (W j)⁻¹ ≤ Sw) →
    (∀ T : Finset (Cl × J), (∀ x ∈ T, U x.1 x.2 ≠ 0) → ∑ x ∈ T, W x.2 * y x.1 x.2 ≤ M) →
    ∀ Cs : Finset Cl, ∑ c ∈ Cs, ‖∑' j, U c j‖ ^ 2 ≤ Sw * M
def FirstBracket : Prop :=
  ∀ (Γ Nu : Type) (w Pn : Γ → ℝ) (occ : Γ → Nu → Prop) (Sw : ℝ),
    (∀ γ, 0 < w γ) → (∀ γ ν, occ γ ν → 0 < Pn γ) →
    (∀ (γ : Γ) (S : Finset Nu), (∀ ν ∈ S, occ γ ν) → (S.card : ℝ) ≤ Pn γ) →
    (∀ S : Finset Γ, (∀ γ ∈ S, ∃ ν, occ γ ν) → ∑ γ ∈ S, (w γ)⁻¹ ≤ Sw) →
    ∀ T : Finset (Γ × Nu), (∀ x ∈ T, occ x.1 x.2) → ∑ x ∈ T, (w x.1 * Pn x.1)⁻¹ ≤ Sw
def SecondBracket : Prop :=
  ∀ (Cl Γ Nu : Type) (isPt : Γ → Prop) (a2 : Cl → Γ → Nu → ℝ) (w Jloc JB n NG ND Hh ngen : Γ → ℝ)
    (κ2 cSt AAre e1 gf Pc TB : ℝ) (e7 eN Aexp : ℕ),
    0 ≤ κ2 → 0 ≤ cSt → 0 ≤ AAre → 0 ≤ e1 → 1 ≤ gf → 0 ≤ Pc → e7 + eN + 6 ≤ Aexp →
    (∀ c γ ν, 0 ≤ a2 c γ ν) →
    (∀ γ, isPt γ → 0 < w γ ∧ 0 ≤ Jloc γ ∧ 0 ≤ JB γ ∧ 0 ≤ n γ ∧ 1 ≤ NG γ ∧ 1 ≤ ND γ ∧ 1 ≤ Hh γ) →
    (∀ γ, isPt γ → ∀ S : Finset (Cl × Nu), ∑ x ∈ S, a2 x.1 γ x.2 ≤ κ2 * Hh γ ^ e7 * ngen γ) →
    (∀ γ, isPt γ → Jloc γ ≤ cSt * JB γ) →
    (∀ γ, isPt γ → ngen γ ≤ AAre * e1 * Hh γ ^ eN * n γ) →
    (∀ γ, isPt γ → Hh γ ≤ gf * NG γ * ND γ) →
    (∀ S : Finset Γ, (∀ γ ∈ S, isPt γ) →
      ∑ γ ∈ S, w γ * n γ * (NG γ * ND γ) ^ Aexp * JB γ ≤ TB) →
    ∀ T : Finset (Cl × Γ × Nu), (∀ x ∈ T, isPt x.2.1) →
      ∑ x ∈ T, (w x.2.1 * (Pc * NG x.2.1 ^ 6)) * (a2 x.1 x.2.1 x.2.2 * Jloc x.2.1) ≤
        κ2 * cSt * AAre * e1 * Pc * gf ^ Aexp * TB
abbrev Pts (E : Type) [Field E] (r : ℕ) : Type := Σ c : Composition (r + 1), (Fin c.length → E)
structure NGData (τ E : Type) [Field E] (r : ℕ) (Cl Nu : Type) where

  cls : τ → Cl

  pt : τ → Pts E r

  nml : τ → Nu

  a2 : Cl → Pts E r → Nu → ℝ

  J2loc : Pts E r → ℝ

  jacobianSquareBound : Pts E r → ℝ

  n : Pts E r → ℝ

  NG : Pts E r → ℝ

  ND : Pts E r → ℝ

  Hh : Pts E r → ℝ

  ngen : Pts E r → ℝ
section row
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
  {E : Type} [Field E] {r : ℕ} {Cl Nu : Type} (N : NGData τ E r Cl Nu)
def grp (c : Cl) (γ : Pts E r) (ν : Nu) : H₁ :=
  ∑' t, (X.ngSet ∩ {t | N.cls t = c ∧ N.pt t = γ ∧ N.nml t = ν}).indicator X.vec t
def Occ (c : Cl) (γ : Pts E r) (ν : Nu) : Prop :=
  ∃ t ∈ X.ngSet, X.vec t ≠ 0 ∧ N.cls t = c ∧ N.pt t = γ ∧ N.nml t = ν
def IsPt (γ : Pts E r) : Prop := ∃ c ν, Occ X N c γ ν
def ClassInput : Prop :=
  ∀ t ∈ X.ngSet, ∀ t' ∈ X.ngSet, (X.rowOf t = X.rowOf t' ∧ X.s0 t t' = 1) ↔ N.cls t = N.cls t'
def AmpInput : Prop :=
  (∀ c γ ν, 0 ≤ N.a2 c γ ν) ∧ (∀ γ, 0 ≤ N.J2loc γ) ∧
  ∀ c γ ν, ‖grp X N c γ ν‖ ^ 2 ≤ N.a2 c γ ν * N.J2loc γ
def NormalsInput (Pc : ℝ) : Prop :=
  ∀ (c : Cl) (γ : Pts E r) (S : Finset Nu), (∀ ν ∈ S, Occ X N c γ ν) → (S.card : ℝ) ≤ Pc * N.NG γ ^ 6
def PointsInput : Prop := ∀ γ, IsPt X N γ → Formalism.HermitianLatticeCounting.ExpansionTerms.BlockEndMinorsIntegral γ
def LocalInput (C1 C0 k : ℕ) : Prop :=
  ∀ γ, IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : LocalNG Cl Nu, L.Basic ∧ L.NGAt C1 r k ∧ L.MassRatioAt C0 r ∧
    L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = L.a2 x.1 x.2) ∧ N.Hh γ = L.Htot ∧ N.ngen γ = L.ngenTot
def MeasureInput (cSt : ℝ) : Prop :=
  ∀ γ, IsPt X N γ → 0 ≤ N.jacobianSquareBound γ ∧ N.J2loc γ ≤ cSt * N.jacobianSquareBound γ
def eN (r : ℕ) : ℕ := 10 * (r + 1) ^ 2 + 6 * (2 * r + 2) + 1
def GenMassInput (AAre e1 : ℝ) : Prop :=
  ∀ γ, IsPt X N γ → 0 ≤ N.n γ ∧ N.ngen γ ≤ AAre * e1 * N.Hh γ ^ eN r * N.n γ
def GenMassSplit (AAre e1 : ℝ) (Gk dens tw : Pts E r → ℝ) : Prop :=
  ∀ γ, IsPt X N γ → 0 < Gk γ ∧ 0 < tw γ ∧ N.n γ = Gk γ * tw γ ∧ 0 ≤ dens γ ∧ dens γ ≤ e1 * N.Hh γ ∧
    (tw γ)⁻¹ ≤ N.Hh γ ^ (6 * (2 * r + 2)) ∧ N.ngen γ ≤ AAre * Gk γ * dens γ * N.Hh γ ^ (10 * (r + 1) ^ 2)
def HeightInput (gf : ℝ) : Prop :=
  ∀ γ, IsPt X N γ → 1 ≤ N.NG γ ∧ 1 ≤ N.ND γ ∧ N.Hh γ ≤ gf * N.NG γ * N.ND γ
def PointSumInput [NumberField E] (Aexp : ℕ) (TB : ℝ) : Prop :=
  ∀ S : Finset (Pts E r), (∀ γ ∈ S, IsPt X N γ) →
    ∑ γ ∈ S, Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * N.n γ * (N.NG γ * N.ND γ) ^ Aexp * N.jacobianSquareBound γ ≤ TB
end row
def GenMassOfSplit : Prop :=
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) (E : Type) [Field E] (r : ℕ) (Cl Nu : Type)
    (N : NGData τ E r Cl Nu) (AAre e1 : ℝ) (Gk dens tw : Pts E r → ℝ), 0 ≤ AAre →
    (∀ γ, IsPt X N γ → 1 ≤ N.Hh γ) → GenMassSplit X N AAre e1 Gk dens tw → GenMassInput X N AAre e1
def ExactCores : Prop :=
  Formalism.HermitianLatticeCounting.S4.Step4 ∧ Formalism.HermitianLatticeCounting.S4.OmCount ∧ Formalism.HermitianLatticeCounting.S4.WeightedCS ∧ Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumPowSixtyFour
def RowFromClasses : Prop :=
  ClassSquaresSum →
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁)
    (E : Type) [Field E] (r : ℕ) (Cl Nu : Type) (N : NGData τ E r Cl Nu), X.AbsConv → ClassInput X N →
    Summable (fun c => ‖∑' x : Pts E r × Nu, grp X N c x.1 x.2‖ ^ 2) ∧
    X.pairSum (X.one X.ngSet) = X.Gam1 * ∑' c, ‖∑' x : Pts E r × Nu, grp X N c x.1 x.2‖ ^ 2
def RowNGAbstract : Prop :=
  ExactCores → ClassSquaresSum → RowFromClasses → ClassCS → FirstBracket → SecondBracket → MeanAmpJoint →
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r k : ℕ) (Cl Nu : Type) (N : NGData τ E r Cl Nu)
    (C1 C0 Aexp : ℕ) (Pc gf cSt AAre e1 TB : ℝ),
    e7 C1 C0 r + eN r + 6 ≤ Aexp → 0 < Pc → 1 ≤ gf → 0 ≤ cSt → 0 ≤ AAre → 0 ≤ e1 →
    X.AbsConv → ClassInput X N → AmpInput X N → NormalsInput X N Pc → PointsInput X N →
    LocalInput X N C1 C0 k → MeasureInput X N cSt → GenMassInput X N AAre e1 → HeightInput X N gf →
    PointSumInput X N Aexp TB →
    X.pairSum (X.one X.ngSet) ≤ X.Gam1 * (64 ^ (Fintype.card (InfinitePlace E) * (r + 1)) *
      (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ * cSt * AAre * e1 * Pc * gf ^ Aexp * TB))
def ExponentSum : Prop :=
  ∀ C1 C0 A r : ℕ, C1 + C0 + 38 ≤ A → e7 C1 C0 r + eN r + 6 ≤ A * (r + 1) ^ 2
def ExponentSumText : Prop :=
  ∀ r : ℕ, ((39 + 9) * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5) + (10 * (r + 1) ^ 2 + 6 * (2 * r + 2) + 1) + 6 ≤
      86 * (r + 1) ^ 2 ∧ 86 * (r + 1) ^ 2 ≤ 100 * (r + 1) ^ 2
def NGSizes (Cg CT CSt : ℝ) (r f : ℕ) (b rd g TT cSt e1 : ℝ) : Prop :=
  1 ≤ f ∧ 16 ≤ b ∧ 0 < rd ∧ rd ≤ b ∧ 1 ≤ g ∧ g ≤ b ^ Cg ∧ 0 < TT ∧
  TT ≤ b ^ (2 * CT * ((2 * r + 2 : ℕ) : ℝ)) ∧ 0 ≤ cSt ∧
  cSt ≤ b ^ (CSt * ((2 * r + 2 : ℕ) : ℝ) ^ 3 * f) ∧ 0 ≤ e1 ∧ e1 ≤ 2
def NGNumbers : Prop :=
  ∀ (A : ℕ) (CB CSt Cg CT : ℝ), 0 ≤ CB → 0 ≤ CSt → 0 ≤ Cg → 0 ≤ CT → ∃ Cn : ℝ, 0 ≤ Cn ∧
    ∀ (r f : ℕ) (b rd g TT cSt e1 : ℝ), NGSizes Cg CT CSt r f b rd g TT cSt e1 →
      64 ^ (f * (r + 1)) * (cSt * e1 * (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) *
          (g ^ f) ^ (A * (r + 1) ^ 2) * Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b)) *
        ((rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3))) ≤
      Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b)
def NGInputs {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
    {E : Type} [Field E] [NumberField E] {r : ℕ} {Cl Nu : Type} (N : NGData τ E r Cl Nu) (k f C1 C0 A : ℕ)
    (CB b rd g TT cSt AAre e1 Ire : ℝ) : Prop :=
  ClassInput X N ∧ AmpInput X N ∧ NormalsInput X N (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) ∧
  PointsInput X N ∧ LocalInput X N C1 C0 k ∧ MeasureInput X N cSt ∧ GenMassInput X N AAre e1 ∧
  HeightInput X N (g ^ f) ∧
  PointSumInput X N (A * (r + 1) ^ 2)
    (Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) * Ire)
def NGChain : Prop :=
  ExactCores ∧ ClassSquaresSum ∧ RowFromClasses ∧ ClassCS ∧ FirstBracket ∧ SecondBracket ∧ MeanAmpJoint ∧
  RowNGAbstract ∧ NormBound ∧ FramePassage ∧ NormRe ∧ ExponentSum ∧ NGNumbers
def RowNGJoint : Prop :=
  NGChain →
  ∀ (C1 C0 A : ℕ) (CB CSt Cg CT : ℝ), 0 ≤ CB → 0 ≤ CSt → 0 ≤ Cg → 0 ≤ CT →
    C1 + C0 + 38 ≤ A → ∃ Cn : ℝ, 0 ≤ Cn ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
      [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r k : ℕ) (Cl Nu : Type) (N : NGData τ E r Cl Nu)
      (P : Type) [Fintype P] (B : S3.MassData P) (b rd g TT cSt e1 Irat Ire : ℝ),
      X.AbsConv → X.Gam1 = B.Gam1 → NormInputs B →
      FrameInputs B rd g r k (Fintype.card (InfinitePlace E)) Irat Ire →
      NGSizes Cg CT CSt r (Fintype.card (InfinitePlace E)) b rd g TT cSt e1 →
      NGInputs X N k (Fintype.card (InfinitePlace E)) C1 C0 A CB b rd g TT cSt
        (abelian₂ rd r k (Fintype.card (InfinitePlace E)) * B.AA) e1 Ire →
      X.RowNG (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
        Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card (InfinitePlace E) : ℕ) * Real.log b))
        (B.d * B.d' / B.Dstar)
def PairCores : Prop :=
  PB.MainRow ∧ PB.PairBound ∧ PB.LocalCores ∧ PB.GlobalCores ∧ PB.LatticeLink ∧ PB.AxiomsOfLocalModel ∧
  A5.ThetaExistsStep ∧ PB.PairBoundAbstract ∧ PB.NormSqBoundOfEqualIota ∧ PB.GramSumLeOfPosSemidef ∧ PB.PairSplit ∧ PB.SubFamily ∧
  PB.NumPrice ∧ PB.NumExp ∧ PB.NumDens ∧ PB.NumLoops ∧ PB.NumNG ∧ PB.NGExponent ∧ PB.SqrtSumSqLeOneAddInvPowSix
def LoopCores : Prop :=
  Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum ∧ Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum ∧ Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound ∧ Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt ∧
  Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' ∧ PB.LoopsJoint ∧ PB.LoopsGiveRows
def PairBoundFromLocalNG : Prop :=
  PB.PairBoundFromLocal → PairCores → RowNGJoint → NGChain → LoopCores →
  ∀ C₄ Cthr CL : ℝ, 1 ≤ C₄ → 1 ≤ CL →
  ∀ (C1 C0n A : ℕ) (CB CSt Cg CT : ℝ), 0 ≤ CB → 0 ≤ CSt → 0 ≤ Cg → 0 ≤ CT →
    C1 + C0n + 38 ≤ A →
    ∃ CA C K₀ Cn : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧ 0 ≤ Cn ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (bb Cp Cf Th : ℝ)
      (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → J.SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      S6.Unram E → J.Inst D e G CA de de' T T' l → PB.LocalModel D →
      ∀ (jn : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) (sd : ℝ),
        PB.RealInputs D C₄ jn Vt → PB.DensInput G.k G.r G.f sd →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), PB.RowsInput D sd Vt c B → PB.MassDataHyp B →
          PB.EnergyLink B jn sd C Th D.r D.f →
          ∀ (τ Rw I HS H₁ : Type) [Fintype I] [NormedAddCommGroup HS] [InnerProductSpace ℂ HS]
            [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
            (X : PB.Terms τ Rw I HS H₁),
            PB.Link X B G de T du du' → PB.SplitInputs X B.tt →
            PB.SizeNumbers G.k G.r G.f bb G.g1 G.g2 (1 / 3) Cn →
            ∀ (Al NT Gam : ℝ) (Xi : ℕ → ℝ), 1 ≤ Al →
              Formalism.HermitianLatticeCounting.LatticeSumBounds.Params CL K₀ G.k (2 * G.r + 2) G.f bb G.g G.v NT Gam →
              Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp CL G.k (2 * G.r + 2) G.f bb G.v NT Xi →
              6 * Real.log (3 * Al) ≤ (G.k : ℝ) * G.f * Real.log G.k →
              PB.LoopsInput X Al CL G.k G.r G.f bb G.g G.v Gam Xi
                (du * du' / (G.size de T du).Dstar) →
              ∀ (Cl Nu : Type) (N : NGData τ E G.r Cl Nu) (cSt e1 Irat Ire : ℝ),
                FrameInputs B (2 * G.v) G.g G.r G.k G.f Irat Ire →
                NGSizes Cg CT CSt G.r G.f bb (2 * G.v) G.g ((T : ℝ) * T') cSt e1 →
                NGInputs X N G.k G.f C1 C0n A CB bb (2 * G.v) G.g ((T : ℝ) * T') cSt
                  (abelian₂ (2 * G.v) G.r G.k G.f * B.AA) e1 Ire →
                ‖X.K0‖ ^ 2 ≤ (1 + (bb ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar)
end
end Formalism.FourierDecayAlt.PN


