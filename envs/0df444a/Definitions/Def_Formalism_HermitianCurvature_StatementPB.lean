-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementPB
-- name    : Formalism_HermitianCurvature_StatementPB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:44.998317+00:00
-- url     : https://prove2.me/theorems/1524a275-cb70-4a0b-bcac-14c2e8b54b78
-- title:
--   Statement PB
-- statement:
--   Definitions and structural lemmas for Statement PB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementPB.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.PB
open Finset NumberField
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Classical
structure Terms (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] where

  op : τ → H

  vec : τ → H₁

  rowOf : τ → Rw

  io : Rw → I

  isId : τ → Prop

  G : τ → ℝ

  gener : τ → Prop

  GG : I → I → ℂ

  Gam1 : ℝ

  s0 : τ → τ → ℕ

  scal : τ → τ → Prop
namespace Terms
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁)
def idSet : Set τ := {t | X.isId t}
def degSet : Set τ := {t | X.G t = 0 ∧ ¬ X.isId t}
def ngSet : Set τ := {t | X.G t ≠ 0 ∧ ¬ X.gener t}
def genSet : Set τ := {t | X.G t ≠ 0 ∧ X.gener t}
def nzSet : Set τ := {t | X.G t ≠ 0}
def part (S : Set τ) : H := ∑' t, S.indicator X.op t
def vecPart (S : Set τ) (i : I) : H₁ := ∑' t, (S ∩ {t | X.io (X.rowOf t) = i}).indicator X.vec t
def K : H := ∑' t, X.op t
def K0 : H := X.part X.idSet + X.part X.genSet + X.part X.ngSet
def PhiEq (S : Set τ) : ℝ := X.Gam1 * ∑ i, ‖X.vecPart S i‖ ^ 2
def allPairs (S : Set τ) : Set (τ × τ) := {p | p.1 ∈ S ∧ p.2 ∈ S ∧ X.rowOf p.1 = X.rowOf p.2}
def big (S : Set τ) : Set (τ × τ) := {p | p ∈ X.allPairs S ∧ 2 ≤ X.s0 p.1 p.2}
def one (S : Set τ) : Set (τ × τ) := {p | p ∈ X.allPairs S ∧ X.s0 p.1 p.2 = 1}
def nsc (S : Set τ) : Set (τ × τ) := {p | p ∈ X.allPairs S ∧ X.s0 p.1 p.2 = 1 ∧ ¬ X.scal p.1 p.2}
def sc (S : Set τ) : Set (τ × τ) := {p | p ∈ X.allPairs S ∧ X.s0 p.1 p.2 = 1 ∧ X.scal p.1 p.2}
def pairSum (Q : Set (τ × τ)) : ℝ :=
  X.Gam1 * ∑' p : τ × τ, Q.indicator (fun p => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p
def pairAbs (Q : Set (τ × τ)) : ℝ :=
  X.Gam1 * ∑' p : τ × τ, Q.indicator (fun p => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p
def AbsConv : Prop :=
  Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1
def IdDegenerate : Prop := ∀ t, X.isId t → X.G t = 0
def NormExpansionOn (S : Set τ) : Prop :=
  ‖X.part S‖ ^ 2 = (∑ i, ∑ j, X.GG i j * inner ℂ (X.vecPart S i) (X.vecPart S j)).re
def GGBound (Pg : ℝ) : Prop :=
  (((Pg * X.Gam1 : ℝ) : ℂ) • (1 : Matrix I I ℂ) - Matrix.of X.GG).PosSemidef
def RowOrth : Prop :=
  ∀ t t', X.io (X.rowOf t) = X.io (X.rowOf t') → X.rowOf t ≠ X.rowOf t' →
    inner ℂ (X.vec t) (X.vec t') = 0
def CorankPos : Prop :=
  ∀ t t', X.rowOf t = X.rowOf t' → X.G t ≠ 0 → X.G t' ≠ 0 → 1 ≤ X.s0 t t'
def IdZero : Prop := X.part X.idSet = 0
def RowBig (ε dd : ℝ) : Prop := X.pairAbs (X.big X.nzSet) ≤ ε * dd
def RowNotScalar (ε dd : ℝ) : Prop := X.pairAbs (X.nsc X.genSet) ≤ ε * dd
def RowLoops (ε dd : ℝ) : Prop := X.pairAbs (X.big X.nzSet ∪ X.nsc X.genSet) ≤ ε * dd
def RowMain (A dd : ℝ) : Prop := X.pairSum (X.sc X.genSet) ≤ A * dd
def RowNG (ε dd : ℝ) : Prop := X.pairSum (X.one X.ngSet) ≤ ε * dd
end Terms
def FourParts : Prop :=
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁), X.IdDegenerate →
    X.idSet ∪ X.degSet ∪ X.ngSet ∪ X.genSet = Set.univ ∧
    Disjoint X.idSet X.degSet ∧ Disjoint X.idSet X.ngSet ∧ Disjoint X.idSet X.genSet ∧
    Disjoint X.degSet X.ngSet ∧ Disjoint X.degSet X.genSet ∧ Disjoint X.ngSet X.genSet
def SplitSum : Prop :=
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁), X.AbsConv →
    X.IdDegenerate → X.K = X.K0 + X.part X.degSet
def GramSumLeOfPosSemidef : Prop :=
  ∀ (I H₁ : Type) [Fintype I] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (Γ : I → I → ℂ)
    (c : ℝ) (a : I → H₁), (((c : ℝ) : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ).PosSemidef →
    (∑ i, ∑ j, Γ i j * inner ℂ (a i) (a j)).re ≤ c * ∑ i, ‖a i‖ ^ 2
def GGNumeric : Prop :=
  ∀ (k : ℕ) (g : ℝ), 3 ≤ g → ∏ i ∈ Icc 1 k, (1 - (g ^ i)⁻¹)⁻¹ ≤ 1 + 3 / g
def NormSqBoundOfEqualIota : Prop :=
  GramSumLeOfPosSemidef →
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁) (Pg : ℝ) (S : Set τ),
    X.NormExpansionOn S → X.GGBound Pg → ‖X.part S‖ ^ 2 ≤ Pg * X.PhiEq S
def PairSplit : Prop :=
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Terms τ Rw I H H₁),
    X.AbsConv → X.RowOrth → X.CorankPos →
    (∀ S : Set τ, X.PhiEq S = X.pairSum (X.allPairs S)) ∧
    X.PhiEq X.genSet =
      X.pairSum (X.big X.genSet) + X.pairSum (X.nsc X.genSet) + X.pairSum (X.sc X.genSet) ∧
    X.PhiEq X.ngSet = X.pairSum (X.big X.ngSet) + X.pairSum (X.one X.ngSet)
def SubFamily : Prop :=
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁), X.AbsConv →
    ∀ Q Q' : Set (τ × τ), Q ⊆ Q' → X.pairAbs Q ≤ X.pairAbs Q' ∧ |X.pairSum Q| ≤ X.pairAbs Q
def LoopsGiveRows : Prop :=
  SubFamily →
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁) (ε dd : ℝ), X.AbsConv →
    X.RowLoops ε dd → X.RowBig ε dd ∧ X.RowNotScalar ε dd
def NGTotal : Prop :=
  PairSplit → SubFamily →
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Terms τ Rw I H H₁)
    (ε ε' dd : ℝ), X.AbsConv → X.RowOrth → X.CorankPos → X.RowBig ε dd → X.RowNG ε' dd →
    X.PhiEq X.ngSet ≤ (ε + ε') * dd
def NormSqAddBoundBySqrtSum : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] (x y : H) (η ε dd : ℝ), 0 ≤ dd →
    ‖x‖ ^ 2 ≤ (1 + η + ε) * dd → ‖y‖ ^ 2 ≤ ε * dd →
    ‖x + y‖ ^ 2 ≤ (√(1 + η + ε) + √ε) ^ 2 * dd
def PairBoundAbstract : Prop :=
  NormSqBoundOfEqualIota → GramSumLeOfPosSemidef → PairSplit → SubFamily →
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Terms τ Rw I H H₁)
    (Pg A ε ε' dd : ℝ), 0 ≤ Pg → 0 ≤ dd →
    X.AbsConv → (X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) → X.GGBound Pg → X.RowOrth →
    X.CorankPos → X.IdZero →
    X.RowBig ε dd → X.RowNotScalar ε dd → X.RowMain A dd → X.RowNG ε' dd →
    ‖X.K0‖ ^ 2 ≤ (√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2 * dd
def NumPrice : Prop :=
  ∀ (f k : ℕ) (b g1 g2 : ℝ), 1 ≤ b → 1 ≤ k → f ≤ k → ((k : ℝ) * b) ^ 8 ≤ g1 → ((k : ℝ) * b) ^ 8 ≤ g2 →
    (f : ℝ) / g1 ≤ (b ^ 7)⁻¹ ∧ (f : ℝ) / g2 ≤ (b ^ 7)⁻¹ ∧
    0 ≤ (1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f ∧
    (1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f ≤ Real.exp (6 * (b ^ 7)⁻¹)
def NumExp : Prop :=
  ∀ (k : ℕ) (b : ℝ), 0 < b → 70 * Real.log b ≤ k → Real.exp (-(k : ℝ) / 5) ≤ (b ^ 14)⁻¹
def NumDens : Prop :=
  ∀ k r f : ℕ, f ≤ k → 32 ≤ k → 4 * r + 12 ≤ k →
    12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹ ≤ (f : ℝ) * (2 : ℝ) ^ (-(k : ℝ) / 2) ∧
    (f : ℝ) * (2 : ℝ) ^ (-(k : ℝ) / 2) ≤ Real.exp (-(k : ℝ) / 5)
def NumLoops : Prop :=
  ∀ (k f : ℕ) (c : ℝ), 1 ≤ 5 * c * f * Real.log k →
    Real.exp (-(c * k * f * Real.log k)) ≤ Real.exp (-(k : ℝ) / 5)
def NumNG : Prop :=
  ∀ (k m f : ℕ) (C b : ℝ), 8 * (C * (m : ℝ) ^ 5 * f * Real.log b) ≤ k →
    (2 : ℝ) ^ (-(k : ℝ) / 2) * Real.exp (C * (m : ℝ) ^ 5 * f * Real.log b) ≤ Real.exp (-(k : ℝ) / 5)
def NGExponent : Prop :=
  ∀ k r : ℕ, 4 * r + 10 ≤ k → ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ ≤ (2 : ℝ) ^ (-(k : ℝ) / 2)
def SqrtSumSqLeOneAddInvPowSix : Prop :=
  ∀ b Pg A ε ε' : ℝ, 16 ≤ b → 0 ≤ Pg → Pg ≤ Real.exp (6 * (b ^ 7)⁻¹) →
    A ≤ (1 + (b ^ 7)⁻¹) * Real.exp ((b ^ 14)⁻¹) → ε ≤ (b ^ 14)⁻¹ → ε' ≤ (b ^ 14)⁻¹ →
    (√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2 ≤ 1 + (b ^ 6)⁻¹
def MainRowShape : Prop :=
  ∀ δ y z : ℝ, 0 ≤ δ → 0 ≤ y → 0 ≤ z → δ + y + z ≤ 1 →
    (1 + δ) * Real.exp y * Real.exp z ≤ 1 + 2 * (δ + y + z)
def SizeNumbers (k r f : ℕ) (b g1 g2 c Cn : ℝ) : Prop :=
  16 ≤ b ∧ 32 ≤ k ∧ f ≤ k ∧ 4 * r + 12 ≤ k ∧ ((k : ℝ) * b) ^ 8 ≤ g1 ∧ ((k : ℝ) * b) ^ 8 ≤ g2 ∧
  70 * Real.log b ≤ k ∧ 1 ≤ 5 * c * f * Real.log k ∧
  8 * (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) ≤ k
def PairBound : Prop :=
  PairBoundAbstract → NormSqBoundOfEqualIota → GramSumLeOfPosSemidef → PairSplit → SubFamily → NumPrice → NumExp → NumDens →
  NumLoops → NumNG → NGExponent → SqrtSumSqLeOneAddInvPowSix →
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Terms τ Rw I H H₁)
    (k r f : ℕ) (b g1 g2 c Cn δ e1 dd : ℝ), SizeNumbers k r f b g1 g2 c Cn → 0 ≤ dd →
    0 ≤ δ → δ ≤ (b ^ 7)⁻¹ → 0 ≤ e1 → e1 ≤ Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹) →
    X.AbsConv → (X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) →
    X.GGBound ((1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f) → X.RowOrth → X.CorankPos → X.IdZero →
    X.RowBig (Real.exp (-(c * k * f * Real.log k))) dd →
    X.RowNotScalar (Real.exp (-(c * k * f * Real.log k))) dd →
    X.RowMain ((1 + δ) * e1) dd →
    X.RowNG (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
      Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b)) dd →
    ‖X.K0‖ ^ 2 ≤ (1 + (b ^ 6)⁻¹) * dd
structure Place (E : Type) [Field E] where

  K : Type
  [cr : CommRing K]
  [top : TopologicalSpace K]
  [tr : IsTopologicalRing K]

  R : Subring K

  ψ : AddChar K ℂ
  datum : A5.LocalDatum K R ψ
  char0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)

  σ : E →+* K
attribute [instance] Place.cr Place.top Place.tr
section places
variable {E : Type} [Field E]
def SameKernels (S S' : J.LocSys E (TB.Pt E)) (Y : Finset (TB.Pt E)) : Prop :=
  (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y, S.N t t' h h' = S'.N t t' h h') ∧
  (∀ h ∈ Y, ∀ h' ∈ Y, S.B h h' = S'.B h h') ∧ S.L = S'.L ∧ S.L' = S'.L'
def IsPull (S : J.LocSys E (TB.Pt E)) (Y : Finset (TB.Pt E)) (s : ℕ) (un : Bool) : Prop :=
  ∃ (p : Place E) (u : p.Kˣ) (η : TB.Pt E → A5.Point p.K) (m : ℕ) (d : E → ℂ),
    (∀ h ∈ Y, (η h).1.sum = m) ∧ (∀ t, ‖d t‖ = 1) ∧ (un = true → ∀ h ∈ Y, A5.InGLR p.R (η h)) ∧
    SameKernels S (J.phaseSys d (J.pullSys p.R p.ψ s p.σ u η fun _ _ _ => 0)) Y
def IsTopSys (S : J.LocSys E (TB.Pt E)) (Y : Finset (TB.Pt E)) (un : Bool) : Prop :=
  ∃ (p : Place E) (u : p.Kˣ) (τ₀ : p.K) (η : TB.Pt E → A5.Point p.K) (m : ℕ),
    (∀ h ∈ Y, (η h).1.sum = m) ∧ (un = true → (∀ h ∈ Y, A5.InGLR p.R (η h)) ∧ τ₀ ∈ p.R) ∧
    ∀ Θ : p.K → A5.Point p.K → A5.Point p.K → ℂ, (∀ x, ∀ r ∈ p.R, Θ (x + r) = Θ x) →
      (∀ (c : p.Kˣ) (h h' : A5.Point p.K), h.1.sum = m → h'.1.sum = m →
        Θ (c : p.K) h h' = A5.Ns p.R p.ψ 1 h h' c c) →
      SameKernels S (J.topSys p.R p.ψ p.σ u τ₀ η Θ) Y
def IsOut (S : J.LocSys E (TB.Pt E)) (Y : Finset (TB.Pt E)) (s : ℕ) (tp : Prop) : Prop :=
  (∀ h ∈ Y, ∀ h' ∈ Y, S.B h h' = 1) ∧
  ∀ t t' : E, t ≠ 0 → t' ≠ 0 →
    ∃ (Q : Type) (_ : Fintype Q) (F : Q → J.LocSys E (TB.Pt E)),
      (∀ q, (tp ∧ IsTopSys (F q) Y true) ∨ (¬ tp ∧ IsPull (F q) Y s true)) ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, S.N t t' h h' = ∏ q, (F q).N t t' h h') ∧
      ((∀ q, t ∈ (F q).L) → t ∈ S.L) ∧ ((∀ q, t⁻¹ - t'⁻¹ ∈ (F q).L') → t⁻¹ - t'⁻¹ ∈ S.L')
def LocalModel {W : Type} (D : TB.Data E W) : Prop :=
  (∀ (i : ℕ) (Y : Finset (TB.Pt E)),
    ∃ (P : Type) (_ : Fintype P) (pl : P → Place E) (η : ∀ p, TB.Pt E → A5.Point (pl p).K)
      (cl : P → TB.Pt E → Option E) (d : P → TB.Pt E → ℂ) (a : TB.Pt E → ℝ),
      ∀ x ∈ Y, ∀ y ∈ Y, D.Kr i x y = (a x : ℂ) * a y *
        ∏ p, if cl p x = cl p y then
          d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y) else 0) ∧
  (∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) →
    ∃ (P : Type) (_ : Fintype P) (S : P → J.LocSys E (TB.Pt E)) (a : TB.Pt E → ℝ),
      (∀ p, ((i = D.r + 1 ∧ s = 1) ∧ IsTopSys (S p) Y false) ∨
        (¬ (i = D.r + 1 ∧ s = 1) ∧ IsPull (S p) Y s false) ∨ IsOut (S p) Y s (i = D.r + 1 ∧ s = 1)) ∧
      (∀ t t', t ≠ 0 → t' ≠ 0 → ∀ h ∈ Y, ∀ h' ∈ Y,
        (J.sysOf D i s).N t t' h h' = (J.scaleSys a (J.prodSys S)).N t t' h h') ∧
      (∀ h ∈ Y, ∀ h' ∈ Y, (J.sysOf D i s).B h h' = (J.scaleSys a (J.prodSys S)).B h h') ∧
      (J.sysOf D i s).L = ⨅ p, (S p).L ∧ (⨅ p, (S p).L') ≤ (J.sysOf D i s).L') ∧
  (∀ (h h' : TB.Pt E) (t t' : E), TB.level h = D.r → TB.level h' = D.r → t ≠ 0 → t' ≠ 0 → t ≠ t' →
    D.Kr (D.r + 1) (TB.join h 1 t) (TB.join h' 1 t') = 0) ∧
  (∀ i, 1 ≤ i → i ≤ D.r + 1 → D.e i = 0)
def PoissonInput {W : Type} (D : TB.Data E W) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : MeasurableSpace V)
    (_ : BorelSpace V) (_ : FiniteDimensional ℝ V) (ι : Type) (_ : Fintype ι) (π : ι → V →L[ℝ] ℂ)
    (Λ : ℕ → Submodule ℤ V) (_ : ∀ i, DiscreteTopology (Λ i)) (_ : ∀ i, IsZLattice ℝ (Λ i))
    (emb : ℕ → E →+ V) (dmap : ℕ → E → V),
    (Function.Bijective fun (c : V) (v : ι) => π v c) ∧
    J.Frames D.r (fun i => D.La i 1) D.Lad Λ emb dmap ∧ J.WaveFn D π Λ emb dmap
def RealInputs {W : Type} (D : TB.Data E W) (C₄ jn : ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) : Prop :=
  D.GramPSD ∧ D.WordsPos ∧ D.EstWave ∧ PoissonInput D ∧ D.EstLift ∧ D.EstBlock C₄ ∧ D.EstE jn ∧
  D.Cutoff Vt
def RowsInput {W : Type} (D : TB.Data E W) (sd : ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) {P : Type} [Fintype P]
    (B : S3.MassData P) : Prop :=
  (∀ ρ p, c ρ p ≠ 0 → TB.IsPt p (D.r + 1)) ∧
  (∀ Y : Finset (TB.Pt E), (∀ p ∈ Y, TB.IsPt p (D.r + 1)) → ∀ R : Finset ℕ,
    TB.PSDOn Y (fun p q => (sd : ℂ) * D.Kr (D.r + 1) p q - ∑ ρ ∈ R, c ρ p * conj (c ρ q))) ∧
  (∀ ρ, Summable fun p : TB.Pt E => ‖c ρ p‖ * ‖Vt p‖) ∧
  (∀ M : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ M) →
    B.c0 * B.c0' * B.KV ≤ B.n0c * M) ∧
  0 ≤ B.KV ∧ B.supdens = sd
end places
def DensInput (k r f : ℕ) (sd : ℝ) : Prop :=
  2 * r + 2 + f + 5 ≤ k ∧
  ∃ (P : Type) (q : P → ℝ) (l : P → ℕ), (∀ p, (l p).Prime ∧ ((l p : ℕ) : ℝ) ≤ q p) ∧
    (∀ (m : ℕ) (S : Finset P), (∀ p ∈ S, l p = m) → S.card ≤ f) ∧
    ∀ x : ℝ, x < sd → ∃ S : Finset P, x ≤ ∏ p ∈ S, Real.exp (4 * (q p ^ (k - 2 * r - 2))⁻¹)
def MassDataHyp {P : Type} [Fintype P] (B : S3.MassData P) : Prop :=
  B.Pos ∧ B.InForm ∧ B.InMass ∧ B.InJacMod ∧ B.InNu ∧ B.InInfinity ∧ B.InVolumes ∧ B.InLevelS ∧
  B.InMasses ∧ B.InColumns ∧ B.InOrdinary ∧ B.InTyped ∧ B.InIndices
def LocalCores : Prop :=
  J.PSDAgree ∧ J.SchurProduct ∧ J.ProductDomination ∧ J.DiagScale ∧ J.DiagPhase ∧ J.BlockDiagPSD ∧
  J.ProductLemma ∧ J.ScaleOk ∧ J.PhaseOk ∧ J.OutsideSysOk ∧ J.OutsideDomination ∧ J.LocalPullback ∧
  J.LocalUnitHeads ∧ J.TopPullback ∧ J.TopUnitHeads ∧ J.GlobalOfLocal ∧ J.UniformMajorantOn ∧
  J.AxiomsFromSystems ∧ J.AxiomsFromFamilies ∧ J.KernelOfLocal ∧ J.LocalKernelPSD ∧
  TC.DomMinOfText ∧ TC.DomAfterOfLocal ∧
  A5.A2 ∧ A5.KpGram ∧ A5.BaseKernelOne ∧ A5.SingleBlockParseval ∧ A5.Th1Eq ∧ A5.SingleBlockThetaProps ∧ A5.NsSupport ∧
  A5.NsBlockDiag ∧ A5.LemmaAAssemble
def GlobalCores : Prop :=
  TC.TheoremAAfter ∧ TC.RecursionWithDens ∧ TC.DomScaleTop ∧ TC.SumBoundMax ∧ TC.RecHypScaleTop ∧
  TC.DensSum ∧ TC.DensLeTwo ∧ TC.DensSize ∧ TC.DensChain ∧
  F7.PoissonStepText ∧ J.PoissonJoint ∧ J.PoissonStepJoint ∧
  Formalism.SA.C.BoxSum ∧ S6.LatticesGeneral ∧ S6.IdealsMatch ∧ S6.NormIdl ∧ S6.DegreeFacts ∧
  J.FrameProducts ∧ J.XIsLamOne ∧ J.LatticeSumsJoint ∧ J.InstSizes ∧ J.InstLatticeSums ∧
  Sz.SizesMain ∧ J.SizesToRecursion ∧ J.GlobPositive ∧ S3.MainTheorem ∧ J.FormGivesMain
def EnergyLink {P : Type} [Fintype P] (B : S3.MassData P) (jn sd C Th : ℝ) (r f : ℕ) : Prop :=
  B.IntN = jn ∧ B.e1 = max sd 1 ∧ B.δ = C * ((r : ℝ) + 1) * (C / Th) ^ f
def PullLatticeOrdinary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∉ P →
    ∀ (K : Type) [CommRing K] (R : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ S6.locAt E P (S6.zsub E 1) ↔ σ x ∈ R) →
      ∀ ω : E,
        (∀ t : E, t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 ν)) ↔ ω * t ∈ S6.locAt E P (S6.zsub E 1)) →
        (∀ x : E, x ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 (-ν))) ↔
          ω⁻¹ * x ∈ S6.locAt E P (S6.zsub E 1)) →
        ∀ (u : Kˣ) (α : Type) (ψ : AddChar K ℂ) (η : α → A5.Point K)
          (Θ : K → A5.Point K → A5.Point K → ℂ), (u : K) = σ ω →
          ∀ t : E,
            (t ∈ (J.pullSys R ψ s σ u η Θ).L ↔ t ∈ S6.locAt E P (S6.perLat E g ν s)) ∧
            (t ∈ (J.pullSys R ψ s σ u η Θ).L' ↔ t ∈ S6.locAt E P (S6.liftLat E g ν s))
def LatticeLink : Prop :=
  J.IntersectionOfLocal ∧ J.LatticeOfLocal ∧ S6.TwIsFLattice ∧ J.PullLatticeTyped ∧ J.PullLatticeTypedUnit ∧
  J.PullLiftTyped ∧ J.PullLiftTypedUnit ∧ PullLatticeOrdinary
def AxiomsOfLocalModel : Prop :=
  LocalCores → (∀ s, 1 ≤ s → A5.A13 s) →
  ∀ (E W : Type) [Field E] (D : TB.Data E W), LocalModel D →
    TC.KrPSD D ∧ D.KernelSupport ∧ TC.EBounds D ∧ TC.DomAfter D
def MainRow : Prop :=
  LocalCores → GlobalCores → LatticeLink → AxiomsOfLocalModel → A5.ThetaExistsStep → ∀ C₄ Cthr : ℝ, 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (bb Cp Cf Th : ℝ)
      (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → J.SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      S6.Unram E → J.Inst D e G CA de de' T T' l → LocalModel D →
      ∀ (jn : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) (sd : ℝ),
        RealInputs D C₄ jn Vt → DensInput G.k G.r G.f sd →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), RowsInput D sd Vt c B → MassDataHyp B →
          EnergyLink B jn sd C Th D.r D.f →
          B.Gam1 * B.Sig ≤ (1 + B.δ) * B.e1 * (B.d * B.d' / B.Dstar) ∧
            0 ≤ B.δ ∧ B.δ ≤ (bb ^ 7)⁻¹ ∧ 1 ≤ B.e1 ∧
            B.e1 ≤ Real.exp (12 * (G.f : ℝ) * ((2 : ℝ) ^ (G.k - 2 * G.r - 2))⁻¹)
def LoopsInput {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁) (A C : ℝ) (k r f : ℕ)
    (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ) : Prop :=
  X.pairAbs (X.big X.nzSet ∪ X.nsc X.genSet) ≤
    A * (∑ s ∈ Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
      Gam ^ 2 * ∑ s ∈ Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi +
      C ^ f * Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
        Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
        Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f))) * dd
def LoopsJoint : Prop :=
  Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum → Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum → Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound → Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt →
  Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' → ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ,
  ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁) (k r f : ℕ)
    (A b g v NT Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ), 1 ≤ A →
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k (2 * r + 2) f b g v NT Gam →
    Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k (2 * r + 2) f b v NT Xi →
    6 * Real.log (3 * A) ≤ (k : ℝ) * f * Real.log k → 0 ≤ dd →
    LoopsInput X A C k r f b g v Gam Xi dd →
    X.RowLoops (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd
def Link {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁) {P : Type} [Fintype P]
    (B : S3.MassData P) {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de : ℕ → ℝ) (T : ℕ) (du du' : ℝ) : Prop :=
  X.Gam1 = B.Gam1 ∧ X.pairSum (X.sc X.genSet) = B.Gam1 * B.Sig ∧
  (∃ typ : P ≃ Bool × ι, ∀ p, B.g p = if (typ p).1 then (G.g1 : ℝ) else (G.g2 : ℝ)) ∧
  B.d = du ∧ B.d' = du' ∧ B.Dstar = (G.size de T du).Dstar
def SplitInputs {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁) (Pg : ℝ) : Prop :=
  X.AbsConv ∧ (X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) ∧ X.GGBound Pg ∧ X.RowOrth ∧
  X.CorankPos ∧ X.IdZero ∧
  ∀ i, X.GG i i = ((X.Gam1 : ℝ) : ℂ)
def PairBoundFromLocal : Prop :=
  MainRow → PairBound → LocalCores → GlobalCores → LatticeLink → AxiomsOfLocalModel → A5.ThetaExistsStep →
  PairBoundAbstract → NormSqBoundOfEqualIota → GramSumLeOfPosSemidef → PairSplit → SubFamily → NumPrice → NumExp → NumDens →
  NumLoops → NumNG → NGExponent → SqrtSumSqLeOneAddInvPowSix → ∀ C₄ Cthr : ℝ, 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (bb Cp Cf Th : ℝ)
      (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → J.SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      S6.Unram E → J.Inst D e G CA de de' T T' l → LocalModel D →
      ∀ (jn : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) (sd : ℝ),
        RealInputs D C₄ jn Vt → DensInput G.k G.r G.f sd →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), RowsInput D sd Vt c B → MassDataHyp B →
          EnergyLink B jn sd C Th D.r D.f →
          ∀ (τ Rw I HS H₁ : Type) [Fintype I] [NormedAddCommGroup HS] [InnerProductSpace ℂ HS]
            [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
            (X : Terms τ Rw I HS H₁) (c5 Cn : ℝ),
            Link X B G de T du du' → SplitInputs X B.tt →
            SizeNumbers G.k G.r G.f bb G.g1 G.g2 c5 Cn →
            X.RowBig (Real.exp (-(c5 * G.k * G.f * Real.log G.k))) (du * du' / (G.size de T du).Dstar) →
            X.RowNotScalar (Real.exp (-(c5 * G.k * G.f * Real.log G.k)))
              (du * du' / (G.size de T du).Dstar) →
            X.RowNG (((2 : ℝ) ^ (G.k - 2 * G.r - 5))⁻¹ *
              Real.exp (Cn * ((2 * G.r + 2 : ℕ) : ℝ) ^ 5 * G.f * Real.log bb))
              (du * du' / (G.size de T du).Dstar) →
            ‖X.K0‖ ^ 2 ≤ (1 + (bb ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar)
end
end Formalism.FourierDecayAlt.PB


