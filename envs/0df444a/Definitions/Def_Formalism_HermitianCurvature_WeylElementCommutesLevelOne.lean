-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- name    : Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:30.316323+00:00
-- url     : https://prove2.me/theorems/718c5fbd-4fec-4467-a7f4-a6f4795b4783
-- title:
--   Weyl Element Commutes Level One
-- statement:
--   Definitions and structural lemmas for Weyl Element Commutes Level One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/WeylElementCommutesLevelOne.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.B2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
structure IsClosedSubgroup {k r : ℕ} (U : Set (Mat k r)) : Prop where
  one_mem : (1 : Mat k r) ∈ U
  mul_mem : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U
  inv_mem : ∀ a ∈ U, a⁻¹ ∈ U
  unit : ∀ a ∈ U, IsUnit a.det
  closed : IsClosed U
def invM {k r : ℕ} (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)
def mulM {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := Matrix.of p.1 * Matrix.of p.2
def mulSet {k r : ℕ} (A B : Set (Mat k r)) : Set (Mat k r) := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
def HaarUnique : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ ν : Measure (Mt k r)), IsClosedSubgroup U → IsHaarOn U μ →
    ν Uᶜ = 0 → (∀ a ∈ U, ν.map (lmulM a) = ν) → (∀ K : Set (Mt k r), IsCompact K → ν K < ∞) →
    ∃ c : ℝ≥0, ν = c • μ
def HaarInv : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSubgroup U → IsHaarOn U μ → μ.map invM = μ
def HaarInvFromUnique : Prop := HaarUnique → HaarInv
def ConjHaar : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ : Measure (Mt k r)) (a : Mat k r), IsClosedSubgroup U → IsUnit a.det →
    (∀ u ∈ U, a * u * a⁻¹ ∈ U) → (∀ u ∈ U, a⁻¹ * u * a ∈ U) → IsHaarOn U μ → IsHaarOn U (μ.map (conjM a))
def CompactConj : Prop :=
  ∀ (k r : ℕ) (U K : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSubgroup U → IsClosedSubgroup K → IsCompact K →
    (∀ a ∈ K, ∀ u ∈ U, a * u * a⁻¹ ∈ U) → IsHaarOn U μ → ∀ a ∈ K, μ.map (conjM a) = μ
def CompactConjFromUnique : Prop := HaarUnique → ConjHaar → CompactConj
def SemiHaar : Prop :=
  ∀ (k r : ℕ) (A B : Set (Mat k r)) (μA μB : Measure (Mt k r)) (ρ : Mt k r → Mt k r),
    IsClosedSubgroup A → IsClosedSubgroup B → (∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) →
    IsClosed (mulSet A B) → Continuous ρ → (∀ a ∈ A, ∀ b ∈ B, ρ (a * b) = b) →
    IsHaarOn A μA → IsHaarOn B μB → (∀ b ∈ B, μA.map (conjM b) = μA) →
    IsClosedSubgroup (mulSet A B) ∧ IsHaarOn (mulSet A B) ((μA.prod μB).map mulM)
def levM (k r' : ℕ) (x : Mt k r') : Mt k (1 + r') := ιLev k 1 r' (Matrix.of x)
def LevHaar : Prop :=
  ∀ (k r' : ℕ) (U : Set (Mat k r')) (μ : Measure (Mt k r')), IsClosedSubgroup U → IsHaarOn U μ →
    IsClosedSubgroup (ιLev k 1 r' '' U) ∧ IsHaarOn (ιLev k 1 r' '' U) (μ.map (levM k r'))
def CompactHaarExists : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)), IsClosedSubgroup U → IsCompact U → ∃ μ : Measure (Mt k r), IsHaarOn U μ
def ShellInt : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (N : X → ℝ) (C d A : ℝ), Measurable N → (∀ᵐ x ∂μ, 1 ≤ N x) →
    0 ≤ d → (∀ R : ℝ, 1 ≤ R → μ {x | N x ≤ R} ≤ ENNReal.ofReal (C * R ^ d)) → d < A →
    (∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ) < ∞
def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}
def ClosedG : Prop := ∀ k r : ℕ, IsClosedSubgroup (GV k r)
def ClosedN : Prop := ∀ k r : ℕ, IsClosedSubgroup (Nset k r)
def ClosedW : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), IsClosedSubgroup (UWset k r z)
def ClosedWb : Prop := ∀ k r : ℕ, IsClosedSubgroup (UWb k r)
def CompactW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsCompact (UWset k r z)
def HaarGExists : Prop := ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsHaarOn (GV k r) μ
def HaarWbExists : Prop := ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsHaarOn (UWb k r) μ
def HaarWExists : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∃ μ : Measure (Mt k r), IsHaarOn (UWset k r z) μ
def HaarWFromCompact : Prop := CompactHaarExists → ClosedW → CompactW → HaarWExists
def ConjInvRaw : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    IsHaarOn (Nset k r) μN → ∀ h ∈ UWset k r z, μN.map (conjM h) = μN
def ConjInvAll : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq), ConjInv D
def AssembleConjInv : Prop :=
  CompactConj → ClosedN → ClosedW → CompactW → UWNormal → ConjInvRaw ∧ ConjInvAll
def a0 (r' : ℕ) : Fin (1 + r') := ⟨0, by omega⟩
def e0 (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) → ℂ := bvec (eI k (1 + r') (a0 r'))
def es0 (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) → ℂ := bvec (esI k (1 + r') (a0 r'))
def heisG (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) : Mat k (1 + r') :=
  1 - Matrix.vecMulVec (e0 k r') (fun j => herm (Hpk k (1 + r')) (bvec j) v) +
    Matrix.vecMulVec (v + b • e0 k r') (fun j => herm (Hpk k (1 + r')) (bvec j) (e0 k r'))
def hb (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : ℂ :=
  ((-(herm (Hpk k r') y y).re / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I
abbrev HPar (k r' : ℕ) := (Fin (2 * r' + k + 1) → ℂ) × ℝ
def heis0 (k r' : ℕ) (x : HPar k r') : Mat k (1 + r') := heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2)
def Hset (k r' : ℕ) : Set (Mat k (1 + r')) := Set.range (heis0 k r')
def μHeis (k r' : ℕ) : Measure (Mt k (1 + r')) := (volume : Measure (HPar k r')).map fun x => (heis0 k r' x : Mt k (1 + r'))
def HeisAct : Prop :=
  ∀ (k r' : ℕ) (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ),
    heisG k r' v b *ᵥ u = u - herm (Hpk k (1 + r')) u v • e0 k r' + herm (Hpk k (1 + r')) u (e0 k r') • (v + b • e0 k r')
def HeisMem : Prop := ∀ (k r' : ℕ) (x : HPar k r'), heis0 k r' x ∈ Nset k (1 + r')
def HeisMul : Prop :=
  ∀ (k r' : ℕ) (x x' : HPar k r'),
    heis0 k r' x * heis0 k r' x' = heis0 k r' (x.1 + x'.1, x.2 + x'.2 - (herm (Hpk k r') x'.1 x.1).im)
def HeisInv : Prop := ∀ (k r' : ℕ) (x : HPar k r'), (heis0 k r' x)⁻¹ = heis0 k r' (-x.1, -x.2)
def HeisClosed : Prop := ∀ k r' : ℕ, Function.Injective (heis0 k r') ∧ IsClosedSubgroup (Hset k r')
def HeisHaar : Prop := ∀ k r' : ℕ, IsHaarOn (Hset k r') (μHeis k r')
def HeisConjLev : Prop :=
  ∀ (k r' : ℕ), ∀ g₁ ∈ GV k r', ∀ x : HPar k r',
    ιLev k 1 r' g₁ * heis0 k r' x * (ιLev k 1 r' g₁)⁻¹ = heis0 k r' (g₁ *ᵥ x.1, x.2)
def HeisConjLevMeas : Prop :=
  ∀ (k r' : ℕ), ∀ g₁ ∈ GV k r', (μHeis k r').map (conjM (ιLev k 1 r' g₁)) = μHeis k r'
def NDecomp : Prop := ∀ k r' : ℕ, Nset k (1 + r') = mulSet (Hset k r') (ιLev k 1 r' '' Nset k r')
def NRecHaar : Prop :=
  ∀ (k r' : ℕ) (μ' : Measure (Mt k r')), IsHaarOn (Nset k r') μ' →
    IsHaarOn (Nset k (1 + r')) (((μHeis k r').prod (μ'.map (levM k r'))).map mulM)
def NBase : Prop := ∀ k : ℕ, Nset k 0 = {1}
def HaarNExists : Prop := ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsHaarOn (Nset k r) μ
def AssembleNRec : Prop :=
  SemiHaar → LevHaar → ClosedN → HeisClosed → HeisHaar → HeisConjLev → HeisConjLevMeas → NDecomp → NRecHaar
def AssembleHaarN : Prop := NRecHaar → NBase → HaarNExists
def DilHeis : Prop :=
  ∀ (k r' : ℕ) (t : ℝ), t ≠ 0 → ∀ x : HPar k r',
    aDil k (1 + r') t * heis0 k r' x * (aDil k (1 + r') t)⁻¹ =
      heis0 k r' (((t ^ (1 + r') : ℝ) : ℂ) • (aDil k r' t *ᵥ x.1), t ^ (2 * (1 + r')) * x.2)
def DilLev : Prop :=
  ∀ (k r' : ℕ) (t : ℝ), t ≠ 0 → ∀ g₁ : Mat k r',
    aDil k (1 + r') t * ιLev k 1 r' g₁ * (aDil k (1 + r') t)⁻¹ = ιLev k 1 r' (aDil k r' t * g₁ * (aDil k r' t)⁻¹)
def DilHeisMeas : Prop :=
  ∀ (k r' : ℕ) (t : ℝ), 0 < t →
    (μHeis k r').map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ (2 * (2 * r' + k + 2) * (1 + r')))⁻¹) • μHeis k r'
def KapRec : Prop := ∀ k r' : ℕ, kap k (1 + r') = 2 * (2 * r' + k + 2) * (1 + r') + kap k r'
def DilJacRaw : Prop :=
  ∀ (k r : ℕ) (μN : Measure (Mt k r)), IsHaarOn (Nset k r) μN → ∀ t : ℝ, 0 < t →
    μN.map (conjM (aDil k r t)) = ENNReal.ofReal ((t ^ kap k r)⁻¹) • μN
def DilJacAll : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq), DilJac D
def AssembleDilJac : Prop :=
  HaarUnique → ClosedN → NRecHaar → NBase → HaarNExists → DilLev → DilHeisMeas → KapRec → DilJacRaw ∧ DilJacAll
def IntF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μG μW μN μW' : Measure (Mt k r)) : Prop :=
  ∀ f : Mt k r → ℝ≥0∞, Measurable f →
    (∫⁻ g, f g ∂μG) = ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
        ∫⁻ p : SS k r, f (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW.prod μN).prod (μW'.prod μN))
structure IsMeasData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μG μW μN μW' : Measure (Mt k r)) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarG : IsHaarOn (GV k r) μG
  haarW : IsHaarOn (UWset k r z) μW
  haarN : IsHaarOn (Nset k r) μN
  haarW' : IsHaarOn (UWset k r z') μW'
  sec : IsSection k r z z' μsec
def w0 (k r' : ℕ) (c : ℂ) : Mat k (1 + r') := fun i j =>
  if i.val = 0 ∧ j.val = 2 * (1 + r') + k then (star c)⁻¹
  else if i.val = 2 * (1 + r') + k ∧ j.val = 0 then c
  else if i = j ∧ 0 < i.val ∧ i.val < 2 * (1 + r') + k then 1 else 0
def oneStep (k r' : ℕ) (x : HPar k r') (c : ℂ) (g₁ : Mat k r') (x' : HPar k r') : Mat k (1 + r') :=
  (heis0 k r' x)⁻¹ * w0 k r' c * ιLev k 1 r' g₁ * heis0 k r' x'
def OneStepMem : Prop :=
  ∀ (k r' : ℕ) (x x' : HPar k r') (c : ℂ), c ≠ 0 → ∀ g₁ ∈ GV k r',
    oneStep k r' x c g₁ x' ∈ GV k (1 + r') ∧
      herm (Hpk k (1 + r')) (oneStep k r' x c g₁ x' *ᵥ e0 k r') (e0 k r') = c
def OneStepCoord : Prop :=
  ∀ (k r' : ℕ), ∀ g ∈ GV k (1 + r'), herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0 →
    ∃! p : HPar k r' × Mat k r' × HPar k r', p.2.1 ∈ GV k r' ∧
      g = oneStep k r' p.1 (herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r')) p.2.1 p.2.2
def coneMeas (k r' : ℕ) : Measure (Fin (2 * (1 + r') + k + 1) → ℂ) :=
  (((volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1)))).prod
      (volume : Measure (HPar k r'))).map
    fun p => p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')
def ConeInv : Prop :=
  ∀ (k r' : ℕ), ∀ g ∈ GV k (1 + r'), (coneMeas k r').map (fun x => g *ᵥ x) = coneMeas k r'
def ConeFinite : Prop :=
  ∀ (k r' : ℕ) (K : Set (Fin (2 * (1 + r') + k + 1) → ℂ)), IsCompact K → coneMeas k r' K < ∞
def P1set (k r' : ℕ) : Set (Mat k (1 + r')) := {g | g ∈ GV k (1 + r') ∧ g *ᵥ e0 k r' = e0 k r'}
def StabDecomp : Prop := ∀ k r' : ℕ, P1set k r' = mulSet (Hset k r') (ιLev k 1 r' '' GV k r')
def StabHaar : Prop :=
  ∀ (k r' : ℕ) (μG₁ : Measure (Mt k r')), IsHaarOn (GV k r') μG₁ →
    IsClosedSubgroup (P1set k r') ∧ IsHaarOn (P1set k r') (((μHeis k r').prod (μG₁.map (levM k r'))).map mulM)
def AssembleStab : Prop :=
  SemiHaar → LevHaar → ClosedG → HeisClosed → HeisHaar → HeisConjLev → HeisConjLevMeas → StabDecomp → StabHaar
def OneStepInt : Prop :=
  ∀ (k r' : ℕ) (μG : Measure (Mt k (1 + r'))) (μG₁ : Measure (Mt k r')),
    IsHaarOn (GV k (1 + r')) μG → IsHaarOn (GV k r') μG₁ →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : Mt k (1 + r') → ℝ≥0∞, Measurable f →
      (∫⁻ g, f g ∂μG) = (C : ℝ≥0∞) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁)
def AssembleOneStep : Prop :=
  HaarUnique → HaarInv → ClosedG → HeisAct → HeisInv → OneStepMem → OneStepCoord → ConeInv → ConeFinite → StabDecomp →
    StabHaar → OneStepInt
def OneStepNull : Prop :=
  ∀ (k r' : ℕ) (μG : Measure (Mt k (1 + r'))), IsHaarOn (GV k (1 + r')) μG →
    μG {g | herm (Hpk k (1 + r')) (Matrix.of g *ᵥ e0 k r') (e0 k r') = 0} = 0
def OneStepNullFromInt : Prop := OneStepInt → HaarGExists → OneStepMem → OneStepNull
def cWeight (k r : ℕ) (c : Fin r → ℂ) : ℝ := ∏ a : Fin r, ‖c a‖ ^ (2 * (Mdim k r a - 2))
def BigCellRec : Prop :=
  ∀ (k r' : ℕ) (c : Fin (1 + r') → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    bigCell k (1 + r') c μ = w0 k r' (c (a0 r')) * ιLev k 1 r' (bigCell k r' (fun a => c (Fin.natAdd 1 a)) μ)
def WeylElementCommutesLevelOne : Prop :=
  ∀ (k r' : ℕ) (c : ℂ) (g₁ : Mat k r'), w0 k r' c * ιLev k 1 r' g₁ = ιLev k 1 r' g₁ * w0 k r' c
def UWbRec : Prop := ∀ k r' : ℕ, UWb k (1 + r') = ιLev k 1 r' '' UWb k r'
def IterInt : Prop :=
  ∀ (k r : ℕ) (μG μN μb : Measure (Mt k r)), IsHaarOn (GV k r) μG → IsHaarOn (Nset k r) μN → IsHaarOn (UWb k r) μb →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      (∫⁻ g, f g ∂μG) = (C : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) *
        ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
          f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb)
def AssembleIter : Prop :=
  OneStepInt → HaarUnique → HaarInv → LevHaar → ClosedG → ClosedN → ClosedWb → HaarGExists → HaarNExists → HaarWbExists →
    NRecHaar → NBase → HeisConjLevMeas → BigCellRec → WeylElementCommutesLevelOne → UWbRec → IterInt
def embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) then 1 else 0
def BigCellFactor : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    bigCell k r c μ = bigCell k r c 1 * embWb k r μ ∧ bigCell k r c μ = embWb k r μ * bigCell k r c 1
def UWbFacts : Prop :=
  ∀ k r : ℕ, UWb k r = embWb k r '' {μ | μᴴ * Hb k * μ = Hb k} ∧
    (∀ z : Fin (2 * r + k + 1) → ℂ, UWset k r z ⊆ UWb k r) ∧
    ∀ (c : Fin r → ℂ), ∀ m ∈ UWb k r, m * bigCell k r c 1 = bigCell k r c 1 * m
def zWeight (k : ℕ) (T T' : ℝ) (ζ : ℂ) : ℝ :=
  if T * T' ≤ Complex.normSq ζ then (Complex.normSq ζ - T * T') ^ (k - 1) else 0
def WeightFactor : Prop :=
  ∀ (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ), bcWeight k r T T' q = cWeight k r q.1 * zWeight k T T' q.2
def hypMeas (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μW : Measure (Mt k r)) : Measure (Fin (2 * r + k + 1) → ℂ) :=
  (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
    fun p => (Matrix.of p.2)⁻¹ *ᵥ (embWb k r (μsec p.1) *ᵥ z')
def HypInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μW : Measure (Mt k r)), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsSection k r z z' μsec → IsHaarOn (UWset k r z) μW →
    ∀ m ∈ UWb k r, (hypMeas k r z z' μsec μW).map (fun v => m *ᵥ v) = hypMeas k r z z' μsec μW
def RankOneMem : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    inWb k r z → inWb k r z' → IsSection k r z z' μsec →
    ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z',
      h⁻¹ * embWb k r (μsec ζ) * h' ∈ UWb k r ∧
        herm (Hpk k r) ((h⁻¹ * embWb k r (μsec ζ) * h') *ᵥ z') z = ζ
def RankOneCoord : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ m ∈ UWb k r, Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (m *ᵥ z') z) →
      ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
        m = h⁻¹ * embWb k r (μsec (herm (Hpk k r) (m *ᵥ z') z)) * h'
def RankOneInt : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μb μW μW' : Measure (Mt k r)), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsSection k r z z' μsec → IsHaarOn (UWb k r) μb → IsHaarOn (UWset k r z) μW → IsHaarOn (UWset k r z') μW' →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      (∫⁻ m, f m ∂μb) = (C : ℝ≥0∞) * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * embWb k r (μsec ζ) * Matrix.of p.2) ∂(μW.prod μW')
def WbFromDiag : Prop :=
  Formalism.REAL.UJEmb → Formalism.REAL.Unimodular → Formalism.REAL.BallFinite → UWbFacts → HaarWbExists
def AssembleRankOne : Prop :=
  HaarUnique → ClosedWb → ClosedW → CompactW → UWbFacts → RankOneMem → RankOneCoord → HypInv → RankOneInt
def IntConst : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μG μW μN μW' : Measure (Mt k r)), IsMeasData k r z z' μsec μG μW μN μW' →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      (∫⁻ g, f g ∂μG) = (C : ℝ≥0∞) * ∫⁻ q : (Fin r → ℂ) × ℂ,
        ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
          ∫⁻ p : SS k r, f (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW.prod μN).prod (μW'.prod μN))
def AssembleInt : Prop :=
  IterInt → RankOneInt → ConjInvRaw → HaarWbExists → BigCellFactor → UWbFacts → WeightFactor → IntConst
def IntNorm : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μG μW μN μW' : Measure (Mt k r)), IsMeasData k r z z' μsec μG μW μN μW' →
    ∃! c : ℝ≥0, 0 < c ∧ IntF k r z z' μsec (c • μG) μW μN μW'
def IntNormFromConst : Prop := IntConst → IntNorm
def IntNormB : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq),
    ∃! c : ℝ≥0, 0 < c ∧ IntF k r D.z D.z' D.μsec (c • D.μG) D.μW D.μN D.μW'
def IntNormBFromNorm : Prop := IntNorm → IntNormB
def GNLower : Prop := ∀ (k r : ℕ), ∀ g ∈ GV k r, 1 ≤ gN g
def Ppos (k r : ℕ) : Mat k r := (1 / 2 : ℂ) • (1 + Hpk k r)
def Pneg (k r : ℕ) : Mat k r := (1 / 2 : ℂ) • (1 - Hpk k r)
def HSBlock : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ GV k r, gN g ^ 2 = ((2 * r + k + 1 : ℕ) : ℝ) + 4 * gN (Ppos k r * g * Pneg k r) ^ 2
def VolExact : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GV k r) μG →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      μG {g | gN (Matrix.of g) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) + 4 * ρ ^ 2} =
        (C : ℝ≥0∞) * ENNReal.ofReal (ρ ^ (2 * (k + r) * (r + 1)))
def VolSharp : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GV k r) μG →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → μG {g | gN (Matrix.of g) ≤ R} ≤ ENNReal.ofReal (C * R ^ (2 * ((k : ℝ) + r) * ((r : ℝ) + 1)))
def VolSharpFromExact : Prop := VolExact → VolSharp
def VolCrude : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GV k r) μG →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → μG {g | gN (Matrix.of g) ≤ R} ≤ ENNReal.ofReal (C * R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2))
def GFromDiag : Prop :=
  Formalism.REAL.UJEmb → Formalism.REAL.Unimodular → Formalism.REAL.BallFinite → Formalism.REAL.VolGrowth → HpkFacts → UHConj → HaarUnique → ClosedG →
    HaarGExists ∧ VolCrude
def GNIntSharp : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)) (A : ℝ), IsHaarOn (GV k r) μG → AB k r ≤ A →
    (∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂μG) < ∞
def GNIntCrude : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)) (A : ℝ), IsHaarOn (GV k r) μG → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A →
    (∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂μG) < ∞
def GNIntSharpFromVol : Prop := ShellInt → GNLower → VolSharp → GNIntSharp
def GNIntCrudeFromVol : Prop := ShellInt → GNLower → VolCrude → GNIntCrude
def CCFromGN : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    (∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG) < ∞ → CCIntegrable D A
def CCIntAll : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    AB k r ≤ A → CCIntegrable D A
def CCIntCrudeAll : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A → CCIntegrable D A
def CCIntDouble : Prop :=
  XiExists →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    2 * AB k r ≤ A → CCIntegrable D A
def AssembleCCInt : Prop := CCFromGN → GNIntSharp → CCIntAll
def AssembleCCIntCrude : Prop := CCFromGN → GNIntCrude → CCIntCrudeAll
def ZExists : Prop :=
  ∀ k r : ℕ, inWb k r (bvec (wI k r (Fin.last k))) ∧ Tz k r (bvec (wI k r (Fin.last k))) = 1
def ChiExists : Prop :=
  ∃ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ tsupport χ ⊆ Set.Ioo (1 / 2) 2 ∧ (∫ t, χ t) = 1
def RealPlaceDataExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsCRepOn (UWset k r z) π → IsCRepOn (UWset k r z') π' →
    (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset k r z', ∀ v, ‖π' h v‖ = ‖v‖) →
    ContinuousOn π (UWset k r z) → ContinuousOn π' (UWset k r z') →
    ∃ D : RealPlaceData k r Wp Wq, D.z = z ∧ D.z' = z' ∧ D.π = π ∧ D.π' = π' ∧ IntFormula D
def RealPlaceDataNonempty : Prop := ∀ k r : ℕ, 1 ≤ k → ∃ D : RealPlaceData k r ℂ ℂ, IntFormula D
def AssembleExists : Prop :=
  HaarGExists → HaarWExists → HaarNExists → SectionExists → ChiExists → IntNorm → ZExists →
    RealPlaceDataExists ∧ RealPlaceDataNonempty
def LemmaBNorm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), AB k r ≤ A → IntFormula D → PairingContinuityBound D A ∧ PairingEqLimitPairing D A ∧ PairingAdjointness D A ∧ AdjointnessPolynomialCoefficients D A
def LemmaBNormFromParts : Prop := LemmaBClosed → ConjInvAll → DilJacAll → CCIntAll → LemmaBNorm
def LemmaBAny : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), AB k r ≤ A →
    ∃ c : ℝ≥0, 0 < c ∧ IntF k r D.z D.z' D.μsec (c • D.μG) D.μW D.μN D.μW' ∧
      PairingContinuityBound D A ∧
      (∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = ((c : ℝ) : ℂ) * betaInf D F F') ∧
      PairingAdjointness D A ∧ AdjointnessPolynomialCoefficients D A
def LemmaBAnyFromNorm : Prop := LemmaBNorm → IntNormB → LemmaBAny
def LemmaBCrude : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A → IntFormula D →
    PairingContinuityBound D A ∧ PairingEqLimitPairing D A ∧ PairingAdjointness D A ∧ AdjointnessPolynomialCoefficients D A
def LemmaBCrudeFromParts : Prop := LemmaBClosed → ConjInvAll → DilJacAll → CCIntCrudeAll → LemmaBCrude
def LemmaBDouble : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), 2 * AB k r ≤ A → IntFormula D → PairingContinuityBound D A ∧ PairingEqLimitPairing D A ∧ PairingAdjointness D A ∧ AdjointnessPolynomialCoefficients D A
def LemmaBDoubleFromParts : Prop :=
  (XiExists → LemmaBClosed) → ConjInvAll → DilJacAll → CCIntDouble → XiExists → LemmaBDouble
def LemmaBFromXi : Prop := XiExists → LemmaBNorm ∧ LemmaBAny
def LemmaBFromXiFromParts : Prop :=
  (XiExists → LemmaBClosed) → ConjInvAll → DilJacAll → CCIntAll → IntNormB → LemmaBFromXi
end Formalism.FourierDecayAlt.B2


