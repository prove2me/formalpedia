-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
-- name    : Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:59:15.211331+00:00
-- url     : https://prove2.me/theorems/03ffcc41-9d14-4980-97f0-fa0663d7422f
-- title:
--   Lower Block Normalised Bound From Components
-- statement:
--   Definitions and structural lemmas for Lower Block Normalised Bound From Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/LowerBlockNormalisedBoundFromComponents.lean

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.PairingProductCorollary
open Finset
open scoped ComplexOrder
noncomputable section
def cg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (a : Fin K) : ℝ :=
  ∑ i, |F7.lagCo (grid a) i|
def coProd {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.lagCo (grid a) (j a)
def qProd {K d : ℕ} (q : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, F7.qW q w (grid a (j a))
def nnProd {K d : ℕ} (nn : ℝ → ℝ) (h : ℝ) (grid : Fin K → Fin (d + 1) → ℝ)
    (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, nn (grid a (j a) + h)
def PSD {V : Type} [AddCommGroup V] [Module ℂ V] (R : F7.Sesq V) : Prop :=
  ∀ x, (R x x).im = 0 ∧ 0 ≤ (R x x).re
def Npair {V : Type} [AddCommGroup V] [Module ℂ V] (R : F7.Sesq V) (x : ℂ → V) (wt : ℂ → ℝ) (bw : ℝ)
    (t t' : ℂ) : ℂ :=
  ((wt t * wt t' / bw : ℝ) : ℂ) * R (x t) (x t')
def PairingGramBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (R : F7.Sesq V) (x : ℂ → V) (wt : ℂ → ℝ) (bw : ℝ),
    PSD R → 0 < bw → (∀ t, 0 ≤ wt t) → ∀ t t' : ℂ,
    ‖Npair R x wt bw t t'‖ ≤ Real.sqrt ((Npair R x wt bw t t).re * (Npair R x wt bw t' t').re)
def LiftLeadingCoefficientIdentity {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (e o W0 : ℂ)
    (W : (Fin K → Fin (d + 1)) → ℂ) : Prop :=
  (e * o) ^ K * W0 = ∑ j, ((coProd grid j : ℝ) : ℂ) * W j
def NodeDualityBound {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (q : ℝ → ℝ) (w : List (F7.WLetter ℝ))
    (W : (Fin K → Fin (d + 1)) → ℂ) (RL RV : (Fin K → Fin (d + 1)) → ℝ) : Prop :=
  ∀ j, ‖W j‖ ^ 2 ≤ RL j * RV j / qProd q w grid j
def UnnormalisedLiftBoundFromComponents : Prop :=
  ∀ (K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (q : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (e o W0 : ℂ)
    (W : (Fin K → Fin (d + 1)) → ℂ) (RL RV : (Fin K → Fin (d + 1)) → ℝ),
    (e = 1 ∨ e = -1) → (∀ j, 0 < qProd q w grid j) → (∀ j, 0 ≤ RL j ∧ 0 ≤ RV j) →
    LiftLeadingCoefficientIdentity grid e o W0 W → NodeDualityBound grid q w W RL RV →
    ‖o‖ ^ K * ‖W0‖ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j)
def LowerBlockNormalisedBoundFromComponents : Prop :=
  ∀ (K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (q nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (o W0 : ℂ)
    (RL RV : (Fin K → Fin (d + 1)) → ℝ) (wt wt' bw Qw BB : ℝ),
    (∀ a, Function.Injective (grid a)) →
    (∀ a i, 0 < q (grid a i) ∧ 0 < F7.qW q w (grid a i) ∧ 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1)) →
    (∀ a i, q (grid a i) ≤ Qw * F7.qW q w (grid a i)) →
    (∀ a i, nn (grid a i) * nn (grid a i + 1) / q (grid a i) ≤ BB ^ 2) →
    0 ≤ BB → 0 ≤ wt → 0 ≤ wt' → 0 < bw → (∀ j, 0 ≤ RL j ∧ 0 ≤ RV j) →
    ‖o‖ ^ K * ‖W0‖ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) →
    ‖o‖ ^ K * (wt * wt' / bw * ‖W0‖) ≤
      (∏ a, cg grid a) * (Real.sqrt Qw * BB) ^ K *
        ∑ j, F7.thGrid grid j *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2)
def LowerBlockLiftBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (R : F7.Sesq V) (x : ℂ → V) (ex K d : ℕ)
    (grid : Fin K → Fin (d + 1) → ℝ) (q nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (e t t' : ℂ)
    (W : (Fin K → Fin (d + 1)) → ℂ) (RL RV : (Fin K → Fin (d + 1)) → ℝ) (bw Qw BB : ℝ),
    PSD R → 0 < bw → t ≠ 0 → t' ≠ 0 → (e = 1 ∨ e = -1) →
    (∀ a, Function.Injective (grid a)) →
    (∀ a i, 0 < q (grid a i) ∧ 0 < F7.qW q w (grid a i) ∧ 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1)) →
    (∀ a i, q (grid a i) ≤ Qw * F7.qW q w (grid a i)) →
    (∀ a i, nn (grid a i) * nn (grid a i + 1) / q (grid a i) ≤ BB ^ 2) → 0 ≤ BB →
    (∀ j, 0 ≤ RL j ∧ 0 ≤ RV j) →
    LiftLeadingCoefficientIdentity grid e (1 / t - 1 / t') (R (x t) (x t')) W → NodeDualityBound grid q w W RL RV →
    (‖Npair R x (fun u => ‖u‖ ^ ex) bw t t'‖ ≤
      Real.sqrt ((Npair R x (fun u => ‖u‖ ^ ex) bw t t).re * (Npair R x (fun u => ‖u‖ ^ ex) bw t' t').re)) ∧
    (‖1 / t - 1 / t'‖ ^ K * ‖R (x t) (x t')‖ ≤
      ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j)) ∧
    (‖1 / t - 1 / t'‖ ^ K * ‖Npair R x (fun u => ‖u‖ ^ ex) bw t t'‖ ≤
      (∏ a, cg grid a) * (Real.sqrt Qw * BB) ^ K *
        ∑ j, F7.thGrid grid j *
          ((‖t‖ ^ (2 * ex) * RL j / (bw * nnProd nn 0 grid j) +
            ‖t'‖ ^ (2 * ex) * RV j / (bw * nnProd nn 1 grid j)) / 2))
def LowerBlockLiftBoundFromComponents : Prop := PairingGramBound → UnnormalisedLiftBoundFromComponents → LowerBlockNormalisedBoundFromComponents → LowerBlockLiftBound
def LeadingCoefficientVectorIdentity {V : Type} [AddCommGroup V] [Module ℂ V] {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (e t : ℂ) (X0 : V) (XK : (Fin K → Fin (d + 1)) → V) : Prop :=
  (e / t) ^ K • X0 = ∑ j, ((coProd grid j : ℝ) : ℂ) • XK j
def wPrev {K d : ℕ} (w : List (F7.WLetter ℝ)) (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1))
    (a : Fin K) : List (F7.WLetter ℝ) :=
  ((List.finRange K).filter fun b => decide (b < a)).map
      (fun b => (⟨true, grid b (j b), true⟩ : F7.WLetter ℝ)) ++ w
def Rwt (q x : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (Y : ℝ) : ℝ :=
  F7.qW q w Y / F7.xW x w (Y + 1)
def SameLetters (w w' : List (F7.WLetter ℝ)) : Prop :=
  w'.map (fun l => (l.plus, l.pt)) = w.map (fun l => (l.plus, l.pt))
def DiagonalWeightPositivity {V : Type} [SeminormedAddCommGroup V] {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (q x : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (XK : (Fin K → Fin (d + 1)) → V)
    (ρ : Fin K → (Fin K → Fin (d + 1)) → ℝ) (E : (Fin K → Fin (d + 1)) → ℝ) : Prop :=
  (∀ a j, 0 < ρ a j) ∧
  (∀ a j w', SameLetters w w' → ρ a j ≤ Rwt q x (wPrev w' grid j a) (grid a (j a))) ∧
  ∀ j, (∏ a, ρ a j) * ‖XK j‖ ^ 2 ≤ E j
def LeadingBlockRecursiveBoundFromComponents : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ)
    (q x nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (e t : ℂ) (X0 : V) (XK : (Fin K → Fin (d + 1)) → V)
    (ρ : Fin K → (Fin K → Fin (d + 1)) → ℝ) (E : (Fin K → Fin (d + 1)) → ℝ) (wt bw Rw ZZ : ℝ),
    (∀ a, Function.Injective (grid a)) → (e = 1 ∨ e = -1) → t ≠ 0 →
    (∀ a i, 0 < q (grid a i) ∧ 0 < nn (grid a i) ∧ x (grid a i + 1) ≠ 0) →
    LeadingCoefficientVectorIdentity grid e t X0 XK → DiagonalWeightPositivity grid q x w XK ρ E →
    (∀ a j, q (grid a (j a)) / |x (grid a (j a) + 1)| ≤ Rw * ρ a j) →
    (∀ a i, nn (grid a i) * |x (grid a i + 1)| / q (grid a i) ≤ ZZ) →
    0 ≤ wt → 0 < bw →
    ‖t‖ ^ (-(2 * K : ℤ)) * (wt ^ 2 * ‖X0‖ ^ 2 / bw) ≤
      (∏ a, (cg grid a ^ 2 * Rw * ZZ)) * ∑ j, F7.thGrid grid j * (wt ^ 2 * E j / (bw * nnProd nn 0 grid j))
def PairingGramInequality (Ntt : ℂ) (Nt Nt' : ℝ) : Prop := ‖Ntt‖ ^ 2 ≤ Nt * Nt'
def LeadingBlockBoundFromRecursion : Prop :=
  ∀ (K : ℕ) (t t' Ntt : ℂ) (Nt Nt' S abelian₂ : ℝ) (c : Fin K → ℝ),
    t ≠ 0 → t' ≠ 0 → 1 / t - 1 / t' ≠ 0 → ‖t‖ ≤ ‖t'‖ →
    0 ≤ Nt → 0 ≤ Nt' → 0 ≤ S → 0 ≤ abelian₂ → (∀ a, 0 ≤ c a ∧ c a ≤ abelian₂ ^ 2) →
    PairingGramInequality Ntt Nt Nt' → ‖t‖ ^ (-(2 * K : ℤ)) * Nt ≤ (∏ a, c a) * S →
    ‖Ntt‖ ≤ (2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K * ((S + Nt') / 2)
def lamPSq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (Rw ZZ : ℝ) : ℝ :=
  univ.fold max 0 fun a : Fin K => cg grid a ^ 2 * Rw * ZZ
def LeadingBlockLiftBound : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (ex K d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ)
    (q x nn : ℝ → ℝ) (w : List (F7.WLetter ℝ)) (e t t' Ntt : ℂ) (X0 : ℂ → V)
    (XK : (Fin K → Fin (d + 1)) → V) (ρ : Fin K → (Fin K → Fin (d + 1)) → ℝ)
    (E : (Fin K → Fin (d + 1)) → ℝ) (bw Rw ZZ : ℝ),
    (∀ a, Function.Injective (grid a)) → (e = 1 ∨ e = -1) → t ≠ 0 → t' ≠ 0 →
    (∀ a i, 0 < q (grid a i) ∧ 0 < nn (grid a i) ∧ x (grid a i + 1) ≠ 0) →
    LeadingCoefficientVectorIdentity grid e t (X0 t) XK → DiagonalWeightPositivity grid q x w XK ρ E →
    (∀ a j, q (grid a (j a)) / |x (grid a (j a) + 1)| ≤ Rw * ρ a j) →
    (∀ a i, nn (grid a i) * |x (grid a i + 1)| / q (grid a i) ≤ ZZ) → 0 ≤ Rw → 0 ≤ ZZ → 0 < bw →
    PairingGramInequality Ntt (‖t‖ ^ (2 * ex) * ‖X0 t‖ ^ 2 / bw) (‖t'‖ ^ (2 * ex) * ‖X0 t'‖ ^ 2 / bw) →
    (‖t‖ ^ (-(2 * K : ℤ)) * (‖t‖ ^ (2 * ex) * ‖X0 t‖ ^ 2 / bw) ≤
      (∏ a, (cg grid a ^ 2 * Rw * ZZ)) *
        ∑ j, F7.thGrid grid j * (‖t‖ ^ (2 * ex) * E j / (bw * nnProd nn 0 grid j))) ∧
    (1 / t - 1 / t' ≠ 0 → ‖t‖ ≤ ‖t'‖ →
      ‖Ntt‖ ≤ (2 * Real.sqrt (lamPSq grid Rw ZZ) / ‖1 / t - 1 / t'‖) ^ K *
        ((∑ j, F7.thGrid grid j * (‖t‖ ^ (2 * ex) * E j / (bw * nnProd nn 0 grid j)) +
          ‖t'‖ ^ (2 * ex) * ‖X0 t'‖ ^ 2 / bw) / 2))
def LeadingBlockLiftBoundFromComponents : Prop := LeadingBlockRecursiveBoundFromComponents → LeadingBlockBoundFromRecursion → LeadingBlockLiftBound
def minFac (L o : ℝ) (K : ℕ) : ℝ := if L < o then (L / o) ^ K else 1
def PlacesCombine : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ o : ι → ℝ) (N S : ℝ),
    (∀ v, 0 ≤ abelian₂ v) → 0 ≤ S →
    (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K) * N ≤
      (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), abelian₂ v ^ K) * S →
    N ≤ (∏ v, minFac (abelian₂ v) (o v) K) * S
def oAbs {ι : Type} (t t' : ι → ℂ) (v : ι) : ℝ := ‖1 / t v - 1 / t' v‖
def LeadingBlockSeveralPlacesBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ : ι → ℝ) (t t' : ι → ℂ) (Ntt : ℂ)
    (Nt Nt' S1 S2 : ℝ),
    (∀ v, t v ≠ 0 ∧ t' v ≠ 0) → (∀ v, 0 ≤ abelian₂ v) → 0 ≤ Nt → 0 ≤ Nt' → 0 ≤ S1 → 0 ≤ S2 →
    PairingGramInequality Ntt Nt Nt' →
    Nt ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1 →
    Nt' ≤ (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2 →
    ‖Ntt‖ ≤ (∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K) * ((S1 + S2) / 2)
def FactorsPositive : Prop :=
  (∀ D : ℝ, D ≠ 0 → D ≠ 1 → (0 < (D + 1) / D ∧ 0 < D / (D - 1) ↔ 1 < |D|)) ∧
  (∀ d : ℝ, d ≠ 1 → d ≠ 2 → (0 < d / (d - 1) ∧ 0 < (d - 1) / (d - 2) ↔ (d < 0 ∨ 2 < d))) ∧
  (∀ D : ℝ, 0 < D → D < 1 → D / (D - 1) < 0)
def CutRoom : Prop :=
  ∀ (r : ℕ) (α β : ℝ), 30 * ((r : ℝ) + 1) ^ 2 ≤ β - α →
    3 * (r + 1) * (2 * r + 2) = 6 * (r + 1) ^ 2 ∧
    ∀ k : ℕ, k < 6 * (r + 1) ^ 2 → α + 2 ≤ α + 2 + 5 * (k : ℝ) ∧ α + 2 + 5 * (k : ℝ) + 1 ≤ β - 2
def WeightLower : Prop :=
  ∀ (N m : ℕ) (f : Fin m → ℝ), 4 ≤ N → m ≤ N → (∀ i, 1 - 1 / (N : ℝ) ^ 2 ≤ f i) →
    Real.exp (-(1 / 2)) ≤ ∏ i, f i
def CorAProduct : Prop :=
  ∀ (n : ℕ) (TT IL y : ℝ) (q x P QQ : ℝ → ℝ),
    0 < TT → 0 < IL → 4 * (n : ℝ) ≤ IL → q y = TT * |QQ (y + 1 / 2)| → 0 < q y →
    |x (y + 1)| ≤ Real.sqrt |QQ (y + 1 / 2)| → P (y + 1) ≠ 0 →
    |P y / P (y + 1)| ≤ Real.exp (4 * n / IL) →
    |x (y + 1) * P y| / q y ≤
      Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))
def CorAConstWave : Prop :=
  (∀ (n : ℕ) (ell Qw BBs BB : ℝ), 0 < ell → 1 ≤ n → 0 ≤ Qw → Qw ≤ Real.exp (1 / 2) → 0 ≤ BBs →
    BBs ≤ BB →
    (1 / 2) * (4 / ell) ^ n * Real.sqrt Qw * BBs ≤ Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ n * BB) ∧
  (∀ (Qw BBs BB : ℝ), 0 ≤ Qw → Qw ≤ Real.exp 2 → 0 ≤ BBs → BBs ≤ BB →
    Real.sqrt Qw * BBs ≤ Real.exp 1 * BB)
def CorAConstTop : Prop :=
  (∀ (n : ℕ) (ell Rw ZZ BB TT : ℝ), 0 < ell → 1 ≤ n → 0 < TT → 0 ≤ Rw → Rw ≤ Real.exp (1 / 2) →
    0 ≤ ZZ → ZZ ≤ Real.exp (1 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) →
    ((1 / 2) * (4 / ell) ^ n) ^ 2 * Rw * ZZ ≤
      Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * n) * BB * TT ^ (-(1 / 2 : ℝ))) ∧
  (∀ (Rw ZZ BB TT : ℝ), 0 < TT → 0 ≤ Rw → Rw ≤ Real.exp (1 / 2) → 0 ≤ ZZ →
    ZZ ≤ Real.exp (1 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) →
    Rw * ZZ ≤ Real.exp (3 / 2) * BB * TT ^ (-(1 / 2 : ℝ)))
def WeightedKernelPSD : Prop :=
  ∀ (H : Type) [Fintype H] (Kn : Matrix H H ℂ) (n : H → ℝ), Kn.PosSemidef → (∀ h, 0 ≤ n h) →
    (Matrix.of fun h h' => ((Real.sqrt (n h) * Real.sqrt (n h') : ℝ) : ℂ) * Kn h h').PosSemidef
def ScaleThresholds : Prop :=
  ∀ (ka ell sb TT : ℝ) (i s r : ℕ), 0 < ka → 0 < ell → 0 < TT → 1 ≤ i →
    ka ^ ((2 * i : ℤ) - 3) * (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * i - 2) * (ka * sb)) =
      Real.exp (1 / 4) / 2 * sb * (4 * ka / ell) ^ (2 * i - 2) ∧
    ka ^ ((2 * i + s : ℤ) - 3) * (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * (i - 1) + s) * (ka * sb)) =
      Real.exp (1 / 4) / 2 * sb * (4 * ka / ell) ^ (2 * (i - 1) + s) ∧
    ka ^ (2 * (i + r - 1)) * (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * (ka * sb) *
        (ka ^ (4 * r) * TT) ^ (-(1 / 2 : ℝ))) =
      Real.exp (3 / 2) / 4 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (4 / ell) ^ (2 * (i - 1))
def ScaleThresholdsOne : Prop :=
  ∀ (ka sb TT : ℝ) (r : ℕ), 0 < ka → 0 < TT →
    ka ^ (-1 : ℤ) * (Real.exp 1 * (ka * sb)) = Real.exp 1 * sb ∧
    ka ^ (2 * r) * (Real.exp (3 / 2) * (ka * sb) * (ka ^ (4 * r) * TT) ^ (-(1 / 2 : ℝ))) =
      Real.exp (3 / 2) * sb * ka * TT ^ (-(1 / 2 : ℝ))
def ScaleThresholdsBelow : Prop :=
  ∀ (ka ell sb TT N IL : ℝ) (m i : ℕ), 0 < ka → 0 < ell → 0 < N → 0 < IL → 0 ≤ sb → 0 < TT →
    IL / (7 * N) ≤ ell →
    Real.exp (1 / 4) / 2 * sb * (4 * ka / ell) ^ m ≤ sb * (28 * ka * N / IL) ^ m ∧
    Real.exp (3 / 2) / 4 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (4 / ell) ^ (2 * (i - 1)) ≤
      2 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (28 * N / IL) ^ (2 * (i - 1))
def ScaleBeta : Prop :=
  ∀ (ka Pp q : ℝ) (r : ℕ), 0 < ka → 0 < q → 0 ≤ Pp →
    Real.sqrt (Pp / (ka ^ (4 * r) * q)) = ka * (ka ^ (-(1 + 2 * r : ℤ)) * Real.sqrt (Pp / q))
def ScaleCharacter : Prop :=
  ∀ (ka : ℝ) (i : ℕ) (l c : ℂ), 0 < ka → 1 ≤ i →
    Complex.exp (ka * (l * c - starRingEnd ℂ (l * c))) =
      Complex.exp ((ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c) -
        starRingEnd ℂ ((ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c)))
def StdFramePhase : Prop :=
  ∀ (ka : ℝ) (a b : ℕ), 1 ≤ a → 1 ≤ b →
    (Complex.I * ka) ^ (b - 1) * (starRingEnd ℂ (Complex.I * ka)) ^ (a - 1) =
      (ka : ℂ) ^ (a + b - 2) * Complex.I ^ ((b : ℤ) - a)
def BlockPhase : Prop :=
  ∀ (s x : ℕ), Complex.I ^ ((s : ℤ) - 1 - 2 * x) * (-1) ^ x = Complex.I ^ ((s : ℤ) - 1)
def RealCharacter : Prop :=
  ∀ (g rd : ℝ) (x : ℂ), 0 < g → 0 < rd →
    Complex.exp (2 * Real.pi * Complex.I * (x + starRingEnd ℂ x) / g) =
      Complex.exp (Complex.I * ((2 * Real.pi / (g * rd) : ℝ) : ℂ) * (rd * x + starRingEnd ℂ (rd * x)))
def RealFrameEntry : Prop :=
  ∀ (rd : ℝ) (r a b i s : ℤ), 0 < rd →
    rd ^ (-(r + 1 - b)) * rd ^ (-(r + 1 - a)) = rd ^ (-(2 * r + 2 - a - b)) ∧
    (a + b = 2 * i + s - 1 → 2 * r + 2 - a - b = 2 * r + 3 - 2 * i - s)
def FrameJacobian : Prop :=
  ∀ (ka : ℝ) (m : ℕ) (g : ℂ → ℂ), 0 < ka →
    ∫ z : ℂ, ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * g z =
      ((ka ^ (2 * m + 2) : ℝ) : ℂ) * ∫ c : ℂ, ((‖c‖ ^ (2 * m) : ℝ) : ℂ) * g ((ka : ℂ) * c)
def GaExponent : Prop :=
  (∀ (ka : ℝ) (l M : ℕ), 2 ≤ M → (ka ^ (2 * l - 2)) ^ (2 * (M - 2) + 2) = ka ^ (4 * (l - 1) * (M - 1))) ∧
  (∀ r k : ℕ, 1 ≤ k → 4 * r * (k - 1) + 4 * r = 4 * r * ((k + 1) - 1))
def FrameIntegral : Prop :=
  ∀ (ka de Cst : ℝ) (ph pht : ℂ → ℂ) (Rt R : ℂ), 0 < ka → 0 < de →
    (∀ c, ph c * de = Cst * pht ((ka : ℂ) * c) * ka ^ 2) →
    ∫ z : ℂ, pht z = Rt → R = Cst * Rt →
    ∫ c : ℂ, ph c * de = R
end
end Formalism.FourierDecayAlt.PairingProductCorollary


