-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
-- name    : Formalism_ThetaSupremumBounds_StatementCB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:17.059902+00:00
-- url     : https://prove2.me/theorems/93dacc20-0623-4cad-bb2b-6ceedb9c77ed
-- title:
--   Statement CB
-- statement:
--   Definitions and structural lemmas for Statement CB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/StatementCB.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
noncomputable section
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
def cbSq (n n' h h' t : ℝ) : ℝ := n * n' * (h * h') * t
def entryHom {AA AA' : Type} {Cl : AA → Type} {Cl' : AA' → Type} [∀ a, Fintype (Cl a)] {A B : Type}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : (Σ a, Cl a) → ℝ) (ε : (Σ a, Cl a) → (Σ b, Cl' b) → ℂ)
    (T : (Σ a, Cl a) → (Σ b, Cl' b) → A →L[ℂ] B) (a : AA) (b : AA') : (Cl a → A) →+ (Cl' b → B) where
  toFun φ := liftOp (fun L => γ ⟨a, L⟩) (fun L L' => ε ⟨a, L⟩ ⟨b, L'⟩) (fun L L' => T ⟨a, L⟩ ⟨b, L'⟩) φ
  map_zero' := by funext L'; simp [liftOp]
  map_add' φ ψ := by funext L'; simp [liftOp, Finset.sum_add_distrib]
def blockMap {AA AA' : Type} [Fintype AA] {H : AA → Type} {H' : AA' → Type}
    [∀ a, AddCommMonoid (H a)] [∀ b, AddCommMonoid (H' b)]
    (E : ∀ a b, H a →+ H' b) (G : ∀ a, H a) : ∀ b, H' b :=
  fun b => ∑ a, E a b (G a)
def coupledOp {AA Rep Y Cl2 : Type} {Cl : AA → Type} [∀ a, Fintype (Cl a)] [Fintype Rep] [Fintype Y] {A B C : Type}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (γ0 : (Σ a, Cl a) → ℝ) (γ1 : Rep → ℝ) (ε1 : (Σ a, Cl a) → (Σ _ : Y, Rep) → ℂ)
    (T1 : (Σ a, Cl a) → (Σ _ : Y, Rep) → A →L[ℂ] B) (ε2 : (Σ _ : Y, Rep) → Cl2 → ℂ)
    (T2 : (Σ _ : Y, Rep) → Cl2 → B →L[ℂ] C)
    (a : AA) (φ : Cl a → A) (g' : Cl2) : C :=
  ∑ x, (γ1 x : ℂ) • ∑ y, ε2 ⟨y, x⟩ g' • T2 ⟨y, x⟩ g'
    (liftOp (fun L => γ0 ⟨a, L⟩) (fun L x' => ε1 ⟨a, L⟩ ⟨y, x'⟩) (fun L x' => T1 ⟨a, L⟩ ⟨y, x'⟩) φ x)
def SharpEntries : Prop :=
  ∀ (AA AA' : Type) [Fintype AA] (Cl : AA → Type) (Cl' : AA' → Type) [∀ a, Fintype (Cl a)] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : (Σ a, Cl a) → ℝ) (ε : (Σ a, Cl a) → (Σ b, Cl' b) → ℂ)
    (T : (Σ a, Cl a) → (Σ b, Cl' b) → A →L[ℂ] B) (G : (Σ a, Cl a) → A),
    (∀ (b : AA') (L' : Cl' b), liftOp γ ε T G ⟨b, L'⟩ =
      blockMap (entryHom γ ε T) (fun a L => G ⟨a, L⟩) b L') ∧
    (∑ p, γ p * ‖G p‖ ^ 2) = ∑ a, ∑ L, γ ⟨a, L⟩ * ‖G ⟨a, L⟩‖ ^ 2
def CoupledProduct : Prop :=
  ∀ (AA Rep Y Cl2 : Type) [Fintype AA] (Cl : AA → Type) [∀ a, Fintype (Cl a)] [Fintype Rep] [Fintype Y]
    (A B C : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (γ0 : (Σ a, Cl a) → ℝ) (γ1 : Rep → ℝ) (ε1 : (Σ a, Cl a) → (Σ _ : Y, Rep) → ℂ)
    (T1 : (Σ a, Cl a) → (Σ _ : Y, Rep) → A →L[ℂ] B) (ε2 : (Σ _ : Y, Rep) → Cl2 → ℂ)
    (T2 : (Σ _ : Y, Rep) → Cl2 → B →L[ℂ] C)
    (G : (Σ a, Cl a) → A) (g' : Cl2),
    liftOp (fun p : (Σ _ : Y, Rep) => γ1 p.2) ε2 T2 (liftOp γ0 ε1 T1 G) g' =
      ∑ a, coupledOp γ0 γ1 ε1 T1 ε2 T2 a (fun L => G ⟨a, L⟩) g'
def PathSum : Prop :=
  ∀ (m : ℕ) (AA : Fin (m + 1) → Type) [∀ i, Fintype (AA i)] [∀ i, DecidableEq (AA i)]
    (H : ∀ i, AA i → Type) [∀ i a, AddCommMonoid (H i a)]
    (E : ∀ (j : Fin m) (a : AA j.castSucc) (b : AA j.succ), H j.castSucc a →+ H j.succ b)
    (G : ∀ a, H 0 a),
    chainFun (C := fun i => ∀ a, H i a) (fun j => blockMap (E j)) (Fin.last m) G =
      ∑ al : (∀ i, AA i), Pi.single (al (Fin.last m))
        (chainFun (C := fun i => H i (al i)) (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last m)
          (G (al 0)))
def ColPaths : Prop :=
  ∀ (m : ℕ) (AA : Fin (m + 1) → Type) [∀ i, Fintype (AA i)] [∀ i, DecidableEq (AA i)]
    (Cl : ∀ i, AA i → Type) [∀ i a, Fintype (Cl i a)]
    (W : Fin (m + 1) → Type) [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℂ (W i)]
    (γ : ∀ i, (Σ a, Cl i a) → ℝ)
    (ε : ∀ j : Fin m, (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → ℂ)
    (T : ∀ j : Fin m, (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → W j.castSucc →L[ℂ] W j.succ)
    (G : (Σ a, Cl 0 a) → W 0),
    (fun (b : AA (Fin.last m)) (L' : Cl (Fin.last m) b) =>
      chainFun (C := fun i => (Σ a, Cl i a) → W i) (fun j => liftOp (γ j.castSucc) (ε j) (T j))
        (Fin.last m) G ⟨b, L'⟩) =
      ∑ al : (∀ i, AA i), Pi.single (al (Fin.last m))
        (chainFun (C := fun i => Cl i (al i) → W i)
          (fun j => entryHom (γ j.castSucc) (ε j) (T j) (al j.castSucc) (al j.succ)) (Fin.last m)
          (fun L => G ⟨al 0, L⟩))
def SharpNorm : Prop :=
  ∀ (AA AA' : Type) [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : (Σ a, Cl a) → ℝ) (γ' : (Σ b, Cl' b) → ℝ) (ε : (Σ a, Cl a) → (Σ b, Cl' b) → ℂ)
    (T : (Σ a, Cl a) → (Σ b, Cl' b) → A →L[ℂ] B) (h h' tmax : ℝ),
    (∀ p, 0 < γ p ∧ γ p ≤ 1) → (∀ q, 0 < γ' q ∧ γ' q ≤ 1) → (∀ p q, ‖ε p q‖ = 1) →
    (∀ p q, ‖T p q‖ ^ 2 ≤ tmax) → 0 ≤ tmax →
    (∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) → (∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') →
    (∀ G : (Σ a, Cl a) → A, (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2) ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax * ∑ p, γ p * ‖G p‖ ^ 2) ∧
    liftNormSq γ γ' ε T ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax
def CoupledNorm : Prop :=
  ∀ (AA Rep Y Cl2 : Type) (Cl : AA → Type) [∀ a, Fintype (Cl a)] [Fintype Rep] [Fintype Y] [Fintype Cl2]
    (A B C : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (γ0 : (Σ a, Cl a) → ℝ) (γ1 : Rep → ℝ) (γ2 : Cl2 → ℝ) (ε1 : (Σ a, Cl a) → (Σ _ : Y, Rep) → ℂ)
    (T1 : (Σ a, Cl a) → (Σ _ : Y, Rep) → A →L[ℂ] B) (ε2 : (Σ _ : Y, Rep) → Cl2 → ℂ)
    (T2 : (Σ _ : Y, Rep) → Cl2 → B →L[ℂ] C)
    (t1 t2 : ℝ) (a : AA) (φ : Cl a → A),
    (∀ p, 0 < γ0 p ∧ γ0 p ≤ 1) → (∀ x, 0 < γ1 x ∧ γ1 x ≤ 1) → (∀ g', 0 < γ2 g' ∧ γ2 g' ≤ 1) →
    (∀ p q, ‖ε1 p q‖ = 1) → (∀ q g', ‖ε2 q g'‖ = 1) →
    (∀ p q, ‖T1 p q‖ ^ 2 ≤ t1) → (∀ q g', ‖T2 q g'‖ ^ 2 ≤ t2) → 0 ≤ t1 → 0 ≤ t2 →
    (∑ g', γ2 g' * ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2) ≤
      (Fintype.card Y : ℝ) ^ 2 * (((Fintype.card Rep : ℝ) * (Fintype.card Cl2 : ℝ)) * t2) *
        (((Fintype.card (Cl a) : ℝ) * (Fintype.card Rep : ℝ)) * t1) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2
def SharpCost : Prop :=
  ∀ (n n' : ℕ) (g f N : ℝ), 1 ≤ n → 1 ≤ n' → 1 ≤ g → 0 ≤ f → 1 ≤ N →
    ((n : ℝ) ≤ g ^ (f * N ^ 2) ∨ (n : ℝ) ≤ g ^ (f * N)) →
    ((n' : ℝ) ≤ g ^ (f * N ^ 2) ∨ (n' : ℝ) ≤ g ^ (f * N)) →
    Real.log n ≤ f * N ^ 2 * Real.log g ∧ Real.log n' ≤ f * N ^ 2 * Real.log g ∧
    Real.log ((n : ℝ) * n') ≤ 2 * f * N ^ 2 * Real.log g
def LemmaCB : Prop :=
  SharpEntries ∧ CoupledProduct ∧ PathSum ∧ ColPaths ∧ SharpNorm ∧ CoupledNorm ∧ SharpCost
def LiftSharpBound : Prop :=
  ∀ (Pl ι AA AA' : Type) [Fintype Pl] [Fintype ι] [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Σ a, Cl a) → (Σ b, Cl' b) → (Pl × ι → ℂ) → ℂ) (c : (Σ a, Cl a) → (Σ b, Cl' b) → (Pl × ι → ℕ) → ℂ)
    (Rc : (Pl × ι → ℕ) →₀ (A →L[ℂ] B)) (lam : Pl → ℂ) (Om : Pl → ℝ) (S : ℝ)
    (γ : (Σ a, Cl a) → ℝ) (γ' : (Σ b, Cl' b) → ℝ) (ε : (Σ a, Cl a) → (Σ b, Cl' b) → ℂ) (h h' : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ, ∑ i, ν τ i = n τ) →
    (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    (∀ L L', Continuous (Th L L')) →
    (∀ L L' u, HasSum (fun e => c L L' e * mono u e) (Th L L' u)) →
    (∀ L L' u, ‖Th L L' u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ e ∈ Rc.support, ∀ τ, ∑ x, e (τ, x) = n τ) →
    (∀ u, ‖Rc.sum (fun e X => mono (cj u) e • X)‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    (∀ τ, 0 < Om τ) → (∀ τ, ‖lam τ‖ ^ 2 = (Om τ)⁻¹) →
    (∀ L, 0 < γ L ∧ γ L ≤ 1) → (∀ L', 0 < γ' L' ∧ γ' L' ≤ 1) → (∀ L L', ‖ε L L'‖ = 1) →
    (∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) → (∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') →
    liftNormSq γ γ' ε (fun L L' => liftBlock (c L L') Rc lam) ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h'
        (S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ n τ *
          (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i)))))
def CBHyp {K : Type} [Field K] [NumberField K] {m : ℕ} {c : Fin (m + 1) → ℕ}
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    {AA : Fin (m + 1) → Type} (Cl : ∀ i, AA i → Type) [∀ i, Fintype (AA i)] [∀ i a, Fintype (Cl i a)]
    (W : Fin (m + 1) → InfinitePlace K → Type) [∀ i v, NormedAddCommGroup (W i v)]
    [∀ i v, NormedSpace ℂ (W i v)]
    (γ : ∀ i, (Σ a, Cl i a) → ℝ)
    (Φ : ∀ i v, (Fin (c i) → ℂ) → (Σ a, Cl i a) → W i v)
    (ε : ∀ (j : Fin m) (_ : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → ℂ)
    (T : ∀ (j : Fin m) (v : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) →
      W j.castSucc v →L[ℂ] W j.succ v)
    (hcl : Fin (m + 1) → ℝ) (tmax : Fin m → InfinitePlace K → ℝ) : Prop :=
  (∀ i v, IsUnit (Xc i v).det) ∧
  (∀ i p, 0 < γ i p ∧ γ i p ≤ 1) ∧
  (∀ i v x, (∑ p, γ i p * ‖Φ i v x p‖ ^ 2) = fnorm (Xc i v) x ^ 2) ∧
  (∀ j v x, Φ j.succ v (((Kj j).map v.embedding).mulVec x) =
    liftOp (γ j.castSucc) (ε j v) (T j v) (Φ j.castSucc v x)) ∧
  (∀ j v p q, ‖ε j v p q‖ = 1) ∧
  (∀ j v p q, ‖T j v p q‖ ^ 2 ≤ tmax j v) ∧ (∀ j v, 0 ≤ tmax j v) ∧
  (∀ i a, (Fintype.card (Cl i a) : ℝ) ≤ hcl i)
def ChainCB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (AA : Fin (m + 1) → Type) (Cl : ∀ i, AA i → Type) [∀ i, Fintype (AA i)] [∀ i a, Fintype (Cl i a)]
    (W : Fin (m + 1) → InfinitePlace K → Type) [∀ i v, NormedAddCommGroup (W i v)]
    [∀ i v, NormedSpace ℂ (W i v)]
    (γ : ∀ i, (Σ a, Cl i a) → ℝ)
    (Φ : ∀ i v, (Fin (c i) → ℂ) → (Σ a, Cl i a) → W i v)
    (ε : ∀ (j : Fin m) (_ : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → ℂ)
    (T : ∀ (j : Fin m) (v : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) →
      W j.castSucc v →L[ℂ] W j.succ v)
    (hcl : Fin (m + 1) → ℝ) (tmax : Fin m → InfinitePlace K → ℝ),
    CBHyp Xc Kj Cl W γ Φ ε T hcl tmax →
    ∀ kU : Fin m → InfinitePlace K → ℝ,
    (∀ j v, kU j v = Real.sqrt (cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v))) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) ∧
    (∀ j v, kU j v ^ 2 = cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v)) ∧
    (chainMat Kj (Fin.last m) ≠ 0 →
      (∀ j v, 0 < (Fintype.card (AA j.castSucc) : ℝ) ∧ 0 < (Fintype.card (AA j.succ) : ℝ) ∧
        0 < hcl j.castSucc ∧ 0 < hcl j.succ ∧ 0 < tmax j v) ∧
      (∀ j v, Real.log (kU j v ^ 2) =
        Real.log (tmax j v) + (Real.log (hcl j.castSucc) + Real.log (hcl j.succ)) +
          (Real.log (Fintype.card (AA j.castSucc)) + Real.log (Fintype.card (AA j.succ)))) ∧
      (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
          (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ^ 2) ≤
        ∑ j : Fin m, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2)) ∧
      (∀ v, (∑ j : Fin m, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2)) ≤
        ∑ j : Fin m, Real.log (kU j v ^ 2)) ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
                (Xc (Fin.last m)) (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, ∑ j : Fin m, Real.log (kU j v ^ 2))
def StepDiCB : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' logn logn' hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j)) →
    (∀ j, logn j ≤ f * N ^ 2 * logg) → (∀ j, logn' j ≤ f * N ^ 2 * logg) →
    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) + 2 * C8 ≤ C0 →
    (∀ j s, logK j s ≤
      liftedMapLogSize ν g0 (fun j s => MainNotions j s + (logn j + logn' j) / 2) logOmτ logth0 logh logh' v j s) ∧
    (∀ j s, MainNotions j s + (logn j + logn' j) / 2 ≤
      C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + 1 * f * N ^ 2 * logg) ∧
    (∀ j s, logK j s ≤
      liftedMapLogSize ν g0 MainNotions logOmτ logth0 (fun j => logh j + logn j) (fun j => logh' j + logn' j) v j s) ∧
    (∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j) ∧
    ∃ eK : J → ℝ,
      DiHyp6 J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) logOm f m N L La C0
def PerEmbeddingCB : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' logn logn' : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j)) →
    (∀ j, logn j ≤ f * N ^ 2 * logg) → (∀ j, logn' j ≤ f * N ^ 2 * logg) →
    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) + 2 * C8 ≤ C0 →
    ∃ cst : J → ℝ, (∀ j, 0 ≤ cst j) ∧
      (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j) + cst j) ∧
      (∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j) + cst j)) /
        (Fintype.card Emb : ℝ) = sizeB ν logOm f m N L La C0 j)
def LiftStepDiCB : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    (ι AA AA' : J → Type) (Cl : ∀ j, AA j → Type) (Cl' : ∀ j, AA' j → Type)
    [∀ j, Fintype (ι j)] [∀ j, Fintype (AA j)] [∀ j, Fintype (AA' j)]
    [∀ j a, Fintype (Cl j a)] [∀ j b, Fintype (Cl' j b)]
    [∀ j, Nonempty (AA j)] [∀ j, Nonempty (AA' j)] [∀ j a, Nonempty (Cl j a)] [∀ j b, Nonempty (Cl' j b)]
    (A B : J → Emb → Type)
    [∀ j σ, NormedAddCommGroup (A j σ)] [∀ j σ, NormedSpace ℂ (A j σ)]
    [∀ j σ, NormedAddCommGroup (B j σ)] [∀ j σ, NormedSpace ℂ (B j σ)] [∀ j σ, CompleteSpace (B j σ)]
    (r : ℕ) (ν : J → Pl → Fin r → ℝ) (n : J → Pl → ℕ)
    (s : ∀ j, Emb → Pl → (ι j → ℂ) → Fin r → ℝ)
    (Th : ∀ j, Emb → (Σ a, Cl j a) → (Σ b, Cl' j b) → (Pl × ι j → ℂ) → ℂ)
    (c : ∀ j, Emb → (Σ a, Cl j a) → (Σ b, Cl' j b) → (Pl × ι j → ℕ) → ℂ)
    (Rc : ∀ j σ, (Pl × ι j → ℕ) →₀ (A j σ →L[ℂ] B j σ))
    (lam : Pl → Emb → ℂ) (Om : Pl → Emb → ℝ) (S kc : J → Emb → ℝ) (th0sq : Emb → ℝ)
    (γ : ∀ j, (Σ a, Cl j a) → ℝ) (γ' : ∀ j, (Σ b, Cl' j b) → ℝ)
    (ε : ∀ j, Emb → (Σ a, Cl j a) → (Σ b, Cl' j b) → ℂ) (hK hcl hcl' : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j τ i, 0 ≤ ν j τ i) → (∀ j τ, ∑ i, ν j τ i = (n j τ : ℝ)) →
    (∀ j σ τ u i, 0 ≤ s j σ τ u i) → (∀ j σ τ u, ∑ i, s j σ τ u i ^ 2 = nsq u) →
    (∀ j σ L L', Continuous (Th j σ L L')) →
    (∀ j σ L L' u, HasSum (fun e => c j σ L L' e * mono u e) (Th j σ L L' u)) →
    (∀ j σ L L' u, ‖Th j σ L L' u‖ ≤ S j σ * Real.exp (nsq u / 2)) →
    (∀ j σ, ∀ e ∈ (Rc j σ).support, ∀ τ, ∑ x, e (τ, x) = n j τ) →
    (∀ j σ u, ‖(Rc j σ).sum (fun e X => mono (cj u) e • X)‖ ≤
      ∏ τ, ∏ i, s j σ τ (fun x => u (τ, x)) i ^ ν j τ i) →
    (∀ τ σ, 0 < Om τ σ) → (∀ τ σ, ‖lam τ σ‖ ^ 2 = (Om τ σ)⁻¹) →
    (∀ j L, 0 < γ j L ∧ γ j L ≤ 1) → (∀ j L', 0 < γ' j L' ∧ γ' j L' ≤ 1) →
    (∀ j σ L L', ‖ε j σ L L'‖ = 1) →
    (∀ j σ, S j σ ^ 2 = kc j σ ^ 2 *
      (8 + 32 * ((Fintype.card Pl * Fintype.card (ι j) : ℕ) : ℝ) * v) ^ (Fintype.card Pl * Fintype.card (ι j)) *
      th0sq σ ^ (Fintype.card Pl * Fintype.card (ι j))) →
    (∀ j σ, 0 < liftNormSq (γ j) (γ' j) (ε j σ)
      (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ))) →
    (∀ j σ, 0 < kc j σ) → (∀ σ, 0 < th0sq σ) → 0 < v →
    (∀ j, hK j = (∑ σ, Real.log (liftNormSq (γ j) (γ' j) (ε j σ)
      (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ)))) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ σ, Real.log (Om τ σ)) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j σ, Real.log (kc j σ) ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ σ, Real.log (th0sq σ)) / (Fintype.card Emb : ℝ) ≤ C3 * L →

    (∀ j a, (Fintype.card (Cl j a) : ℝ) ≤ hcl j) → (∀ j b, (Fintype.card (Cl' j b) : ℝ) ≤ hcl' j) →
    (∀ j, Real.log (hcl j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, Real.log (hcl' j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, Real.log (Fintype.card (AA j) : ℝ) ≤ f * N ^ 2 * logg) →
    (∀ j, Real.log (Fintype.card (AA' j) : ℝ) ≤ f * N ^ 2 * logg) →
    0 ≤ logT →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, (Fintype.card (ι j) : ℝ) ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl * Fintype.card (ι j) : ℕ) : ℝ) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (n j τ : ℝ) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * (C4 + 1) * (1 + C7 + C8) ≤ C0 →
    ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j
def LiftedMapEmbeddingLogBound : Prop :=
  ∀ (J Pl Emb : Type) [Fintype Pl] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (n : J → Pl → ℕ) (g0 : J → ℕ)
    (Ksq kc : J → Emb → ℝ) (Om : Pl → Emb → ℝ) (th0sq : Emb → ℝ) (nn nn' hcl hcl' : J → ℝ) (v : ℝ),
    (∀ j τ, ∑ i, ν j τ i = (n j τ : ℝ)) →
    (∀ j s, 0 < Ksq j s) → (∀ j s, 0 < kc j s) → (∀ τ s, 0 < Om τ s) → (∀ s, 0 < th0sq s) →
    (∀ j, 0 < nn j) → (∀ j, 0 < nn' j) → (∀ j, 0 < hcl j) → (∀ j, 0 < hcl' j) → 0 < v →
    (∀ j s, Ksq j s ≤ cbSq (nn j) (nn' j) (hcl j) (hcl' j)
      ((kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) *
        ∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))))) →
    ∀ j s, Real.log (Ksq j s) ≤
      liftedMapLogSize ν (fun j => (g0 j : ℝ)) (fun j s => Real.log (kc j s)) (fun τ s => Real.log (Om τ s))
        (fun s => Real.log (th0sq s)) (fun j => Real.log (hcl j)) (fun j => Real.log (hcl' j)) v j s +
        (Real.log (nn j) + Real.log (nn' j))
end Formalism.DimensionVariation


