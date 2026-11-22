-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
-- name    : Formalism_QuotientMetricDivisors_HeightBoundExactNorms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:00.580823+00:00
-- url     : https://prove2.me/theorems/a5f93415-c4fd-4c59-96ec-9a2cc87217f0
-- title:
--   Height Bound Exact Norms
-- statement:
--   Definitions and structural lemmas for Height Bound Exact Norms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HeightBoundExactNorms.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.DivisionValues
section Defs
def fnorm {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℝ :=
  Formalism.HermitianLatticesTheory.cnorm (Y⁻¹.mulVec x)
def fmaj {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  ∑ i, star (Y⁻¹.mulVec x i) * Y⁻¹.mulVec y i
def pairC {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) : ℂ :=
  ∑ i, ∑ k, x i * y k * v.embedding (B (Pi.single i 1) (Pi.single k 1))
def chainFun {m : ℕ} {C : Fin (m + 1) → Type} (Kj : ∀ j : Fin m, C j.castSucc → C j.succ) :
    ∀ i : Fin (m + 1), C 0 → C i :=
  Fin.induction (motive := fun i => C 0 → C i) id (fun j f => Kj j ∘ f)
def chainMat {R : Type} [Semiring R] {m : ℕ} {c : Fin (m + 1) → ℕ}
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) R) :
    ∀ i : Fin (m + 1), Matrix (Fin (c i)) (Fin (c 0)) R :=
  Fin.induction (motive := fun i => Matrix (Fin (c i)) (Fin (c 0)) R) 1 (fun j A => Kj j * A)
def minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f
end Defs
def FnormRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K),
      fnorm (X v) (fun i => v.embedding (x i)) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ∧
      fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (y i)) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y ∧
      ((fnorm (X v) (fun i => v.embedding (x i)) ^ 2 : ℝ) : ℂ) =
        fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (x i))
def PairCRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a D : ℕ) (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (φ : Fin a → K) (e : Fin D → K),
      pairC v B (fun i => v.embedding (φ i)) (fun k => v.embedding (e k)) = v.embedding (B φ e)
def OpNormDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (a D : ℕ)
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (XM v).det) → (∀ v, IsUnit (XE v).det) →
    ∀ (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (v : InfinitePlace K) (c : ℝ), 0 ≤ c →
      (Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) v B ≤ c ↔
        ∀ (x : Fin a → ℂ) (y : Fin D → ℂ), ‖pairC v B x y‖ ≤ c * fnorm (XM v) x * fnorm (XE v) y)
def DescendNorm : Prop :=
  ∀ (V Q : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] (π : V →ₗ[ℂ] Q), Function.Surjective π →
    (∀ x ∈ (LinearMap.ker π)ᗮ, ‖π x‖ = ‖x‖) →
    ∀ l : V →ₗ[ℂ] ℂ, (∀ u, π u = 0 → l u = 0) →
      ∃ l' : Q →ₗ[ℂ] ℂ, (∀ x, l' (π x) = l x) ∧
        (∀ l'' : Q →ₗ[ℂ] ℂ, (∀ x, l'' (π x) = l x) → l'' = l') ∧
        ∀ p : ℝ, 0 ≤ p → ((∀ x, ‖l x‖ ≤ p * ‖x‖) ↔ ∀ y, ‖l' y‖ ≤ p * ‖y‖)
def QuotMetricRep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ v : InfinitePlace K,
      (∀ x : Fin n → ℂ, fnorm (XQ v) ((P.map v.embedding).mulVec x) ≤ fnorm (X0 v) x) ∧
      ∀ y : Fin D → ℂ, ∃ x : Fin n → ℂ, (P.map v.embedding).mulVec x = y ∧
        fnorm (X0 v) x = fnorm (XQ v) y ∧
        ∀ u : Fin n → ℂ, (P.map v.embedding).mulVec u = 0 → fmaj (X0 v) x u = 0
def DescendNormAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (a n D : ℕ)
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ), (∀ v, IsUnit (XM v).det) →
    ∀ (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ A : (Fin a → K) →ₗ[K] Module.Dual K (Fin n → K),
    (∀ φ F, P.mulVec F = 0 → A φ F = 0) →
      ∃ A' : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K),
        (∀ φ F, A' φ (P.mulVec F) = A φ F) ∧
        (∀ A'' : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K),
          (∀ φ F, A'' φ (P.mulVec F) = A φ F) → A'' = A') ∧
        (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame XQ) v A' =
          Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin n)).dualBasis
            (Formalism.HN.dualFrame X0) v A) ∧
        Formalism.HN.htMap (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
                  (Formalism.HN.dualFrame XQ) A' =
          Formalism.HN.htMap (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin n)).dualBasis
            (Formalism.HN.dualFrame X0) A
def ChainSpec : Prop :=
  (∀ (m : ℕ) (C : Fin (m + 1) → Type) (Kj : ∀ j : Fin m, C j.castSucc → C j.succ) (φ : C 0),
    chainFun Kj 0 φ = φ ∧ ∀ j : Fin m, chainFun Kj j.succ φ = Kj j (chainFun Kj j.castSucc φ)) ∧
  (∀ (R : Type) [Semiring R] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) R),
    chainMat Kj 0 = 1 ∧ ∀ j : Fin m, chainMat Kj j.succ = Kj j * chainMat Kj j.castSucc)
def CompNorm : Prop :=
  ∀ (m : ℕ) (C : Fin (m + 1) → Type) [∀ i, SeminormedAddCommGroup (C i)]
    (Kj : ∀ j : Fin m, C j.castSucc → C j.succ) (k : Fin m → ℝ), (∀ j, 0 ≤ k j) →
    (∀ j x, ‖Kj j x‖ ≤ k j * ‖x‖) →
      ∀ φ : C 0, ‖chainFun Kj (Fin.last m) φ‖ ≤ (∏ j, k j) * ‖φ‖
def CompNormAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K,
      (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) v (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j))) ∧
      (chainMat Kj (Fin.last m) ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∑ j : Fin m, Formalism.HN.htMap (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (Matrix.mulVecLin (Kj j)))
def SminLog : Prop :=
  ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (κ : ℝ) (lam : J → Ix → ℝ), 0 < κ →
    (∀ j p, 0 < lam j p) →
      0 < κ * minOver (fun p => ∏ j, lam j p) ∧
      (∀ p, κ * minOver (fun p => ∏ j, lam j p) ≤ κ * ∏ j, lam j p) ∧
      (∃ p, κ * minOver (fun p => ∏ j, lam j p) = κ * ∏ j, lam j p) ∧
      Real.log (κ * minOver (fun p => ∏ j, lam j p)) =
        Real.log κ + minOver (fun p => ∑ j, Real.log (lam j p))
def SminLogMean : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J]
    (κ : InfinitePlace K → ℝ) (lam : J → Ix → InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    (∀ j p v, 0 < lam j p v) →
      (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
          ∑ v, Real.log (κ v * minOver (fun p => ∏ j, lam j p v)) =
        meanLog κ + (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lam j p v))
def SminMono : Prop :=
  ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (lamL lam : J → Ix → ℝ),
    (∀ j p, 0 < lamL j p) → (∀ j p, lamL j p ≤ lam j p) →
      minOver (fun p => ∑ j, Real.log (lamL j p)) ≤ minOver (fun p => ∑ j, Real.log (lam j p))
def SpecOfNorm : Prop :=
  ∀ (Q E : Type) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι : Q →ₗ[ℂ] E) (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule ℂ Q), (⨆ p, Qp p) = ⊤ →
    (∀ p q, p ≠ q → ∀ x ∈ Qp p, ∀ y ∈ Qp q, ⟪x, y⟫_ℂ = 0) →
    ∀ s : Ix → ℝ,
    (∀ f : Ix → Q, (∀ p, f p ∈ Qp p) → ‖ι (∑ p, f p)‖ ^ 2 = ∑ p, s p * ‖f p‖ ^ 2) →
      ∀ p, ∀ x ∈ Qp p, ∀ y : Q, ⟪ι x, ι y⟫_ℂ = (s p : ℂ) * ⟪x, y⟫_ℂ
def PairingDefined : Prop :=
  ∀ (K : Type) [Field K] (a n D : ℕ) (P : Matrix (Fin D) (Fin n) K), Function.Surjective P.mulVec →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ A : (Fin a → K) →ₗ[K] Module.Dual K (Fin n → K),
      ((∀ φ F, P.mulVec F = 0 → A φ F = 0) ↔
        ∃ B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K),
          ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = A φ F) ∧
      ∀ B B' : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K),
        (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = A φ F) →
        (∀ φ F, B' φ (ι.mulVec (P.mulVec F)) = A φ F) → B = B'
def HeightBoundConstant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
      (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin D → K)),
    (⨆ p, Qp p) = ⊤ →
    ∀ (κ : InfinitePlace K → ℝ) (lam lamL : J → Ix → InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    (∀ j p v, 0 < lamL j p v) → (∀ j p v, lamL j p v ≤ lam j p v) →
    (∀ v p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((κ v * ∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    ∀ (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
      (B : (Fin (c 0) → K) →ₗ[K] Module.Dual K (Fin D → K)),
    (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec φ) F) → B ≠ 0 →
    ∀ (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ),
    (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) →
      (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
        Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
          minOver (fun p => ∑ j, Real.log (lamL j p v))) ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) B ≤
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2)) -
          (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lamL j p v)) - meanLog κ
def HeightBoundExactNorms : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
      (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin D → K)),
    (⨆ p, Qp p) = ⊤ →
    ∀ (κ : InfinitePlace K → ℝ) (lam : J → Ix → InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    (∀ j p v, 0 < lam j p v) →
    (∀ v p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((κ v * ∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    ∀ (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
      (B : (Fin (c 0) → K) →ₗ[K] Module.Dual K (Fin D → K)),
    (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec φ) F) → B ≠ 0 →
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) B ≤
        Formalism.HN.htMap (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
          (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) Pt +
        ∑ j : Fin m, Formalism.HN.htMap (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (Matrix.mulVecLin (Kj j)) -
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lam j p v)) - meanLog κ
end Formalism.DivisionValues


