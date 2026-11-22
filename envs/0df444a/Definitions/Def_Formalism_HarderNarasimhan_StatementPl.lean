-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_StatementPl
-- name    : Formalism_HarderNarasimhan_StatementPl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:11.191974+00:00
-- url     : https://prove2.me/theorems/28b20b6c-94ff-4e5c-a1e8-f70d9343691d
-- title:
--   Statement Pl
-- statement:
--   Definitions and structural lemmas for Statement Pl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/StatementPl.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_Statement
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HN
section Pl
variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]
variable (K) in

def nPl : ℕ := Fintype.card (InfinitePlace K)
variable (K) in

def logDisc : ℝ := Real.log |(NumberField.discr K : ℝ)|
def rkK (L : Submodule (𝓞 K) V) : ℕ := Module.finrank K (Submodule.span K (L : Set V))
def ht (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  (2 : ℝ) ^ (nPl K * rkK L) * |(NumberField.discr K : ℝ)| ^ (-(rkK L : ℝ) / 2) *
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) L)
def size (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  ht b X L ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK L : ℝ)))
def htQ (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L S : Submodule (𝓞 K) V) : ℝ :=
  (2 : ℝ) ^ ((nPl K : ℝ) * ((rkK L : ℝ) - rkK S)) *
    |(NumberField.discr K : ℝ)| ^ (-((rkK L : ℝ) - rkK S) / 2) *
    Formalism.F.covol (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) L) (zl (Formalism.HermitianLatticesTheory.realize b X) S))
def sizeQ (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L S : Submodule (𝓞 K) V) : ℝ :=
  htQ b X L S ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * ((rkK L : ℝ) - rkK S)))
def leastSize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (B : Submodule (𝓞 K) V) : ℝ :=
  sInf {t | ∃ R : Submodule (𝓞 K) V, R ≤ B ∧ R ≠ ⊥ ∧ size b X R = t}
def largestSize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (A : Submodule (𝓞 K) V) : ℝ :=
  sSup {t | ∃ S : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A S ∧ S ≠ A ∧ sizeQ b X A S = t}
def gramPl (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {j : ℕ}
    (e : Fin j → V) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a c => Formalism.HermitianLatticesTheory.majAt b X v (e a) (e c)
def opNormAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (φ : V →ₗ[K] W) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))‖
def htMap (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
def muDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * slope (Formalism.HermitianLatticesTheory.realize b X) L - Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)
def muMaxDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * muMax (Formalism.HermitianLatticesTheory.realize b X) L - Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)
def muMinDef (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  2 * muMin (Formalism.HermitianLatticesTheory.realize b X) L - Real.log 2 + logDisc K / (Module.finrank ℚ K : ℝ)
end Pl
def PlLat : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) V, L.FG →
      IsLat (Formalism.HermitianLatticesTheory.realize b X) L ∧
      rk (Formalism.HermitianLatticesTheory.realize b X) L = Module.finrank ℚ K * rkK L ∧ 0 < ht b X L
def HtGram : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V), LinearIndependent K e →
      ht b X (Submodule.span (𝓞 K) (Set.range e)) = ∏ v, (gramPl b X v e).det.re ∧
      ∀ L : Submodule (𝓞 K) V, L.FG → Submodule.span (𝓞 K) (Set.range e) ≤ L → rkK L = j →
        ht b X L * ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
          L.toAddSubgroup : ℝ) = ht b X (Submodule.span (𝓞 K) (Set.range e))
def SizeMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) V, L.FG → L ≠ ⊥ →
      let c : ℝ := Real.log 2 / 2 - logDisc K / (2 * (Module.finrank ℚ K : ℝ))
      size b X L = Real.exp (c - slope (Formalism.HermitianLatticesTheory.realize b X) L) ∧
      muDef b X L = -2 * Real.log (size b X L) ∧
      (∀ S : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) L S → S ≠ L →
        sizeQ b X L S = Real.exp (c - Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) L)
          (zl (Formalism.HermitianLatticesTheory.realize b X) S)))) ∧
      leastSize b X L = Real.exp (c - muMax (Formalism.HermitianLatticesTheory.realize b X) L) ∧
      largestSize b X L = Real.exp (c - muMin (Formalism.HermitianLatticesTheory.realize b X) L) ∧
      (∀ L' : Submodule (𝓞 K) V, L ≤ L' → L'.FG → rkK L' = rkK L → ht b X L' ≤ ht b X L)
def HtImage : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V), A.FG →
      IsSat (Formalism.HermitianLatticesTheory.realize b X) A (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) ∧
      ht b' X' (A.map (φ.restrictScalars (𝓞 K))) ≤
        (∏ v, opNormAt b X b' X' v φ ^ (2 * rkK (A.map (φ.restrictScalars (𝓞 K))))) *
          htQ b X A (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K))
def SizeIneq : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W), A.FG → B.FG →
      A.map (φ.restrictScalars (𝓞 K)) ≤ B → A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ →
      leastSize b' X' B / largestSize b X A ≤
        (∏ v, opNormAt b X b' X' v φ) ^ ((1 : ℝ) / (nPl K : ℝ))
def Twist : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (c : InfinitePlace K → ℝ), (∀ v, IsUnit (X v).det) →
    (∀ v, 0 < c v) →
    let X' : InfinitePlace K → Matrix ι ι ℂ := fun v => ((c v : ℂ)) • X v
    let t : ℝ := (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v)
    ∀ L : Submodule (𝓞 K) V, L.FG →
      (L ≠ ⊥ → slope (Formalism.HermitianLatticesTheory.realize b X') L = slope (Formalism.HermitianLatticesTheory.realize b X) L + t) ∧
      (L ≠ ⊥ → muMax (Formalism.HermitianLatticesTheory.realize b X') L = muMax (Formalism.HermitianLatticesTheory.realize b X) L + t ∧
        muMin (Formalism.HermitianLatticesTheory.realize b X') L = muMin (Formalism.HermitianLatticesTheory.realize b X) L + t) ∧
      (L ≠ ⊥ → muDef b X' L = muDef b X L + 2 * t ∧ muMaxDef b X' L = muMaxDef b X L + 2 * t ∧
        muMinDef b X' L = muMinDef b X L + 2 * t) ∧
      ∀ θ : ℝ, hnStep (Formalism.HermitianLatticesTheory.realize b X') L (θ + t) = hnStep (Formalism.HermitianLatticesTheory.realize b X) L θ
def SlopeIneqMean : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V), A.FG → A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ →
      muMinDef b X A - htMap b X b' X' φ ≤ muMinDef b' X' (A.map (φ.restrictScalars (𝓞 K))) ∧
      (∀ B : Submodule (𝓞 K) W, B.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ B →
        muMinDef b X A ≤ muMaxDef b' X' B + htMap b X b' X' φ ∧
        (Set.InjOn φ (A : Set V) → muMaxDef b X A ≤ muMaxDef b' X' B + htMap b X b' X' φ))
def RescaleCovol : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (c : InfinitePlace K → ℝ),
    (∀ v, IsUnit (X v).det) → (∀ v, 0 < c v) →
    ∀ N : Submodule (𝓞 K) V, N.FG →
      Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N) =
        (∏ v, c v) ^ (-(2 * (rkK N : ℝ))) * Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N)
end Formalism.HN


