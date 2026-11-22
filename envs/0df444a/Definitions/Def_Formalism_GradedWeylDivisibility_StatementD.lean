-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
-- name    : Formalism_GradedWeylDivisibility_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:37:35.864573+00:00
-- url     : https://prove2.me/theorems/30c298b6-3414-4c0b-83c3-d7676addd1e3
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementD.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
def ssIdx (k n : ℕ) (ν : Fin n → ℕ) : Set (Fin k × Fin n →₀ ℕ) :=
  {m | Interlaced m ∧ ∀ t : Fin n, ∑ a : Fin k, m (a, t) = ν t}
def rowWt {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) : Fin k → ℕ := fun a => rowDeg m a
def IsWeightBasis (R : Type*) [CommRing R] (k n : ℕ) (ν : Fin n → ℕ) {ι : Type*}
    (b : ι → MvPolynomial (Fin k × Fin n) R) (μ : ι → (Fin k → ℕ)) : Prop :=
  LinearIndependent R b ∧ Submodule.span R (Set.range b) = dualWeyl R k n ν ∧
    ∀ i, IsWeightedHomogeneous (rowW k n) (b i) (μ i)
def nablaL (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k n : ℕ) (ν : Fin n → ℕ)
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (MvPolynomial (Fin k × Fin n) K) :=
  Submodule.comap ((rowAct K (n := n) g).toLinearMap.restrictScalars R)
    (Submodule.map (mapAlgHom (Algebra.ofId R K)).toLinearMap (dualWeyl R k n ν))
def SSBasis : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ),
    ∃ b : ssIdx k n ν → MvPolynomial (Fin k × Fin n) R,
      IsWeightBasis R k n ν b (fun m => rowWt m.1) ∧
      ∀ m : ssIdx k n ν, (colLex k n).degree (b m) = m.1 ∧ (colLex k n).leadingCoeff (b m) = 1 ∧
        ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin k),
          shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ b m = bideterminant R sz hsz I
def SSIdxFinite : Prop :=
  ∀ (k n : ℕ) (ν : Fin n → ℕ), (ssIdx k n ν).Finite
def RowActDiagWeight : Prop :=
  ∀ (R : Type) [CommRing R] (k n : ℕ) (t : Fin k → R) (μ : Fin k → ℕ) (f : MvPolynomial (Fin k × Fin n) R),
    IsWeightedHomogeneous (rowW k n) f μ → rowAct R (Matrix.diagonal t) f = (∏ a, t a ^ μ a) • f
def RowActMul : Prop :=
  ∀ (R : Type) [CommRing R] (k n : ℕ) (g h : Matrix (Fin k) (Fin k) R),
    (rowAct R (n := n) g).comp (rowAct R h) = rowAct R (h * g)
def NablaLBasis : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K], Function.Injective (algebraMap R K) →
    ∀ (k n : ℕ) (ν : Fin n → ℕ) {ι : Type} (b : ι → MvPolynomial (Fin k × Fin n) R) (μ : ι → (Fin k → ℕ)),
      IsWeightBasis R k n ν b μ → ∀ g : Matrix (Fin k) (Fin k) K, IsUnit g.det →
        LinearIndependent R (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) ∧
        Submodule.span R (Set.range fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = nablaL R K k n ν g
def NablaLKBasis : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K], Function.Injective (algebraMap R K) →
    ∀ (k n : ℕ) (ν : Fin n → ℕ) {ι : Type} (b : ι → MvPolynomial (Fin k × Fin n) R) (μ : ι → (Fin k → ℕ)),
      IsWeightBasis R k n ν b μ → ∀ g : Matrix (Fin k) (Fin k) K, IsUnit g.det →
        LinearIndependent K (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) ∧
        Submodule.span K (Set.range fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = dualWeyl K k n ν
def NablaLDiag : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K], Function.Injective (algebraMap R K) →
    ∀ (k n : ℕ) (ν : Fin n → ℕ) {ι : Type} (b : ι → MvPolynomial (Fin k × Fin n) R) (μ : ι → (Fin k → ℕ)),
      IsWeightBasis R k n ν b μ → ∀ (g : Matrix (Fin k) (Fin k) K) (t : Fin k → K), IsUnit g.det → (∀ a, t a ≠ 0) →
        LinearIndependent R (fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i))) ∧
        Submodule.span R (Set.range fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i))) =
          nablaL R K k n ν (g * Matrix.diagonal t)
def NablaLTwist : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (φ : K ≃+* K) (ψ : R ≃+* R),
    (∀ x : R, φ (algebraMap R K x) = algebraMap R K (ψ x)) →
    ∀ (k n : ℕ) (ν : Fin n → ℕ) (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K),
      F ∈ nablaL R K k n ν g ↔ map (φ : K →+* K) F ∈ nablaL R K k n ν (g.map φ)
def NablaLLe : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (k n : ℕ) (ν : Fin n → ℕ) (g : Matrix (Fin k) (Fin k) K),
    IsUnit g.det → ∀ F ∈ nablaL R K k n ν g, F ∈ dualWeyl K k n ν
def dualLat (R K : Type*) [CommRing R] [Field K] [Algebra R K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] (M : Submodule R V) : Submodule R (Module.Dual K V) where
  carrier := {φ | ∀ v ∈ M, φ v ∈ Set.range (algebraMap R K)}
  add_mem' := by
    intro φ ψ hφ hψ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    obtain ⟨b, hb⟩ := hψ v hv
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' := by
    intro v _
    exact ⟨0, by simp⟩
  smul_mem' := by
    intro c φ hφ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    refine ⟨c * a, ?_⟩
    rw [LinearMap.smul_apply, ← ha, map_mul, Algebra.smul_def]
def DualLatBasis : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K], Function.Injective (algebraMap R K) →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] {ι : Type} [Fintype ι]
      [DecidableEq ι] (b : Module.Basis ι K V),
      LinearIndependent R (fun i => b.dualBasis i) ∧
      dualLat R K (Submodule.span R (Set.range b)) = Submodule.span R (Set.range fun i => b.dualBasis i)
def blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ} (s : S) :
    MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  rename fun v => (s, v)
def tensorLat (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) : Submodule R (MvPolynomial (S × (Fin k × Fin n)) K) :=
  Submodule.span R {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}
def TensorBasis : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K],
    ∀ (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ) (ι : S → Type)
      (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K),
      (∀ s, LinearIndependent R (b s)) → (∀ s, Submodule.span R (Set.range (b s)) = M s) →
      LinearIndependent R (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) ∧
      Submodule.span R (Set.range fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) = tensorLat R K M
def blockAct (K : Type*) [CommRing K] {S : Type*} {k n : ℕ} (g : S → Matrix (Fin k) (Fin k) K) :
    MvPolynomial (S × (Fin k × Fin n)) K →ₐ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  aeval fun v => ∑ b : Fin k, C (g v.1 v.2.1 b) * X (v.1, (b, v.2.2))
def BlockActTensor : Prop :=
  ∀ (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (S : Type) [Fintype S] (k n : ℕ)
    (g : S → Matrix (Fin k) (Fin k) K),
    (∀ (s : S) (F : MvPolynomial (Fin k × Fin n) K), blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F)) ∧
    ∀ (M M' : S → Submodule R (MvPolynomial (Fin k × Fin n) K)),
      (∀ s, ∀ F ∈ M s, rowAct K (g s) F ∈ M' s) → ∀ P ∈ tensorLat R K M, blockAct K g P ∈ tensorLat R K M'
def nablaLTw (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  Submodule.map ((LinearMap.lsmul K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (g.det ^ (-(lam (Fin.last m))))).restrictScalars R)
    (nablaL R K (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat) g)
def NablaLTwMem : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit g.det →
    ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      F ∈ nablaLTw R K m lam g ↔
        g.det ^ (lam (Fin.last m)) • rowAct K g F ∈
          Submodule.map (mapAlgHom (Algebra.ofId R K)).toLinearMap
            (dualWeyl R (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat))
end Formalism.GradedWeylDivisibility


