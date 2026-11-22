-- Prove2me | Definitions.Def_Formalism_LatticeLocalGlobal_LatticeLocalGlobalOfGlobal
-- name    : Formalism_LatticeLocalGlobal_LatticeLocalGlobalOfGlobal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:49.174205+00:00
-- url     : https://prove2.me/theorems/d464ed5f-cac7-4460-8d6b-3fb3d5d0f306
-- title:
--   Lattice Local Global Of Global
-- statement:
--   Definitions and structural lemmas for Lattice Local Global Of Global, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeLocalGlobal/LatticeLocalGlobalOfGlobal.lean

import Definitions.Def_Formalism_LatticeLocalGlobal_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeLocalGlobalTheory
open IsDedekindDomain
def OneMapIntegralBig : Prop :=
  ∀ (R L K V EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [Field K] [Algebra L K] [Algebra R K] [IsScalarTower R L K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup EE] [Module K EE] [Module R EE] [IsScalarTower R K EE]
    (N : Submodule R V) (RR : Submodule R EE) (B : V →ₗ[K] EE →ₗ[K] K)
    (ζ : HeightOneSpectrum R → L),
    Nonempty (HeightOneSpectrum R) →
    (∀ w : HeightOneSpectrum R, w.valuation L (ζ w) = 1) →
    (∀ w : HeightOneSpectrum R, ∀ φ ∈ N, ∀ F ∈ RR, ∃ p : L, w.valuation L p ≤ 1 ∧
      algebraMap L K (ζ w) * B φ F = algebraMap L K p) →
    ∃ β : N →ₗ[R] Module.Dual R RR,
      ∀ (φ : N) (F : RR), algebraMap R K (β φ F) = B (φ : V) (F : EE)
def SUnitIsUnit : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (s : R) (z : L), z ≠ 0 →
    (∃ n : ℕ, IsIntegral R (algebraMap R L s ^ n * z)) →
    (∃ n : ℕ, IsIntegral R (algebraMap R L s ^ n * z⁻¹)) →
    ∀ w : HeightOneSpectrum R, s ∉ w.asIdeal → w.valuation L z = 1
def LatticeLocalGlobalOfGlobal : Prop :=
  ∀ (R L EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (Λ₀ : Submodule R EE) (Λ' : HeightOneSpectrum R → Submodule R EE)
    (S : Finset (HeightOneSpectrum R)),
    Λ₀.FG → Submodule.span L (Λ₀ : Set EE) = ⊤ →
    (∀ w, (Λ' w).FG) → (∀ w, Submodule.span L (Λ' w : Set EE) = ⊤) →
    (∀ w, w ∉ S → Λ' w = Λ₀) →
    ∃ RR : Submodule R EE, (RR : Set EE) = {x : EE | ∀ w, x ∈ locAt w (Λ' w)} ∧ RR.FG ∧
      Submodule.span L (RR : Set EE) = ⊤ ∧ ∀ w, locAt w RR = locAt w (Λ' w)
def gramσ {K M n : Type} [CommRing K] [AddCommGroup M] [Module K M] (σ : K →+* K)
    (B : M →ₛₗ[σ] M →ₗ[K] K) (v : n → M) : Matrix n n K :=
  Matrix.of fun i j => B (v i) (v j)
def GramChangeσ : Prop :=
  ∀ (K M n : Type) [CommRing K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]
    (σ : K →+* K) (B : M →ₛₗ[σ] M →ₗ[K] K) (v : n → M) (g : Matrix n n K),
    gramσ σ B (fun j => ∑ i, g i j • v i) = (g.map σ).transpose * gramσ σ B v * g ∧
    (gramσ σ B (fun j => ∑ i, g i j • v i)).det = σ g.det * g.det * (gramσ σ B v).det
def DualGramσ : Prop :=
  ∀ (K M n : Type) [Field K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]
    (σ : K →+* K) (B : M →ₛₗ[σ] M →ₗ[K] K), (∀ x y, σ (B x y) = B y x) →
    ∀ (v : Module.Basis n K M) (w : n → M),
      (∀ i j, B (w i) (v j) = if i = j then 1 else 0) →
      gramσ σ B w = (gramσ σ B v)⁻¹ ∧ (gramσ σ B w).det * (gramσ σ B v).det = 1
def FormIsForm : Prop :=
  ∀ (k K E ι : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ W : Submodule k E, Module.finrank k W = Module.finrank K E →
      (∀ v ∈ W, ∀ i, ψ i v ∈ (algebraMap k K).range) →
      ∀ (m : Type) (b : Module.Basis m k W),
        LinearIndependent K (fun j => (b j : E)) ∧
          Submodule.span K (Set.range fun j => (b j : E)) = ⊤
def IndexWellDefined : Prop :=
  ∀ (R A n : Type) [CommRing R] [AddCommGroup A] [Module R A] [Fintype n] [DecidableEq n]
    (b b' : Module.Basis n R A), IsUnit (b.toMatrix b').det
def DescendIntegral : Prop :=
  ∀ (R L X : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup X] [Module L X]
    [Module R X] [IsScalarTower R L X]
    (Mt : Submodule R X) (U : Submodule L X) (f : X →ₗ[L] L),
    (∀ u ∈ U, f u = 0) → (∀ m ∈ Mt, f m ∈ (algebraMap R L).range) →
    ∃ g : (X ⧸ U) →ₗ[L] L, (∀ x, g (U.mkQ x) = f x) ∧
      ∀ y ∈ Mt.map ((U.mkQ).restrictScalars R), g y ∈ (algebraMap R L).range
def DetIntegral : Prop :=
  ∀ (R L n : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [Fintype n] [DecidableEq n]
    (w : HeightOneSpectrum R) (H : Matrix n n L) (c : L),
    (∀ i j, w.valuation L (c * H i j) ≤ 1) →
    w.valuation L (c ^ Fintype.card n * H.det) ≤ 1
def HeightFromPeriod : Prop :=
  ∀ (V EE Q : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup EE]
    [NormedSpace ℂ EE] [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (B : V →ₗ[ℂ] EE →ₗ[ℂ] ℂ) (P : V → Q → ℂ) (io : Q →ₗ[ℂ] EE) (c p : ℝ),
    Function.Surjective io → 0 < c → (∀ F, c * ‖F‖ ^ 2 ≤ ‖io F‖ ^ 2) →
    (∀ φ F, ‖B φ (io F)‖ = ‖P φ F‖) → (∀ φ F, ‖P φ F‖ ≤ p * ‖φ‖ * ‖F‖) →
    ∀ φ x, ‖B φ x‖ ^ 2 ≤ p ^ 2 / c * ‖φ‖ ^ 2 * ‖x‖ ^ 2
end Formalism.LatticeLocalGlobalTheory


