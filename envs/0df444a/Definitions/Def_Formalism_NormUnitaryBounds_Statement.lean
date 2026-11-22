-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- name    : Formalism_NormUnitaryBounds_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:48:43.799801+00:00
-- url     : https://prove2.me/theorems/8549fbd9-2a12-4b11-858b-97058f1e2638
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.NormUnitaryCountingLemmas
section Poly
variable (R : Type*) [CommRing R]
def blockWt (N n : ℕ) : Fin N × Fin n → (Fin N → ℕ) := fun p => Pi.single p.1 1
def coordWt (N n : ℕ) : Fin N × Fin n → (Fin n → ℕ) := fun p => Pi.single p.2 1
def coordKWt (N n : ℕ) (k : Fin n) : Fin N × Fin n → ℕ := fun p => if p.2 = k then 1 else 0
def shear {N n : ℕ} (i j : Fin N) :
    MvPolynomial (Fin N × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin N × Fin n) R) :=
  aeval fun p => Polynomial.C (X p) +
    (if p.1 = j then Polynomial.X * Polynomial.C (X (i, p.2)) else 0)
def H {N n : ℕ} (ν : Fin N → ℕ) : Submodule R (MvPolynomial (Fin N × Fin n) R) :=
  weightedHomogeneousSubmodule R (blockWt N n) ν ⊓
    ⨅ (i : Fin N) (j : Fin N) (_ : i < j),
      LinearMap.ker ((shear R i j).toLinearMap -
        (IsScalarTower.toAlgHom R (MvPolynomial (Fin N × Fin n) R)
          (Polynomial (MvPolynomial (Fin N × Fin n) R))).toLinearMap)
def detPoly (N : ℕ) : MvPolynomial (Fin N × Fin N) R :=
  (Matrix.of fun (j k : Fin N) => (X (j, k) : MvPolynomial (Fin N × Fin N) R)).det
end Poly
def H1 : Prop :=
  ∀ (R : Type*) [CommRing R] (N n : ℕ) (ν : Fin (N + 1) → ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin n) R), F ∈ H R ν →
    ∀ (A : Type*) [CommRing A] [Algebra R A] (x : Fin (N + 1) → Fin n → A) (u : Fin n → A)
      (c : Fin (N + 1) → A),
      (aeval (fun p : Fin (N + 1) × Fin n =>
        Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2)) F).natDegree ≤ ν 0
def H2 : Prop :=
  ∀ (R : Type*) [CommRing R] (N N' : ℕ) (hN : N ≤ N') (ν : Fin N → ℕ)
    (F : MvPolynomial (Fin N × Fin N') R), F ∈ H R ν → ∀ w : ℕ,
    rename (fun p : Fin N × Fin N' => (Fin.castLE hN p.1, p.2)) F * detPoly R N' ^ w ∈
      H R (fun j : Fin N' => (if h : (j : ℕ) < N then ν ⟨j, h⟩ else 0) + w)
def NormUnitaryPermutationInvariance : Prop :=
  ∀ (R : Type*) [CommRing R] (N n : ℕ) (ν : Fin N → ℕ) (σ : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin N × Fin n) R), F ∈ H R ν →
    rename (fun p : Fin N × Fin n => (p.1, σ p.2)) F ∈ H R ν
def NormUnitaryWeight : Prop :=
  ∀ (R : Type*) [CommRing R] (N n : ℕ) (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R),
    F ∈ H R ν → ∀ w : Fin n → ℕ, weightedHomogeneousComponent (coordWt N n) w F ∈ H R ν
def NormUnitaryCount : Prop :=
  ∀ (K : Type*) [Field K] (N n : ℕ) (ν : Fin N → ℕ) (k : Fin n),
    n * ∑ i ∈ Finset.range (∑ j, ν j + 1),
        i * Module.finrank K (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i :
          Submodule K (MvPolynomial (Fin N × Fin n) K)) =
      (∑ j, ν j) * Module.finrank K (H K (n := n) ν)
def blockDeg {N n : ℕ} (e : (Fin N × Fin n) →₀ ℕ) (j : Fin N) : ℕ := ∑ k : Fin n, e (j, k)
def bweight {N n : ℕ} (e : (Fin N × Fin n) →₀ ℕ) : ℝ :=
  ∏ j : Fin N, ((∏ k : Fin n, (e (j, k)).factorial : ℕ) : ℝ) / ((blockDeg e j).factorial : ℝ)
def bnormSq {N n : ℕ} (F : MvPolynomial (Fin N × Fin n) ℂ) : ℝ :=
  ∑ e ∈ F.support, ‖F.coeff e‖ ^ 2 * bweight e
def bnorm {N n : ℕ} (F : MvPolynomial (Fin N × Fin n) ℂ) : ℝ := Real.sqrt (bnormSq F)
def linSubst {N n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (F : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial (Fin N × Fin n) ℂ :=
  aeval (fun p : Fin N × Fin n => ∑ l : Fin n, C (U p.2 l) * X (p.1, l)) F
def NormUnitary : Prop :=
  ∀ (N n : ℕ) (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) ℂ),
    F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, bnorm (linSubst U F) = bnorm F
def NormMul : Prop :=
  ∀ (N n : ℕ) (ν μ : Fin N → ℕ) (F G : MvPolynomial (Fin N × Fin n) ℂ),
    F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν →
    G ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) μ →
    bnorm (F * G) ≤ bnorm F * bnorm G
def NormEval : Prop :=
  ∀ (N n : ℕ) (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) ℂ),
    F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν →
    ∀ x : Fin N → Fin n → ℂ,
      ‖eval (fun p : Fin N × Fin n => x p.1 p.2) F‖ ≤
        bnorm F * ∏ j : Fin N, Real.sqrt (∑ k : Fin n, ‖x j k‖ ^ 2) ^ ν j
def NormDet : Prop :=
  ∀ N : ℕ, bnorm (detPoly ℂ N) = Real.sqrt (N.factorial : ℝ)
def ShortIndependentVectorsOfDualMinimum : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℤ E), DiscreteTopology M → Submodule.span ℝ (M : Set E) = ⊤ →
    ∀ l : ℝ, 0 < l →
    (∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) →
    ∃ v : Fin (Module.finrank ℝ E) → E, (∀ i, v i ∈ M) ∧ LinearIndependent ℝ v ∧
      ∀ i, ‖v i‖ ≤ (Module.finrank ℝ E : ℝ) ^ ((3 : ℝ) / 2) / l
def CB : Prop :=
  ∀ (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (S : Type*) [AddCommGroup S] [Module R S] [Module.Free R S] (Nsub : Submodule R S) (n : ℕ),
    Module.length R (S ⧸ Nsub) ≤ (n : ℕ∞) →
  ∀ (I : Type*) (Φ : S →ₗ[R] (I → FractionRing R)) (e : ℤ),
    (∀ x ∈ Nsub, ∀ i : I, ∃ r : R,
      algebraMap R (FractionRing R) ϖ ^ e * Φ x i = algebraMap R (FractionRing R) r) →
  ∀ (ρ : ℕ) (φ : Fin ρ → S) (J : Fin ρ → I), ∃ r : R,
    algebraMap R (FractionRing R) ϖ ^ ((n : ℤ) + (ρ : ℤ) * e) *
        (Matrix.of fun a b : Fin ρ => Φ (φ a) (J b)).det = algebraMap R (FractionRing R) r
def N1 : Prop :=
  ∀ (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ),
    (∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z)) →
    (∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2)) →
    ∀ e : Fin G → ℕ, ‖c e‖ ^ 2 ≤ S ^ 2 * ∏ i, (Real.exp 1 / (e i : ℝ)) ^ e i
def NormOneFactorization : Prop :=
  ∀ (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ),
    (∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z)) →
    (∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2)) →
    ∀ e : Fin G → ℕ, (∏ i, ((e i).factorial : ℝ)) * ‖c e‖ ^ 2 ≤
      S ^ 2 * ∏ i, Real.sqrt (Real.exp 1 ^ 2 * max 1 (e i : ℝ))
def NormOneSum : Prop :=
  ∀ (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ),
    (∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z)) →
    (∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2)) →
    ∀ (β : Type*) [Fintype β] [DecidableEq β] (b : Fin G → β) (m : β → ℕ),
      ∑ e ∈ (Fintype.piFinset fun _ : Fin G => Finset.range (∑ τ, m τ + 1)) with
          (∀ τ, ∑ i with b i = τ, e i = m τ),
        (∏ i, ((e i).factorial : ℝ)) * ‖c e‖ ^ 2 ≤
      S ^ 2 * (Real.exp 1 * (((∑ τ, m τ : ℕ) : ℝ) + 1)) ^ (2 * G)
def autPoly {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (t : ℕ) (a : E) : MvPolynomial (Fin n) ℝ :=
  ∏ j ∈ Finset.Ico (-(t : ℤ)) t, ((∑ k : Fin n, C (inner ℝ a (b k)) * X k) - C (j : ℝ))
def AUTindep : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (t : ℕ) (A : Finset E),
    (∀ a ∈ A, inner ℝ a a = (t : ℝ)) → (∀ a ∈ A, ∀ a' ∈ A, ∃ z : ℤ, inner ℝ a a' = (z : ℝ)) →
    LinearIndependent ℝ (fun a : A => autPoly b t (a : E))
def AUTcount : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (t : ℕ) (A : Finset E),
    (∀ a ∈ A, inner ℝ a a = (t : ℝ)) → (∀ a ∈ A, ∀ a' ∈ A, ∃ z : ℤ, inner ℝ a a' = (z : ℝ)) →
    A.card ≤ Nat.choose (Module.finrank ℝ E + 2 * t) (2 * t)
end Formalism.NormUnitaryCountingLemmas


