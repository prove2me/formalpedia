-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_StatementTW
-- name    : Formalism_CyclotomicNorms_StatementTW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:12:28.957044+00:00
-- url     : https://prove2.me/theorems/9658cbed-dbd2-47c9-9491-fe02c2e5e21b
-- title:
--   Statement TW
-- statement:
--   Definitions and structural lemmas for Statement TW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/StatementTW.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.CyclotomicNorms
def vl {L : Type*} [NormedField L] (ℓ : ℕ) (x : L) : ℝ := -Real.logb ℓ ‖x‖
def GTLemma : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e J M k₀ : ℕ) (h : Fin J → K[X]) (w : Fin J → ℕ) (vv : Fin J → ℝ) (ε : ℝ)
    (X : Finset ℕ),
    ℓ.Prime → 0 < e → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ j i, ‖(h j).coeff i‖ ≤ 1) →
    (∀ j, w j ≤ M ∧ (h j).coeff (w j) ≠ 0 ∧ vl ℓ ((h j).coeff (w j)) ≤ vv j) →
    0 < ε → 1 ≤ k₀ → 2 * (J : ℝ) * M / ε ≤ ((ℓ ^ k₀).totient : ℝ) → (e : ℝ) * ε < k₀ →
    ∃ k : ℕ, k₀ ≤ k ∧
      (k : ℝ) ≤ (k₀ + X.card + J * M + 1) * Real.exp (2 * (∑ j, vv j) / ε) + 1 ∧ k ∉ X ∧
      (∀ ζ ∈ primitiveRoots (ℓ ^ k) L, ∀ j, ((h j).map (algebraMap K L)).eval (ζ - 1) ≠ 0) ∧
      (∑ ζ ∈ primitiveRoots (ℓ ^ k) L, ∑ j, vl ℓ (((h j).map (algebraMap K L)).eval (ζ - 1))) ≤
        ((ℓ ^ k).totient : ℝ) * ((∑ j, vv j) + ε) ∧
      ∃ ζ ∈ primitiveRoots (ℓ ^ k) L, ∃ εj : Fin J → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
        ∀ j, vl ℓ (((h j).map (algebraMap K L)).eval (ζ - 1)) ≤ vv j + εj j
def lamIdeal (A σ : Type) [CommRing A] (ℓ M : ℕ) : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range fun i : σ => (1 + MvPolynomial.X i) ^ (ℓ ^ M) - 1)
def varIdeal (A σ : Type) [CommRing A] : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range MvPolynomial.X)
def redLam (O σ : Type) [CommRing O] [IsLocalRing O] (ℓ M : ℕ) :
    MvPolynomial σ O →+*
      MvPolynomial σ (IsLocalRing.ResidueField O) ⧸ lamIdeal (IsLocalRing.ResidueField O) σ ℓ M :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map (IsLocalRing.residue O))
def FewFactors {O σ : Type} [CommRing O] [IsLocalRing O] (ℓ M m : ℕ) (D : MvPolynomial σ O) :
    Prop :=
  ∃ (n : ℕ) (φ : Fin n →
      MvPolynomial σ (IsLocalRing.ResidueField O) ⧸ lamIdeal (IsLocalRing.ResidueField O) σ ℓ M),
    n ≤ m ∧ redLam O σ ℓ M D = ∏ a, φ a ∧
    ∀ a, IsUnit (φ a) ∨ ∃ (i : σ) (u : MvPolynomial σ (IsLocalRing.ResidueField O) ⧸
        lamIdeal (IsLocalRing.ResidueField O) σ ℓ M),
      IsUnit u ∧ φ a = Ideal.Quotient.mk _ (MvPolynomial.X i) * u
def evTw {L : Type} [Field L] {R' : ℕ} (ℓ : ℕ) (z : L) (e'' e' : Fin R' → ℕ) (a : ℤˣ) :
    Fin R' ⊕ Fin R' → L :=
  Sum.elim (fun i => z ^ ((a : ℤ) * ((ℓ ^ e'' i : ℕ) : ℤ)) - 1)
    (fun i => z ^ ((a : ℤ) * ((ℓ ^ e' i : ℕ) : ℤ)) - 1)
def TWAbs : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e e₀ R' D' m₁ t M₀ : ℕ) (O₀ O : Subring K) [IsDiscreteValuationRing O₀]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O₀)] (w₀ : O₀) (w : O)
    (Sig JJ : Type) [Fintype Sig] [Fintype JJ] (vv : JJ → ℝ)
    (F : ℕ → Sig → MvPolynomial (Fin R' ⊕ Fin R') O₀)
    (f : ℕ → JJ → MvPolynomial (Fin R' ⊕ Fin R') O) (D g : ℕ → JJ → MvPolynomial (Fin R') O),
    ℓ.Prime → 0 < e → 0 < e₀ → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ x : O₀, ‖(x : K)‖ ≤ 1) → (∀ x : O, ‖(x : K)‖ ≤ 1) →
    Irreducible w₀ → Irreducible w → vl ℓ (w₀ : K) = 1 / e₀ → vl ℓ (w : K) = 1 / e →
    (∀ j, ∃ n : ℕ, vv j = n / e) →

    (∀ M, M₀ ≤ M → ∀ s, F M s ∉
      Ideal.span {MvPolynomial.C ((ℓ : O₀) ^ (if ℓ = 2 then 1 else 0) * w₀)} +
        varIdeal O₀ (Fin R' ⊕ Fin R') ^ (D' + 1) + lamIdeal O₀ (Fin R' ⊕ Fin R') ℓ M) →

    (∀ M, M₀ ≤ M → ∀ j,
      MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) (f M j) - D M j * g M j ∈
        lamIdeal O (Fin R') ℓ M ∧
      ((MvPolynomial.constantCoeff (g M j) : O) : K) ≠ 0 ∧
      vl ℓ ((MvPolynomial.constantCoeff (g M j) : O) : K) = vv j ∧
      FewFactors ℓ M m₁ (D M j)) →
    ∀ ε : ℝ, 0 < ε → ∀ sg : Sig ⊕ JJ → ℤˣ,
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧
        (∀ s, MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s) ≠ 0) ∧
        (∀ j, MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j) ≠ 0) ∧
        ∑ s, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s)) ≤
          (if ℓ = 2 then 1 else 0) * (Fintype.card Sig : ℝ) + ε ∧
        (∃ εj : JJ → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
          ∀ j, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j)) ≤ vv j + εj j) ∧
        2 * (t : ℝ) * ∑ i, (vl ℓ (z ^ (ℓ ^ e'' i) - 1) + vl ℓ (z ^ (ℓ ^ e' i) - 1)) ≤ ε
def genB {k : Type} [Field k] {m r d R : ℕ} (u : Matrix (Fin R × Bool × Fin r) (Fin m) k)
    (us : Matrix (Fin R × Bool × Fin r) (Fin d) k) (i : Fin R) (x : Fin m → k) (y : Fin d → k) :
    k :=
  ∑ b : Bool, ∑ ρ : Fin r, (u.mulVec x) (i, b, ρ) * (us.mulVec y) (i, b, ρ)
def RESCore : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ P, (t.mulVec x) P * (us.mulVec y) P = 0) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K')))) +
      (Matrix.of fun p q : Fin d => ∑ i, s i * algebraMap k K'
        (genB u us i (bSel p : Fin m → k) (Pi.single q 1))).rank ≤ d
abbrev TruncK (K' : Type) [Field K'] (n : ℕ) : Type := K'[X] ⧸ Ideal.span {(X : K'[X]) ^ n}
def RESModule : Prop :=
  ∀ (K' : Type) [Field K'] (n a C : ℕ) (Φ : Matrix (Fin a) (Fin a) (TruncK K' n))
    (N : Submodule (TruncK K' n) (Fin a → TruncK K' n)),
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    ((∀ x ∈ N, (Ideal.Quotient.mk _ X : TruncK K' n) • x = 0 → x = 0) →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → Module.finrank K' ↥(N ⊓ LinearMap.ker
        ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1 →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})
def gramB {k : Type} [Field k] {m r d R : ℕ} (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k)
    (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))) (i : Fin R) :
    Matrix (Fin d) (Fin d) k :=
  Matrix.of fun p q => genB u us i (bSel p : Fin m → k) (Pi.single q 1)
def RESAbs : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R n a C : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t)))
    (Φ : Matrix (Fin a) (Fin a) (TruncK K' n)) (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (ι : ↥(N ⊓ LinearMap.ker ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) →ₗ[K']
      ↥(LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K'))))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ P, (t.mulVec x) P * (us.mulVec y) P = 0) →
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    Function.Injective ι →
    (Submodule.span k (Set.range (gramB u t us bSel)) = ⊤ →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → d - 1 ≤ (∑ i, s i • (gramB u t us bSel i).map (algebraMap k K')).rank →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})
end Formalism.CyclotomicNorms


