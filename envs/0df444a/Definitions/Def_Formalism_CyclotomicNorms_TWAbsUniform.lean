-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_TWAbsUniform
-- name    : Formalism_CyclotomicNorms_TWAbsUniform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:07.275646+00:00
-- url     : https://prove2.me/theorems/bad8294f-897f-40c3-94e9-0222885ff727
-- title:
--   TWAbs Uniform
-- statement:
--   Definitions and structural lemmas for TWAbs Uniform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/TWAbsUniform.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
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
def TWAbsUniform : Prop :=
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
    ∀ ε : ℝ, 0 < ε →
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧ ∀ sg : Sig ⊕ JJ → ℤˣ,
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
end Formalism.CyclotomicNorms


