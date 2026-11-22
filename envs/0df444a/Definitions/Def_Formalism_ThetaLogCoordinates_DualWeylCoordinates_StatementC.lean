-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:52.426367+00:00
-- url     : https://prove2.me/theorems/787eb830-5b68-4b36-b0d3-66d7f0c723fe
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/StatementC.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def ClosureBasicModules : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (∀ M : GLMod n, Fintype.card M.ι = 1 → (∀ i j, M.A i j = 1) → Nonempty (ColFam M)) ∧
    (∀ (M : GLMod n) (mu : Fin n → ℤ) (β : M.ι → GLCoord ℤ n), Dominant mu → IsSMu M mu β → Nonempty (ColFam M)) ∧
    ∀ (M M' : GLMod n) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ e : M'.ι ≃ M.ι,
      (∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j)) →
      Nonempty (ColFam M) → Nonempty (ColFam M')
def ClosureTensorPowers : Prop :=
  ∀ (n : ℕ) [NeZero n] (M M' : GLMod n) (b : ℕ), Nonempty (ColFam M) →
    (∀ e, IsTensor M M' (SymMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (SymDMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (LamMat n b) e → Nonempty (ColFam M'))
def ClosureBranching : Prop :=
  ∀ (m : ℕ) [NeZero m] (M : GLMod (m + 1)) (lam : Fin (m + 1) → ℤ) (β : M.ι → GLCoord ℤ (m + 1)),
    Dominant lam → IsSMu M lam β →
    ∃ (Sg : Finset (Fin m → ℤ)) (ph : (nu : ↥Sg) → Matrix M.ι (TIdx (nu : Fin m → ℤ)) ℤ),
      (∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu) ∧
      (∀ (nu : ↥Sg) (R : Type) [CommRing R] (h : GL (Fin (m + 1)) R) (g1 : GL (Fin m) R) (t : Rˣ), IsBlock h g1 t →
        M.A.map (evGL h) * (ph nu).map (Int.castRingHom R) =
          (((t ^ (∑ a, lam a - ∑ a, (nu : Fin m → ℤ) a) : Rˣ) : R)) • ((ph nu).map (Int.castRingHom R) *
            (TMat (nu : Fin m → ℤ)).map (evGL g1))) ∧
      (∀ nu : ↥Sg, (∀ (p : ℕ), p.Prime → (fun i => ((ph nu i (canT _) : ℤ) : ZMod p)) ≠ 0) ∧
        (fun i => ((ph nu i (canT _) : ℤ) : ℚ)) ≠ 0) ∧
      Fintype.card M.ι = ∑ nu : ↥Sg, dMu (nu : Fin m → ℤ)
end Formalism.InvariantFactorPaths.ColumnFamilies


