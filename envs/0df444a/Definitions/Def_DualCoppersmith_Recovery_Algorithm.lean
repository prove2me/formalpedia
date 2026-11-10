-- Prove2me | Definitions.Def_DualCoppersmith_Recovery_Algorithm
-- name    : DualCoppersmith_Recovery_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:55:28.345637+00:00
-- url     : https://prove2.me/theorems/f43cac50-740f-43d4-8d71-3e0114b5beab
-- title:
--   Algorithm 2: basis construction, reduction and verified decoding
-- statement:
--   Algorithm 2 takes only the prime, polynomial relations, positive integer bounds, shift parameters and a specified reduction routine. It constructs the exact shift kernel, selects a basis of that kernel, applies the integer diagonal scaling, and passes that input-derived basis to the routine. If $w$ is the first reduced vector and $w_0\ne0$, its candidates are the exact rationals
--
--   $$c_i=\frac{X_iw_{e_i}}{w_0}.$$
--
--   It returns failure when the constant coordinate is zero, any candidate is nonintegral, or the candidate fails the strict box or any original modular relation. Otherwise it returns the integer candidate. Every check remains operational on every input. An initial exact integrality check on the real-coordinate presentation of $w$ makes the function total on arbitrary routines; it always passes for a certified basis of this integral lattice.
--
--   The output is an optional signed integer vector. Kernel-basis existence is not an input hypothesis: it follows from the explicit kernel containing $p^m\mathbb Z^n$. The reduction validity predicate concerns only the selected input basis and its actual output. The target root occurs neither in the input nor in the subroutine contract.
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 9, Algorithm 2, lines 1–12 (PDF p. 10); p. 10, decoding verification (PDF p. 11)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Lattice
import Definitions.Def_DualCoppersmith_Recovery_Geometry

set_option autoImplicit false

namespace DualCoppersmith.Recovery

open LLLFactor.RedBasis

noncomputable def scaledBasis (I : Instance) (P : Parameters I)
    (b : Fin (dimension I P) → Vec (dimension I P)) :
    Fin (dimension I P) → Vec (dimension I P) :=
  fun j => diagonalMap I P (b j)

/-- Quality of the actual input-derived call only; no target root appears. -/
def ValidReduction (I : Instance) (P : Parameters I) (delta : ℝ)
    (reduce : Reduction (dimension I P)) : Prop :=
  1 ≤ delta ∧ ∀ b, selectBasis (kernelLattice I P) = some b →
    IsLLLCall delta (scaledBasis I P b) (reduce (scaledBasis I P b))

/-- Rational data are recovered from the exactly integral reduced vector.
    Nonintegral real coordinates are rejected as an additional totality guard,
    unreachable for a genuine basis of this integral lattice. -/
noncomputable def rationalVector {n : ℕ} (w : Vec n) : Option (Fin n → ℚ) := by
  classical
  exact if h : ∃ z : Fin n → ℤ, ∀ j, (z j : ℝ) = w j
    then some (fun j => (h.choose j : ℚ)) else none

/-- Algorithm 2, lines 4--12. Every check is performed on every candidate. -/
noncomputable def decode (I : Instance) (P : Parameters I)
    (w : Vec (dimension I P)) : Option (Fin I.ell → ℤ) := by
  classical
  exact do
    let z ← rationalVector w
    if z (constantIndex I P) = 0 then none else
      let c : Fin I.ell → ℚ := fun i =>
        (I.X i : ℚ) * z (linearIndex I P i) / z (constantIndex I P)
      if h : ∃ r : Fin I.ell → ℤ, ∀ i, (r i : ℚ) = c i then
        let r := h.choose
        if IsBoundedRoot I r then some r else none
      else none

/-- Complete input-only pipeline: exact coefficient rows, kernel basis, diagonal
    scaling, reduction, first vector, guarded rational decoding, verification. -/
noncomputable def algorithm2 (I : Instance) (P : Parameters I)
    (reduce : Reduction (dimension I P)) : Option (Fin I.ell → ℤ) := by
  classical
  exact do
    let b ← selectBasis (kernelLattice I P)
    let c := reduce (scaledBasis I P b)
    if hn : 0 < dimension I P then decode I P (c ⟨0, hn⟩) else none

end DualCoppersmith.Recovery


