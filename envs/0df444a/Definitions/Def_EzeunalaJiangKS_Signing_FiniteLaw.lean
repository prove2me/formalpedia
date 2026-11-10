-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_FiniteLaw
-- name    : EzeunalaJiangKS_Signing_FiniteLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:07:26.502083+00:00
-- url     : https://prove2.me/theorems/481f17d8-f102-41fb-bcf0-d33f32800f42
-- title:
--   Centered finite distributions of active directions
-- statement:
--   A finite direction law has an arbitrary positive finite number of atoms, nonnegative weights summing to one, and one real vector per atom, supported on active coordinates. Centering means that the weighted mean of every coordinate is zero. Expectations are their actual weighted sums. Define
--   $$\omega_i=T_i^2\mathbb E[h_i^2].$$
--   This represents any centered finitely supported distribution, without fixing its support size in advance. The fields store only weights and vectors; the separate validity predicate imposes the probability and support conditions, and contains no desired energy inequality.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §4.2, Lemma 4.7, printed p. 19 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Energy

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- The atom count is part of the witness, never fixed before the state. -/
structure FiniteDirection (N : ℕ) where
  atoms : ℕ
  prob : Fin atoms → ℝ
  value : Fin atoms → State N

def FiniteDirection.valid {N : ℕ} (D : FiniteDirection N) (x : State N) : Prop :=
  0 < D.atoms ∧ (∀ a, 0 ≤ D.prob a) ∧ (∑ a, D.prob a) = 1 ∧
    (∀ a, faceDirection x (D.value a)) ∧ ∀ i, (∑ a, D.prob a * D.value a i) = 0

def FiniteDirection.expect {N : ℕ} (D : FiniteDirection N) (f : State N → ℝ) : ℝ :=
  ∑ a, D.prob a * f (D.value a)

def motionWeight {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N)
    (D : FiniteDirection N) (i : Fin N) : ℝ :=
  (coordinateScale A x₀ x i)^2 * D.expect (fun h => (h i)^2)

end EzeunalaJiangKS.Signing


