-- Prove2me | Definitions.Def_PeterfalviProblem_Basic_Witness
-- name    : PeterfalviProblem_Basic_Witness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:05:42.332545+00:00
-- url     : https://prove2.me/theorems/1042f6bf-da87-492a-8c07-4c8ac63b3aeb
-- title:
--   Witness
-- statement:
--   Definitions and structural lemmas for Witness, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/Witness.lean

import Definitions.Def_PeterfalviProblem_Basic_FrobeniusGroup
set_option autoImplicit false
namespace PeterfalviProblem
open scoped Pointwise
variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
variable (p q G) in
/-- A witness of hypothesis (B) for the primes `p`, `q` and the group `G`, with condition (A).

The subgroups `P`, `U` and `P₀` of `G` are the images of `normOneFrobeniusKernel p q`,
`normOneFrobeniusComplement p q` and `primeLine p q` under `sigma`. The element `y` is the
inverse of the element `y` of hypothesis (B); see the module docstring. -/
structure Witness where
  /-- The injective homomorphism `σ : H → G`. -/
  sigma : normOneFrobeniusGroup p q →* G
  sigma_injective : Function.Injective sigma
  /-- The finite abelian subgroup `Q` of `G`, of order prime to `p`. -/
  Q : Subgroup G
  Q_finite : Finite Q
  Q_commutative : IsMulCommutative Q
  Q_pPrime : ¬ p ∣ Nat.card Q
  /-- The element `y ∈ Q`: the inverse of the element `y` of hypothesis (B). -/
  y : G
  y_mem_Q : y ∈ Q
  /-- The image `P = σ(P)`. -/
  P : Subgroup G
  /-- The image `U = σ(U)`. -/
  U : Subgroup G
  /-- The image `P₀ = σ(P₀)`. -/
  P0 : Subgroup G
  sigma_P_eq_P : (normOneFrobeniusKernel p q).map sigma = P
  sigma_U_eq_U : (normOneFrobeniusComplement p q).map sigma = U
  sigma_P0_eq_P0 : (primeLine p q).map sigma = P0
  /-- `σ(P₀)` normalizes `Q`. -/
  P0_normalizes_Q : P0 ≤ Subgroup.normalizer (Q : Set G)
  /-- `y σ(P₀) y⁻¹` normalizes `σ(U)`. -/
  P0_conj_y_normalizes_U : MulAut.conj y • P0 ≤ Subgroup.normalizer (U : Set G)
  q_prime : q.Prime
  /-- Condition (A): `q ∤ p - 1`. -/
  q_not_dvd : ¬ q ∣ p - 1
namespace Witness
noncomputable def s (data : Witness p q G) : G :=
  data.sigma (primeLineGenerator p q)
end Witness
end PeterfalviProblem


