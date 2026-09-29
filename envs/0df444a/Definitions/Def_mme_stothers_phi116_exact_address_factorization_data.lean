-- Prove2me | Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
-- name    : mme_stothers_phi116_exact_address_factorization_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T20:09:28.842133+00:00
-- url     : https://prove2.me/theorems/e9f0013c-ecc2-47f2-b2b1-4663cc4725ec
-- title:
--   Exact-address component data for the phi_116 extraction
-- statement:
--   For the exact outer addresses used in the $\varphi_{116}$ extraction, this module labels the four supported coordinate types $000,111,012,102$ by $\{0,1,2,3\}$, records their prescribed multiplicities $(\alpha,\alpha,\beta,\beta)$, and associates the payload tensors $D_6,D_6,\langle12,1,12\rangle,\langle12,1,12\rangle$.
--
--   These definitions provide the finite indexing interface needed to count address fibers and regroup the literal address tensor into four Kronecker powers.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_outer_grading
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_tensor_bridge

open MME

universe u

namespace MME.StothersFourth.Phi116

set_option autoImplicit false

/-- Encode one supported outer coordinate by its ordered `phi_116`
component. On supported coordinates this is
`000 ↦ 0`, `111 ↦ 1`, `012 ↦ 2`, `102 ↦ 3`. -/
def phi116OuterComponent {N : ℕ} (a : CWQ6CoupledAddress N)
    (j : Fin (2 * N)) : Fin 4 :=
  if a 2 j = 0 then 0
  else if a 2 j = 1 then 1
  else if a 0 j = 0 then 2
  else 3

/-- The source profile `(alpha, alpha, beta, beta)`. -/
def phi116ComponentMultiplicity (alpha beta : ℕ) (u : Fin 4) : ℕ :=
  if u = 0 then alpha else if u = 1 then alpha else beta

/-- Algebraic payloads in source order `000`, `111`, `012`, `102`. -/
noncomputable def phi116ComponentObj
    (K : Type u) [Field K] : Fin 4 → TensorObj K 3 :=
  ![coupledObj K 6, coupledObj K 6,
    MMObj K 12 1 12, MMObj K 12 1 12]

/-- The four supported outer addresses in source order. -/
def phi116ComponentAddress : Fin 4 → Fin 3 → Fin 3 :=
  ![![0, 0, 0], ![1, 1, 1], ![0, 1, 2], ![1, 0, 2]]

end MME.StothersFourth.Phi116


