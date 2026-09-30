-- Prove2me | Definitions.Def_SP4GradedLaurent
-- name    : SP4GradedLaurent
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T01:57:12.201875+00:00
-- url     : https://prove2.me/theorems/7387d59a-01db-482c-8928-e5b98043a87d
-- title:
--   Finite graded Laurent data and Euler evaluations
-- statement:
--   A finite integer Laurent polynomial is a finitely supported coefficient function on the integer degrees. The grading shift sends $P(q)$ to $q^kP(q)$, and the two-degree factor sends $P(q)$ to $(1+q^{-1})P(q)$. The interface supplies additive evaluations $P(1)$ and $P(-1)$ and the signed first moment $∑_m m(-1)^m P_m$. Coefficients remain integers, independently of any coefficient field used in a later chain-complex application. This interface contains no chain complex, Floer realization, or geometric assertion.
--
--   $$
--   P(1)=\sum_m P_m,\qquad P(-1)=\sum_m(-1)^mP_m,\qquad
--   \Psi(P)=\sum_m m(-1)^mP_m.
--   $$
-- source:
--   Local research notes, Cycle 18, A basis-free parity obstruction from saturation and common normalization, Sections 2–3, equations (1)–(4); independent critical audit Sections 1–3. This formalization extracts only their integer Laurent-polynomial implication. The actual graded-complex rank-nullity bridge and applications to named source tables are not included. Primary note: cycle18_structural_primary_proof.md, SHA-256 68da60b83072393fd9491dae22acb095ffce76a18a1285658417457df46188e4.

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-! Finite integer graded-dimension data. Coefficients are integers, never
reduced modulo the characteristic of a chain-complex coefficient field. -/
namespace SP4GradedLaurent

abbrev GradedPolynomial := ℤ →₀ ℤ

noncomputable def sign (m : ℤ) : ℤ := m.negOnePow

noncomputable def shift (k : ℤ) (P : GradedPolynomial) : GradedPolynomial :=
  P.mapDomain (fun m => k + m)

/-- Multiplication by the two-degree factor `1 + q⁻¹`. -/
noncomputable def tensorV (P : GradedPolynomial) : GradedPolynomial :=
  P + shift (-1) P

noncomputable def weightSum (w : ℤ → ℤ) : GradedPolynomial →+ ℤ where
  toFun P := P.sum (fun m c => w m * c)
  map_zero' := by simp
  map_add' P Q := by
    exact Finsupp.sum_add_index (by simp) (by intros; simp [mul_add])

/-- Evaluation at `q = 1`. For a rank polynomial, this is total rank. -/
noncomputable def mass : GradedPolynomial →+ ℤ := weightSum (fun _ => 1)

/-- Evaluation at `q = -1`. -/
noncomputable def euler : GradedPolynomial →+ ℤ := weightSum sign

/-- Evaluation of `q P'(q)` at `q = -1`, defined without analytic derivatives. -/
noncomputable def signedMoment : GradedPolynomial →+ ℤ :=
  weightSum (fun m => m * sign m)

end SP4GradedLaurent


