-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Green
-- name    : KramersHubbard_PartitionFunction_Green
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:49.756212+00:00
-- url     : https://prove2.me/theorems/1ad8df2a-01e2-48c6-bee1-10fe7ab6c8da
-- title:
--   The concrete thermal Green matrix
-- statement:
--   Every insertion $k$ contributes the two columns
--
--   $$R_k^\pm=c_k^{1/4}e^{\pm\tau_kh}[v_{i_k},w_{i_k}].$$
--
--   The global Green matrix applies Eq.(28) to the ordered columns of $R_k^+$ and $R_k^-$. Thus its entry uses $y_j^\dagger\rho x_i$ when the row follows or equals the column and $-y_j^\dagger(I-\rho)x_i$ otherwise. This includes the upper-right diagonal-block entry with its minus sign. Scalar products are evaluated in the raw input basis; they are unchanged by passage to a Kramers basis. The fourth root is two nested nonnegative square roots. This module assumes no quaternionicity, determinant positivity or expansion identity: these are later conclusions.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Eqs.(28), (30)-(32), pp.14-15; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Trotter
import Definitions.Def_KramersHubbard_PartitionFunction_Quaternion

noncomputable section
open scoped BigOperators
open Matrix

namespace KramersHubbard.PartitionFunction

/-- The canonical matrix of Θv=-J conjugate(v) in the paper's Kramers basis. -/
def canonicalTheta (N : ℕ) : OneOp N := fun a b =>
  if a.val / 2 = b.val / 2 then
    if a.val % 2 = 0 ∧ b.val % 2 = 1 then -1
    else if a.val % 2 = 1 ∧ b.val % 2 = 0 then 1 else 0
  else 0

/-- Columns of R±, Eq.(30). -/
def greenVector {N r M} (D : Data N r) (β : ℝ) (sgn : ℝ)
    (a : Insertion M r × Fin 2) : Vec N :=
  let k := a.1
  let i := interactionIndex k
  (Real.sqrt (Real.sqrt (coupling D β M i)) : ℂ) •
    (NormedSpace.exp ((sgn * insertionTime β k : ℝ) • D.h)).mulVec
      (if a.2 = 0 then D.v i else partner D i)

/-- Eq.(28) applied to the full ordered columns (30)-(31), including the diagonal's
    upper-right minus (I-rho) entry. -/
def green {N r M} (D : Data N r) (β : ℝ) :
    Matrix (Insertion M r × Fin 2) (Insertion M r × Fin 2) ℂ := fun a b =>
  let x := greenVector D β 1 b
  let y := greenVector D β (-1) a
  if b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2 ≤ a.2) then
    dotProduct (star y) ((density D β).mulVec x)
  else -dotProduct (star y) ((1 - density D β).mulVec x)

end KramersHubbard.PartitionFunction


