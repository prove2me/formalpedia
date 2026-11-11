-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Quaternion
-- name    : KramersHubbard_PartitionFunction_Quaternion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:23.158135+00:00
-- url     : https://prove2.me/theorems/572f3c39-c365-4a17-a161-917b074306bf
-- title:
--   Quaternionic blocks, whole-block minors and their polynomial
-- statement:
--   A rectangular complex matrix grouped into consecutive $2\times2$ blocks is quaternionic when every block is
--
--   $$\begin{pmatrix}\alpha&-\overline\gamma\\\gamma&\overline\alpha\end{pmatrix}.$$
--
--   For equal-size block-index sets $A,B$, $G[A,B]$ keeps both scalar rows and both scalar columns of each selected block, in increasing block order. Its determinant is complex-valued, with $\det G[\varnothing,\varnothing]=1$. The outside-domain unequal-size branch is $0$ and is never counted in a square minor sum. Define the repeated-block diagonal matrices $D_x$ and
--
--   $$g_G(y,z)=\sum_{|A|=|B|}\det G[A,B]z^Ay^{[p]\setminus B}.$$
--
--   The positive orthant is the Cartesian product of the strictly positive coordinate cones for $y$ and $z$. No Hermiticity or positivity is included in quaternionicity.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Eqs.(12)-(13), (43), pp.11,18; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Mathlib

noncomputable section
open scoped BigOperators
open Matrix

namespace KramersHubbard.PartitionFunction

/-- Consecutive whole 2-by-2 blocks, Eq.(13), with no Hermiticity condition. -/
def Quaternionic {ι κ : Type*} (Q : Matrix (ι × Fin 2) (κ × Fin 2) ℂ) : Prop :=
  ∀ i j, Q (i, 0) (j, 1) = -star (Q (i, 1) (j, 0)) ∧
    Q (i, 1) (j, 1) = star (Q (i, 0) (j, 0))

/-- Select both rows and columns of each block in inherited increasing order. -/
def blockDet {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (A B : Finset (Fin p)) : ℂ :=
  if h : A.card = B.card then
    Matrix.det (fun a b : Fin A.card × Fin 2 =>
      G (A.orderEmbOfFin rfl a.1, a.2) (B.orderEmbOfFin h.symm b.1, b.2))
  else 0

/-- Eq.(43), complex-valued until its reality is asserted by the theorem. -/
def minorPolynomial {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (y z : Fin p → ℝ) : ℂ :=
  ∑ A : Finset (Fin p), ∑ B : Finset (Fin p),
    if A.card = B.card then blockDet G A B *
      ((∏ a ∈ A, (z a : ℂ)) * ∏ b ∈ Bᶜ, (y b : ℂ)) else 0

def blockDiagonal {p} (x : Fin p → ℝ) : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ :=
  Matrix.diagonal (fun i => (x i.1 : ℂ))

def positiveOrthant (p : ℕ) : Set ((Fin p → ℝ) × (Fin p → ℝ)) :=
  {u | (∀ i, 0 < u.1 i) ∧ ∀ i, 0 < u.2 i}

end KramersHubbard.PartitionFunction


