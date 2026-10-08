-- Prove2me | Definitions.Def_LenstraIP_Hyperplanes_LatticeData
-- name    : LenstraIP_Hyperplanes_LatticeData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:50:52.681389+00:00
-- url     : https://prove2.me/theorems/bad4acdf-0893-4c3e-a4c4-e1fe633dec0d
-- title:
--   §1 objects: the determinant d(L) = |det(b₁,…,bₙ)|, the hyperplane H, the distance h, and the hyperplanes H + kbₙ meeting B(p, R)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean length $|\cdot|$, and let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$. It generates the **lattice**
--   $$L = \sum_{i=1}^n \mathbb Z b_i = \Big\{ \sum_{i=1}^n m_i b_i : m_i \in \mathbb Z \Big\}.$$
--   This file introduces the objects of §1 of Lenstra's paper that are built from such a basis.
--
--   1. The **determinant** of $L$ is the positive real number
--   $$d(L) = |\det(b_1, b_2, \dots, b_n)|,$$
--   the $b_i$ being written as the columns of an $n\times n$ matrix. It is the volume of the fundamental parallelepiped $\sum_i [0,1)\, b_i$ and does not depend on the choice of basis.
--   2. Singling out the last vector $b_n$, the **hyperplane** $H = \sum_{i=1}^{n-1} \mathbb R b_i$ is the real span of $b_1, \dots, b_{n-1}$; it contains the $(n-1)$-dimensional lattice $L' = \sum_{i=1}^{n-1} \mathbb Z b_i$.
--   3. The number $h$ is the **distance of $b_n$ to $H$**, $h = \inf_{w \in H} |b_n - w|$.
--   4. For $p \in \mathbb R^n$ and $R \in \mathbb R$, the set of integers $k$ such that the parallel hyperplane
--   $$H + k b_n = \{ x \in \mathbb R^n : x - k b_n \in H \}$$
--   meets the closed ball $B(p, R) = \{x \in \mathbb R^n : |x - p| \le R\}$. Since $L = L' + \mathbb Z b_n \subset \bigcup_{k \in \mathbb Z}(H + k b_n)$, these hyperplanes are the only ones on which lattice points of $B(p,R)$ can lie. The paper's $t$ is the number of such $k$.
--
--   These are the objects in which the goal theorem and every milestone of the mission are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so $|\cdot|$ is the Euclidean norm and balls are round. The lattice $L$ is the published `KannanLattice.Core.lattice b` (the $\mathbb Z$-span of the $b_i$); linear independence of $b$ is a hypothesis of each theorem, not part of the definitions. Where $b_n$ is singled out, $n = k+1$, the basis is `b : Fin (k+1) → ℝⁿ`, $b_n$ is `b (Fin.last k)` and $b_1, \dots, b_{n-1}$ are `b ∘ Fin.castSucc`; the integer index of the hyperplanes $H + kb_n$ is called `j` in Lean because `k` is taken by the dimension. The determinant of the column matrix equals that of its transpose, so the orientation convention is immaterial. The paper never writes a formula for $d(L')$; the theorems use the published `KannanLattice.Core.latticeDet` (the product of the Gram–Schmidt lengths, i.e. the $(n-1)$-dimensional volume of the fundamental parallelepiped of $b_1,\dots,b_{n-1}$).
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, pp. 539–541: (5) the lattice L; p. 540 the determinant d(L); p. 540 (proof of the LEMMA) L′, H and h; p. 541 the hyperplanes H + kbₙ meeting B(p, R) and their number t

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace LenstraIP.Hyperplanes

open KannanLattice.Core

/-- The determinant `d(L)` of the lattice `L = Σ ℤ bᵢ` (Lenstra 1983, §1, p. 540): the positive
real number `|det(b₁, b₂, …, bₙ)|`, the `bᵢ` being written as column vectors. Column `j` of the
matrix is `b j`, so its `(i, j)` entry is the `i`-th coordinate of `b j`. -/
noncomputable def latDet {n : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n)) : ℝ :=
  |Matrix.det (Matrix.of fun i j => b j i)|

/-- The `(n − 1)`-dimensional hyperplane `H = Σ_{i=1}^{n−1} ℝ bᵢ` (§1, p. 540), for `n = k + 1`:
the real span of the first `k` basis vectors `b ∘ Fin.castSucc`. -/
noncomputable def hyperplane {k : ℕ} (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (k + 1))) :=
  Submodule.span ℝ (Set.range (b ∘ Fin.castSucc))

/-- `h`, the distance of `bₙ = b (Fin.last k)` to the hyperplane `H` (§1, p. 540). -/
noncomputable def hgt {k : ℕ} (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1))) : ℝ :=
  Metric.infDist (b (Fin.last k)) (hyperplane b)

/-- The set of integers `j` for which the parallel hyperplane `H + j·bₙ = {x : x − j·bₙ ∈ H}`
meets the closed ball `B(p, R) = {x : |x − p| ≤ R}` (§1, p. 541; the paper calls the integer `k`).
The paper's `t` is the number of elements of this set. -/
def hitIndices {k : ℕ} (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (p : EuclideanSpace ℝ (Fin (k + 1))) (R : ℝ) : Set ℤ :=
  {j | ∃ x ∈ Metric.closedBall p R, x - (j : ℝ) • b (Fin.last k) ∈ hyperplane b}

end LenstraIP.Hyperplanes


