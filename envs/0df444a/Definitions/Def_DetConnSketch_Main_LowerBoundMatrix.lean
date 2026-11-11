-- Prove2me | Definitions.Def_DetConnSketch_Main_LowerBoundMatrix
-- name    : DetConnSketch_Main_LowerBoundMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:19.659261+00:00
-- url     : https://prove2.me/theorems/a186f3bf-eff8-4951-ad15-46a128257bb7
-- title:
--   The lower-bound matrix $M=\frac1{|B|}\sum_{b\in B}X_bQ^{\otimes m}X_b$ (Eq. (4)), the cycle space $C=B^\perp$ and the eigenvalue polynomials $\lambda_\ell$ (Eq. (7))
-- statement:
--   Coordinates of $\mathbb F_2^m$ ($m = k^2$) are the edges of $K_{k,k}$. For $p \in \mathbb R$ let
--   $$Q = \begin{pmatrix} 1 & 2p \\ 0 & 1 \end{pmatrix}, \qquad (Q^{\otimes m})_{xy} = \prod_{e} Q_{x_e, y_e} \quad (x, y \in \mathbb F_2^m),$$
--   rows and columns of $Q$ indexed by $0, 1$. For $b \in \mathbb F_2^m$, $X_b$ is the $2^m\times 2^m$ permutation matrix sending the coordinate vector at $x$ to the one at $x + b$. The **lower-bound matrix** is
--   $$M = \frac{1}{|B|}\sum_{b \in B} X_b\, Q^{\otimes m} X_b \in \mathbb R^{2^m \times 2^m}, \tag{4}$$
--   with $B$ the binary cut space of $K_{k,k}$.
--
--   For $u, x \in \mathbb F_2^m$ write $u\cdot x = \sum_e u_e x_e \in \mathbb F_2$, and let $C = B^\perp = \{c : c \cdot b = 0 \text{ for all } b \in B\}$ (the binary cycle space). For $a \in \mathbb F_2^m$, $|a|$ is its Hamming weight. For $\ell \in \mathbb F_2^m$ the **eigenvalue polynomial** is
--   $$\lambda_\ell(z) = \sum_{a \in C} (-1)^{|a|/2 + \ell\cdot a}\, z^{|a|}, \tag{7}$$
--   and $S_\ell \in \{-1,1\}^{k\times k}$ is the sign matrix with $(S_\ell)_{ij} = (-1)^{\ell_{ij}}$.
--
--   **Formalization Note.** `qMat`, `qTensor`, `shiftMat`, `lowerBoundMatrix k p`, `dot`, `cycleSpace`, `hammingWeight`, `eigLambda ℓ z`, `signMatOfLabel ℓ`; `cutSpaceFinset` and `cycleSpaceFinset` are $B$ and $C$ as finite sets. $|a|/2$ is natural-number division (every $a \in C$ has even weight); $(-1)^{\ell\cdot a}$ uses the value $0$ or $1$ of $\ell \cdot a$.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 51–54 (PDF 55–58), §8.2.3–8.2.5, Eqs. (4), (7)

import Mathlib
import Definitions.Def_DetConnSketch_Main_TwoLift

namespace DetConnSketch.Main

/-!
# The lower-bound matrix `M` (Eq. (4)) and its eigenvalue polynomials `λ_ℓ` (Eq. (7))

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 51–54 (§8.2.3–8.2.6).

Coordinates of `F_2^m` (`m = k²`) are the edges `u_i v_j` of `K_{k,k}` (`EdgeLabel k`).
* `qMat p = Q = [[1, 2p], [0, 1]]`, rows and columns indexed by `0, 1 ∈ F_2`.
* `qTensor p = Q^{⊗m}`: `(Q^{⊗m})_{xy} = ∏_{e} Q_{x_e, y_e}`.
* `shiftMat b = X_b`: the permutation matrix sending the coordinate vector at `x` to the one at
  `x + b`, i.e. `(X_b)_{x' x} = 1` iff `x' = x + b`.
* `lowerBoundMatrix k p = M = (1/|B|) ∑_{b ∈ B} X_b Q^{⊗m} X_b` (Eq. (4)).
* `dot u x = u · x = ∑_e u_e x_e ∈ F_2`; `cycleSpace k = C = B^⊥`; `hammingWeight a = |a|`.
* `eigLambda ℓ z = λ_ℓ(z) = ∑_{a ∈ C} (−1)^{|a|/2 + ℓ·a} z^{|a|}` (Eq. (7)); `|a|` is even on
  `C`, and `|a|/2` is natural-number division.
* `signMatOfLabel ℓ = S_ℓ`, the real sign matrix with `(S_ℓ)_{ij} = (−1)^{ℓ_ij}`.
-/

open Classical in
/-- The cut space `B` as a finite set. -/
noncomputable def cutSpaceFinset (k : ℕ) : Finset (EdgeLabel k) :=
  Finset.univ.filter fun b => b ∈ cutSpace k

/-- `Q = [[1, 2p], [0, 1]]`, indexed by `F_2`: `Q₀₀ = Q₁₁ = 1`, `Q₀₁ = 2p`, `Q₁₀ = 0`. -/
def qMat (p : ℝ) : Matrix (ZMod 2) (ZMod 2) ℝ :=
  fun a b => if a = b then 1 else if a = 0 then 2 * p else 0

/-- The tensor power `Q^{⊗m}`, indexed by `F_2^m`: `(Q^{⊗m})_{xy} = ∏_{i,j} Q_{x_ij, y_ij}`. -/
noncomputable def qTensor {k : ℕ} (p : ℝ) : Matrix (EdgeLabel k) (EdgeLabel k) ℝ :=
  fun x y => ∏ i, ∏ j, qMat p (x i j) (y i j)

open Classical in
/-- The permutation matrix `X_b` of `x ↦ x + b`: entry `(x', x)` is `1` iff `x' = x + b`. -/
noncomputable def shiftMat {k : ℕ} (b : EdgeLabel k) : Matrix (EdgeLabel k) (EdgeLabel k) ℝ :=
  fun x' x => if x' = x + b then 1 else 0

/-- `M = (1/|B|) ∑_{b ∈ B} X_b Q^{⊗m} X_b` (Eq. (4)). -/
noncomputable def lowerBoundMatrix (k : ℕ) (p : ℝ) : Matrix (EdgeLabel k) (EdgeLabel k) ℝ :=
  ((cutSpaceFinset k).card : ℝ)⁻¹ • ∑ b ∈ cutSpaceFinset k, shiftMat b * qTensor p * shiftMat b

/-- The binary dot product `u · x = ∑_{i,j} u_ij x_ij ∈ F_2`. -/
def dot {k : ℕ} (u x : EdgeLabel k) : ZMod 2 :=
  ∑ i, ∑ j, u i j * x i j

/-- The binary cycle space `C = B^⊥ = {c : c · b = 0 for every b ∈ B}`. -/
def cycleSpace (k : ℕ) : Set (EdgeLabel k) :=
  {c | ∀ b ∈ cutSpace k, dot c b = 0}

open Classical in
/-- `C` as a finite set. -/
noncomputable def cycleSpaceFinset (k : ℕ) : Finset (EdgeLabel k) :=
  Finset.univ.filter fun c => c ∈ cycleSpace k

open Classical in
/-- The Hamming weight `|a|`: the number of coordinates equal to `1`. -/
noncomputable def hammingWeight {k : ℕ} (a : EdgeLabel k) : ℕ :=
  (Finset.univ.filter fun p : Fin k × Fin k => a p.1 p.2 ≠ 0).card

/-- `λ_ℓ(z) = ∑_{a ∈ C} (−1)^{|a|/2 + ℓ·a} z^{|a|}` (Eq. (7)). -/
noncomputable def eigLambda {k : ℕ} (ℓ : EdgeLabel k) (z : ℝ) : ℝ :=
  ∑ a ∈ cycleSpaceFinset k, (-1 : ℝ) ^ (hammingWeight a / 2 + (dot ℓ a).val) * z ^ hammingWeight a

/-- `S_ℓ ∈ {−1, 1}^{k×k}` with `(S_ℓ)_{ij} = (−1)^{ℓ_ij}`. -/
noncomputable def signMatOfLabel {k : ℕ} (ℓ : EdgeLabel k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (-1 : ℝ) ^ (ℓ i j).val

end DetConnSketch.Main


