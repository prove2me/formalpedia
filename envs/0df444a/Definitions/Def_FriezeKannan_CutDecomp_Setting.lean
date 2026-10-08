-- Prove2me | Definitions.Def_FriezeKannan_CutDecomp_Setting
-- name    : FriezeKannan_CutDecomp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:04:54.552984+00:00
-- url     : https://prove2.me/theorems/49c7645e-2c1b-4ec6-9c6d-7fec2e210782
-- title:
--   §2.1, pp. 177–178 — M(S, T), the Frobenius and cut norms, cut matrices CUT(S, T, d) and cut sums
-- statement:
--   Let $R$ and $C$ be finite index sets, and let $M$ be a real matrix with rows indexed by $R$ and columns indexed by $C$ (an $R\times C$ matrix). This file fixes the objects of Frieze and Kannan's matrix decompositions.
--
--   1. **Block sums.** For $S\subseteq R$ and $T\subseteq C$,
--   $$M(S,T)=\sum_{(i,j)\in S\times T} M(i,j).$$
--   It is $0$ when $S$ or $T$ is empty.
--   2. **Frobenius norm.** $\|M\|_F=\sqrt{\sum_{(i,j)\in R\times C} M(i,j)^2}$.
--   3. **Cut norm.** $\|M\|_C=\max_{S\subseteq R,\,T\subseteq C}|M(S,T)|$, a maximum over the finitely many pairs of subsets (the pair $(\emptyset,\emptyset)$ is always available, so the maximum exists and is $\ge 0$).
--   4. **Cut matrices.** For $S\subseteq R$, $T\subseteq C$ and a real $d$, the cut matrix $\mathrm{CUT}(S,T,d)$ is the $R\times C$ matrix with entry $d$ at every $(i,j)\in S\times T$ and $0$ elsewhere.
--   5. **Cut sums.** Given $s$ triples $(R_t,C_t,d_t)$, $t=1,\dots,s$, the sum $D^{(1)}+\dots+D^{(s)}$ of the cut matrices $D^{(t)}=\mathrm{CUT}(R_t,C_t,d_t)$; it is the zero matrix when $s=0$. A **cut decomposition** of width $s$ writes $A=D^{(1)}+\dots+D^{(s)}+W$, with error matrix $W$.
--   6. **Vector norms** (used in inequality (1)). For $y\in\mathbb R^R$, $\|y\|_1=\sum_i|y_i|$; for $x\in\mathbb R^C$ with $C$ nonempty, $\|x\|_\infty=\max_j|x_j|$.
--
--   These are the objects every statement of this mission is written in. The cut norm measures how far a matrix is from being "uniform on every rectangle", and cut decompositions approximate a matrix in this norm by a few rank-one blocks.
--
--   **Formalization Note** Subsets are `Finset`s. $M(S,T)$ is `blockSum`, $\|M\|_F$ is `frobNorm` (the real square root of the sum of squares; Mathlib's scoped matrix norms are deliberately not used), $\mathrm{CUT}(S,T,d)$ is `cutMatrix`, and a family of $s$ cut matrices is given by three functions on `Fin s`, summed by `cutSum`. The cut norm and $\|\cdot\|_\infty$ are genuine maxima (`Finset.sup'` over a nonempty finite set), not suprema with junk values.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), pp. 177–178, §2.1 Notation (norms, M(S,T), Cut Matrix), and p. 178, §2.3, (2) (Cut Decomposition)

import Mathlib

namespace FriezeKannan.CutDecomp

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- `M(S, T) = ∑_{(i,j) ∈ S × T} M(i, j)` (§2.1, p. 178). -/
def blockSum (M : Matrix R C ℝ) (S : Finset R) (T : Finset C) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, M i j

/-- The Frobenius norm `‖M‖_F = √(∑_{(i,j) ∈ R × C} M(i, j)²)` (§2.1, p. 177). -/
noncomputable def frobNorm (M : Matrix R C ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The cut matrix `CUT(S, T, d)`: entry `d` on `S × T` and `0` elsewhere (§2.1, p. 178). -/
def cutMatrix (S : Finset R) (T : Finset C) (d : ℝ) : Matrix R C ℝ :=
  fun i j => if i ∈ S ∧ j ∈ T then d else 0

/-- The sum `D^(1) + ⋯ + D^(s)` of the cut matrices `D^(t) = CUT(R_t, C_t, d_t)`, `t = 1, …, s`
(the cut part of a cut decomposition (2), §2.3, p. 178); it is `0` when `s = 0`. -/
def cutSum {s : ℕ} (Rs : Fin s → Finset R) (Cs : Fin s → Finset C) (d : Fin s → ℝ) :
    Matrix R C ℝ :=
  ∑ t, cutMatrix (Rs t) (Cs t) (d t)

/-- The cut norm `‖M‖_C = max_{S ⊆ R, T ⊆ C} |M(S, T)|` (§2.1, p. 177), a maximum over the
finite nonempty set of all pairs of subsets. -/
def cutNorm (M : Matrix R C ℝ) : ℝ :=
  (Finset.univ : Finset (Finset R × Finset C)).sup' Finset.univ_nonempty
    (fun p => |blockSum M p.1 p.2|)

/-- The `ℓ₁` norm `‖y‖₁ = ∑_i |y_i|` of a vector indexed by `R`. -/
def l1Norm (y : R → ℝ) : ℝ :=
  ∑ i, |y i|

/-- The sup norm `‖x‖_∞ = max_j |x_j|` of a vector indexed by a nonempty `C`. -/
def supNorm [Nonempty C] (x : C → ℝ) : ℝ :=
  (Finset.univ : Finset C).sup' Finset.univ_nonempty (fun j => |x j|)

end FriezeKannan.CutDecomp


