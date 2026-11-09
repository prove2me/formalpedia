-- Prove2me | Definitions.Def_ModLatSVP_SearchCond
-- name    : ModLatSVP_SearchCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:42.832281+00:00
-- url     : https://prove2.me/theorems/40ba6ad6-6fb5-4daf-8ece-adabbbe07a18
-- title:
--   Prefix bounds $R_j$, search conditions, and the rescaled Gram matrix $G_a$
-- statement:
--   Let $M$ have a module flag with blocks $L_1,\dots,L_r$ over a field of degree $d$. The **prefix bounds** are
--
--   $$R_j=\sqrt{jd}\,\Big(\prod_{i=1}^{j}G_i\Big)^{1/j}\qquad(1\le j\le r),$$
--
--   so that, by Minkowski's theorem, the prefix $M_j$ has minimum at most $R_j$.
--
--   A flag (of a prefix module $M_t$, or of $M$ itself when $t=r$) satisfies the **search conditions at radius $R>0$** if
--
--   1. its projected suffix is reduced, i.e. it is reduced at every index $2\le i\le t$;
--   2. $R\le H_1\le 2R$;
--   3. $R_j\ge R/2$ for every $1\le j\le t$;
--   4. the module contains a nonzero vector of length at most $R$.
--
--   **Scaling lengths in the first block** by $0<a\le1$ replaces the Gram matrix by
--
--   $$G_a=\begin{pmatrix}a^2F & a^2E\\ a^2E^{T} & Q+a^2E^{T}F^{-1}E\end{pmatrix},\qquad G=\begin{pmatrix}F&E\\E^{T}&F'\end{pmatrix},\ Q=F'-E^{T}F^{-1}E ,$$
--
--   where $F$ is the Gram matrix of the first block; the projection onto $V_1^\perp$ is unchanged, and the first block is shrunk by $a$.
--
--   The search conditions are the hypothesis under which the enumeration cost of a flag is controlled (Lemma 2.3); the rescaling is how Lemma 2.4 reaches them.
--
--   **Formalization Note** $G_a$ is written $a^2G+(1-a^2)P$, where $P$ is the Gram matrix of $\pi_{V_1^\perp}$ (zero on the first block, $Q$ on the rest), obtained by polarizing $x\mapsto\|\pi_{V_1^\perp}x\|^2$; expanding gives the displayed matrix.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.4, (8), p.15 (PDF p.15); search conditions, p.15; p.16; App. B.3, (44), p.49

import Mathlib
import Definitions.Def_ModLatSVP_IsModuleFlag

open Matrix

namespace ModLatSVP

/-- The prefix bound `R_j = √(jd) (∏_{i=1}^{j} G_i)^{1/j}` of (8). Kim, Lee, Son, *Exact SVP and CVP in
Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…), §2.4, (8), p.15 (PDF p.15). -/
noncomputable def prefixBound {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (j : ℕ) : ℝ :=
  Real.sqrt ((j : ℝ) * d) * (∏ i ∈ Finset.Icc 1 j, normDet G i) ^ ((1 : ℝ) / j)

/-- The search conditions of §2.4, p.15, for the flag `V_1 ⊂ ⋯ ⊂ V_t` of the prefix module `M_t` (all of
`M` when `t = r`): "A flag of rank r ≥ 2 satisfies the search conditions at radius R > 0 if its projected
suffix is reduced, R ≤ H₁ ≤ 2R, every prefix bound R_j satisfies R_j ≥ R/2, and the module contains a
nonzero vector of length at most R."

**Formalization Note.** "The projected suffix is reduced" is reducedness at every index `2 ≤ i ≤ t`:
the projected suffix `π_{V_1^⊥} M_t` has blocks `L_2, …, L_t`, and its `(i−1)`-th projected module is
`π_{V_{i−1}^⊥} M_t` because `V_1 ⊆ V_{i−1}`. The parameter `t` lets the conditions be stated for a prefix
`M_t` of the flag, as Lemma 2.4 does. -/
def SearchCond {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (t : ℕ) (R : ℝ) : Prop :=
  0 < R ∧
  (∀ i : ℕ, 2 ≤ i → i ≤ t → ReducedAt G t i) ∧
  R ≤ blockMin G 1 ∧ blockMin G 1 ≤ 2 * R ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ t → R / 2 ≤ prefixBound G j) ∧
  ∃ x : Fin r × Fin d → ℤ, InPrefixZ t x ∧ x ≠ 0 ∧ Real.sqrt (qf G (intVec x)) ≤ R

/-- The Gram matrix of `π_{V_i^⊥}`, the polarization of `x ↦ ‖π_{V_i^⊥} x‖²`: in the adapted basis it is
the block matrix with the Schur complement `Q` of (43) on the coordinates of the blocks after `i` and
zero elsewhere. -/
noncomputable def projGram {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (i : ℕ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  fun p q => (projSq G i (Pi.single p 1 + Pi.single q 1) - projSq G i (Pi.single p 1) -
    projSq G i (Pi.single q 1)) / 2

/-- The Gram matrix `G_a` of (44), App. B.3, p.49 (PDF p.49): "Scaling lengths in the first block by a
factor 0 < a ≤ 1 changes the Gram matrix to G_a = [[a²F, a²E], [a²Eᵀ, Q + a²EᵀF⁻¹E]]" (§2.4, p.16).

**Formalization Note.** `G_a = a² G + (1 − a²) P`, with `P = projGram G 1` the Gram matrix of
`π_{V_1^⊥}`. Writing `G = [[F, E], [Eᵀ, F']]` and `P = [[0, 0], [0, Q]]` with `Q = F' − EᵀF⁻¹E`, this is
`[[a²F, a²E], [a²Eᵀ, a²F' + (1 − a²)Q]]`, and `a²F' + (1 − a²)Q = Q + a²EᵀF⁻¹E`, which is (44). -/
noncomputable def scaledGram {r d : ℕ} (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (a : ℝ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  a ^ 2 • G + (1 - a ^ 2) • projGram G 1

end ModLatSVP


