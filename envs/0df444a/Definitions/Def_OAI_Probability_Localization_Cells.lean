-- Prove2me | Definitions.Def_OAI_Probability_Localization_Cells
-- name    : OAI_Probability_Localization_Cells
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:34:29.283845+00:00
-- url     : https://prove2.me/theorems/4f93cb58-6bf3-42fd-bf6c-a014725ff2df
-- title:
--   Coordinates of dyadic cells: width, lower corner, center, cell of a point, children and ancestors
-- statement:
--   Fix a dimension $n$ and the cube $C_n=\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n\subseteq\mathbb{R}^n$ of side $1/\sqrt n$. A dyadic cell is a pair $Q=(J,k)$ of a level $J\in\mathbb{N}$ and an index vector $k=(k_1,\dots,k_n)\in\{0,1,\dots,2^J-1\}^n$. It describes the half-open box $B_Q=\prod_{i}\big[\lambda_i(Q),\lambda_i(Q)+w_n(J)\big)$, one of the $2^{nJ}$ congruent subcubes into which the $J$-th dyadic subdivision cuts $C_n$. The file defines the following elementary quantities.
--
--   1. **Width.** The side length of a cell of level $J$,
--      $$w_n(J)=\frac{1}{\sqrt n\,2^J}.$$
--
--   2. **Lower corner.** For a cell $Q=(J,k)$ and a coordinate $i$, the left endpoint of the $i$-th side of $B_Q$,
--      $$\lambda_i(Q)=-\frac{1}{2\sqrt n}+\frac{k_i}{\sqrt n\,2^J}.$$
--
--   3. **Center.** The point $c(Q)\in\mathbb{R}^n$ with coordinates $c(Q)_i=\lambda_i(Q)+\tfrac12\,w_n(J)$.
--
--   4. **Index of a point.** For a level $J$ and a point $z\in\mathbb{R}^n$, the index vector $\kappa_J(z)$ with
--      $$\kappa_J(z)_i=\Big\lfloor\Big(z_i+\frac{1}{2\sqrt n}\Big)\sqrt n\,2^J\Big\rfloor_{+}\bmod 2^J ,$$
--      where $\lfloor x\rfloor_+$ is the integer part of $x$ for $x\ge0$ and $0$ for $x<0$.
--
--   5. **Cell of a point.** $\mathrm{cellAt}_J(z)=(J,\kappa_J(z))$. For $z\in C_n$ (and $n\ge1$) this is the level-$J$ cell whose box contains $z$.
--
--   6. **Child cell.** For a cell $Q=(J,k)$, a relative depth $l\in\mathbb{N}$ and an offset $a\in\{0,\dots,2^l-1\}^n$, the cell
--      $$\mathrm{child}(Q,l,a)=\big(J+l,\ (k_i\,2^l+a_i)_{i}\big),$$
--      which is the subcell of $Q$ at level $J+l$ in relative position $a$. Its indices satisfy $k_i2^l+a_i<2^{J+l}$.
--
--   7. **Ancestor cell.** For $Q=(J,k)$ and a level $J'\le J$, the cell
--      $$\mathrm{anc}(Q,J')=\big(J',\ (\lfloor k_i/2^{J-J'}\rfloor)_{i}\big),$$
--      the level-$J'$ cell of the dyadic tree above $Q$; for $n\ge1$ its box contains $B_Q$.
--
--   These coordinates make the dyadic tree of $C_n$ explicit. They are used to compute volumes of cells, to show that a point of $C_n$ lies in exactly one cell of each level, that two cells whose boxes share a point are nested, and that $Q$ is recovered as the child of $\mathrm{anc}(Q,J')$ at relative depth $J-J'$ with offset $(k_i\bmod 2^{J-J'})_i$.
--
--   **Formalization Note** Cells are elements of `Cell n`, a dependent pair of a level `J` and an index map `Fin n -> Fin (2^J)`, and boxes are `cellSet Q`, both from the base definitions. The Lean names are `cellWidth`, `cellLower`, `cellCenter`, `cellIndex`, `cellAt`, `childCell` and `ancestorCell`; the last one takes the proof of $J'\le J$ as an argument. The floor is the natural-number floor `Nat.floor`, and the reduction modulo $2^J$ only affects points outside $C_n$; it guarantees that the index is always valid. For $n=0$ Lean's conventions $\sqrt0=0$ and $x/0=0$ make the formulas degenerate, so the geometric facts are proved under the hypothesis $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Cells.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Cells.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianFiniteEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

noncomputable def cellWidth (n J : ℕ) : ℝ := 1 / (Real.sqrt n * (2 : ℝ)^J)
noncomputable def cellLower {n : ℕ} (Q : Cell n) (i : Fin n) : ℝ :=
  -1 / (2 * Real.sqrt n) + (Q.2 i : ℝ) / (Real.sqrt n * (2 : ℝ)^Q.1)
noncomputable def cellCenter {n : ℕ} (Q : Cell n) : Coordinate n :=
  fun i => cellLower Q i + cellWidth n Q.1 / 2

noncomputable def cellIndex {n : ℕ} (J : ℕ) (z : Coordinate n) : Fin n → Fin (2^J) :=
  fun i => ⟨⌊(z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^J)⌋₊ % 2^J,
    Nat.mod_lt _ (pow_pos (by norm_num) J)⟩

noncomputable def cellAt {n : ℕ} (J : ℕ) (z : Coordinate n) : Cell n := ⟨J, cellIndex J z⟩

noncomputable def childCell {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) : Cell n :=
  ⟨Q.1 + l, fun i => ⟨(Q.2 i).val * 2^l + (a i).val, by
    rw [pow_add]
    have h1 := (Q.2 i).isLt
    have h2 := (a i).isLt
    nlinarith⟩⟩

noncomputable def ancestorCell {n : ℕ} (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) : Cell n :=
  ⟨J,fun i => ⟨(Q.2 i).val / 2^(Q.1-J),by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(Q.1-J))).mpr
    rw [← pow_add,Nat.add_sub_of_le hJ]
    exact (Q.2 i).isLt⟩⟩

end RepeatedLocalization

end OAI


