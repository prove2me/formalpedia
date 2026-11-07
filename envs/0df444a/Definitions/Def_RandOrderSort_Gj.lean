-- Prove2me | Definitions.Def_RandOrderSort_Gj
-- name    : RandOrderSort_Gj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:25.814645+00:00
-- url     : https://prove2.me/theorems/0dbb7bf5-be11-4bed-a95c-27d16ff54d00
-- title:
--   The growing-phase witness majorants, display (40)
-- statement:
--   For a scale $s=2^h$, let $E^{\mathrm{arr}}_{j,s}$ be the event that a child $I$ of the selected $2s$-leaf parent in the tree of growing phase $j$ has $|(P_{j+1}\setminus P_j)\cap I|>2Ts$. Let $E^{\mathrm{re}}_{j,s}$ be the event that a child $I$ of the selected $2s$-leaf parent in the next tree has $2|P_j\cap I|+4T>2Ts$ when $j<J$, or $>Bs$ when $j=J$. An event whose parent does not exist is empty. With $D_g=2048+4096(1+2+4+8+16+32)=260096$,
--   $$A^{\mathrm{arr}}_j=D_g+4096\sum_{s\in\{64,128,\dots\}}s\mathbf 1[E^{\mathrm{arr}}_{j,s}],\qquad R_j=D_g+4096\sum_{s\in\{64,128,\dots\}}s\mathbf 1[E^{\mathrm{re}}_{j,s}],\qquad G_j=A^{\mathrm{arr}}_j+R_j.$$
--   The module also defines the constants $A_g=2+1027^2$ and $M_g=e^{D_g/16384}\bigl(1+A_ge^{-32}/(1-e^{-1/2})\bigr)$.
--
--   These variables depend only on $(P_j,P_{j+1})$, which is what permits the reverse-exposure argument of Lemma 4.10.
--
--   **Formalization Note** The sums over scales run over $6\le h<n$, which contains every scale with a nonempty event, since the trees have at most $n$ leaves.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §4.3.3, pp.30–31, display (40); Lemma 4.8, p.27 (A_g); Lemma 4.10, p.31, display (41)

import Mathlib
import Definitions.Def_RandOrderSort_Dop

namespace RandOrderSort

/-! # The growing-phase witness majorants (§4.3.3, pp.30–31, display (40))

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), p.30: "For each scale s ∈ {1, 2, 4, . . .}, let
E^arr_{j,s} be the event that a child I of the selected 2s-leaf parent in the current tree satisfies
|(P_{j+1} \ P_j) ∩ I| > 2Ts. … Let E^re_{j,s} be the event that a child I of the selected 2s-leaf
parent in the next tree satisfies 2|P_j ∩ I| + 4T > 2Ts (j < J), 2|P_j ∩ I| + 4T > Bs (j = J).
The next tree is a growing tree for j < J and the first shrinking tree for j = J." p.31: "If the
selected parent does not exist in the relevant tree, we take the corresponding event to be empty.
… Set D_g = 2048 + 4096(1 + 2 + 4 + 8 + 16 + 32) = 260096,
A^arr_j = D_g + 4096 ∑_{s∈{64,128,256,...}} s 1[E^arr_{j,s}],
R_j = D_g + 4096 ∑_{s∈{64,128,256,...}} s 1[E^re_{j,s}], G_j = A^arr_j + R_j. (40)"
Lemma 4.10, p.31: "θ_g = 1/32768, M_g = e^{D_g/16384}(1 + A_g e^{−32}/(1 − e^{−1/2})). (41)"
Lemma 4.8, p.27: "A_g = 2 + 1027²".

**Formalization Note.**
* The quantities are defined for a key order `lt` on the arrivals and a cut `β` on keys; in the
  run, `P_j` is the set of the first `t_j` arrivals (`Finset.range (tj j)`). The current tree of
  growing phase `j` is `phaseTree n lt j` (`2^j` leaves from `P_j`); the next tree is
  `phaseTree n lt (j + 1)` (from `P_{j+1}`, with `2^{j+1}` leaves if `j < J`, and the first
  shrinking tree, `b_1` leaves, if `j = J`).
* A scale `s = 2^h`; the selected `2s`-leaf parent is the node of height `h + 1` containing the
  cut; an event at a scale whose parent does not exist (`2^{h+1}` exceeds the leaf count) is
  empty. The sums over `s ∈ {64, 128, …}` run over `6 ≤ h < n`, which contains every scale with a
  nonempty event (the trees have at most `n` leaves).
-/

/-- `E^arr_{j,s}` at `s = 2^h`: a child of the selected `2s`-leaf parent of the phase-`j` tree
receives more than `2Ts` of the phase-`j` arrivals `P_{j+1} \ P_j` (arrivals `t_j, …, 2t_j − 1`). -/
def Earr (n : ℕ) (lt : ℕ → ℕ → Bool) (β : ℕ → Bool) (j h : ℕ) : Prop :=
  2 ^ (h + 1) ≤ (phaseTree n lt j).leaves ∧ ∃ e < 2,
    2 * T * 2 ^ h < countIn lt (phaseTree n lt j) (Finset.Ico (tj j) (2 * tj j)) h
      (2 * (cutLeaf β (phaseTree n lt j) / 2 ^ (h + 1)) + e)

/-- `E^re_{j,s}` at `s = 2^h`: a child `I` of the selected `2s`-leaf parent of the next tree has
`2|P_j ∩ I| + 4T > 2Ts` (`j < J`) or `> Bs` (`j = J`). -/
def Ere (n : ℕ) (lt : ℕ → ℕ → Bool) (β : ℕ → Bool) (j h : ℕ) : Prop :=
  2 ^ (h + 1) ≤ (phaseTree n lt (j + 1)).leaves ∧ ∃ e < 2,
    (if j < J n then 2 * T * 2 ^ h else B n * 2 ^ h) <
      2 * countIn lt (phaseTree n lt (j + 1)) (Finset.range (tj j)) h
        (2 * (cutLeaf β (phaseTree n lt (j + 1)) / 2 ^ (h + 1)) + e) + 4 * T

/-- `D_g = 2048 + 4096(1 + 2 + 4 + 8 + 16 + 32) = 260096` (40). -/
noncomputable def Dg : ℝ := 2048 + 4096 * (1 + 2 + 4 + 8 + 16 + 32)

/-- `A^arr_j = D_g + 4096 ∑_{s ∈ {64,128,…}} s 1[E^arr_{j,s}]` (40). -/
noncomputable def Aarr (n : ℕ) (lt : ℕ → ℕ → Bool) (β : ℕ → Bool) (j : ℕ) : ℝ :=
  by classical exact
    Dg + 4096 * ∑ h ∈ Finset.Ico 6 n, (2 : ℝ) ^ h * (if Earr n lt β j h then 1 else 0)

/-- `R_j = D_g + 4096 ∑_{s ∈ {64,128,…}} s 1[E^re_{j,s}]` (40). -/
noncomputable def Rj (n : ℕ) (lt : ℕ → ℕ → Bool) (β : ℕ → Bool) (j : ℕ) : ℝ :=
  by classical exact
    Dg + 4096 * ∑ h ∈ Finset.Ico 6 n, (2 : ℝ) ^ h * (if Ere n lt β j h then 1 else 0)

/-- `G_j = A^arr_j + R_j` (40). -/
noncomputable def Gj (n : ℕ) (lt : ℕ → ℕ → Bool) (β : ℕ → Bool) (j : ℕ) : ℝ :=
  Aarr n lt β j + Rj n lt β j

/-- The growing sum `∑_{j=0}^{L−1} G_j`. -/
noncomputable def GSum (n : ℕ) (lt : ℕ → ℕ → Bool) (β : ℕ → Bool) : ℝ :=
  ∑ j ∈ Finset.range (L n), Gj n lt β j

/-- `A_g = 2 + 1027²` (35). -/
noncomputable def Ag : ℝ := 2 + 1027 ^ 2

/-- `M_g = e^{D_g/16384}(1 + A_g e^{−32}/(1 − e^{−1/2}))` (41). -/
noncomputable def Mg : ℝ :=
  Real.exp (Dg / 16384) * (1 + Ag * Real.exp (-32) / (1 - Real.exp (-(1 / 2))))

end RandOrderSort


