-- Prove2me | Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
-- name    : DermanSeqDecisions_LinProg_LinearFractional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:22:06.2702+00:00
-- url     : https://prove2.me/theorems/e87e3842-bdd5-4fc1-a33b-d7cc7c15569c
-- title:
--   The linear-fractional program (11), its ratio g, and the transformed linear program (12)
-- statement:
--   This file sets up the objects of Derman's Lemma on linear-fractional programming.
--
--   Let the variables be indexed by a finite set $\iota$ (in the paper $i = 1, \dots, n$) and the constraints by a set $\kappa$ (in the paper $j = 1, \dots, m$). Fix real data $a_{ji}$, $b_j$, $c_i$, $d_i$.
--
--   1. **The constraints (11).** A vector $x = (x_i)$ satisfies (11) when
--   $$x_i \ge 0 \quad (i \in \iota), \qquad \sum_{i} a_{ji} x_i = b_j \quad (j \in \kappa).$$
--   2. **The ratio.** $g(x) = \dfrac{\sum_i c_i x_i}{\sum_i d_i x_i}$.
--   3. **The constraints (12).** A pair $(z, z_{n+1})$, with $z = (z_i)_{i \in \iota}$ and $z_{n+1}$ a real number, satisfies (12) when
--   $$z_i \ge 0,\ z_{n+1} \ge 0, \qquad \sum_i a_{ji} z_i - b_j z_{n+1} = 0 \quad (j \in \kappa), \qquad \sum_i d_i z_i = 1.$$
--   4. **The linear objective.** $h(z) = \sum_i c_i z_i$.
--
--   Derman's Lemma states that, under two conditions on the data, minimizing $g$ subject to (11) reduces to the linear program of minimizing $h$ subject to (12) (the transformation now known as the Charnes–Cooper transformation).
--
--   **Formalization Note.** The $(n+1)$-st coordinate of a point of (12) is a separate real number `zlast`. The ratio uses Lean's real division, which returns $0$ when the denominator vanishes; the Lemma's hypothesis (ii) makes the denominator positive on (11). The paper's misprint $\sum_{j=1}^n a_{ji} x_i$ in (11) is read with the summation index $i$.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, pp. 22–23, §3, Lemma, (11) and (12)

import Mathlib

namespace DermanSeqDecisions.LinProg

/-! Objects of Derman's Lemma (Derman, *On Sequential Decisions and Markov Chains*, Management
Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, Lemma, pp. 22–23): the constraint system
(11), the ratio `g`, the transformed constraint system (12) and the linear objective `h`.

**Formalization Note.** The paper indexes the variables by `i = 1, ⋯, n` and the constraints by
`j = 1, ⋯, m`; here they range over arbitrary types `ι` (finite) and `κ`, of which `Fin n` and
`Fin m` are the instance. The `(n+1)`-st coordinate `z_{n+1}` of (12) is kept as a separate real
number `zlast`, so a point of (12) is a pair `(z, zlast)` with `z : ι → ℝ`. -/

variable {ι κ : Type*} [Fintype ι]

/-- The constraints (11): `x_i ≥ 0` for every `i`, and `∑_i a_{ji} x_i = b_j` for every `j`.
(The paper prints `∑_{j=1}^n a_{ji} x_i`; the summation index is `i`.) -/
def IsFeasible11 (A : κ → ι → ℝ) (b : κ → ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ j, ∑ i, A j i * x i = b j

/-- The ratio `g(x) = (∑_i c_i x_i) / (∑_i d_i x_i)`. (Lean's real division returns `0` when the
denominator is `0`; the Lemma's hypothesis (ii) makes the denominator positive on (11).) -/
noncomputable def fracObj (c d : ι → ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, c i * x i) / ∑ i, d i * x i

/-- The constraints (12) on `(z_1, ⋯, z_n, z_{n+1}) = (z, zlast)`: all coordinates are
nonnegative, `∑_i a_{ji} z_i − b_j z_{n+1} = 0` for every `j`, and `∑_i d_i z_i = 1`. -/
def IsFeasible12 (A : κ → ι → ℝ) (b : κ → ℝ) (d : ι → ℝ) (z : ι → ℝ) (zlast : ℝ) : Prop :=
  (∀ i, 0 ≤ z i) ∧ 0 ≤ zlast ∧ (∀ j, ∑ i, A j i * z i - b j * zlast = 0) ∧ ∑ i, d i * z i = 1

/-- The linear objective `h(z) = ∑_i c_i z_i` (it does not involve `z_{n+1}`). -/
def linObj (c : ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, c i * z i

end DermanSeqDecisions.LinProg


