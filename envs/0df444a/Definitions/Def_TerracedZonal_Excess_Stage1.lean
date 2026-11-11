-- Prove2me | Definitions.Def_TerracedZonal_Excess_Stage1
-- name    : TerracedZonal_Excess_Stage1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:17.10802+00:00
-- url     : https://prove2.me/theorems/852280db-700f-413c-ba31-27ceaa7a0443
-- title:
--   Stage 1 of TerracedZonal: window minimizer and repair loop
-- statement:
--   Stage 1 chooses the ring populations $m_0,\dots,m_{K-1}$.
--
--   1. **Exact minimization (§2.1 item 3).** A pre-repair vector is any vector in the window minimizing $G_{c_{\mathrm{step}}}$ over the window; the Viterbi recursion (7) computes one exactly.
--   2. **Repair loop (App. C.2).** Let $\mathrm{diff}=(N-2)-\sum_k m_k$ and split $m$ into terraces, the maximal runs of equal populations. While $\mathrm{diff}\ne0$, apply an admissible move of least marginal stretching cost per point $\Delta\Psi/|\Delta S|$, where $\Psi=\sum_k\psi_{\mathrm{stretch}}(m_k,y_k)$ and $\Delta S$ is the change of $\sum_k m_k$:
--      - a *right boundary shift*: the first ring of a terrace (not the first terrace) of length $>1$ takes the population of the previous terrace;
--      - a *left boundary shift*: the last ring of a terrace (not the last) of length $>1$ takes the population of the next terrace;
--      - both admissible when $0<\Delta S\cdot\operatorname{sgn}(\mathrm{diff})\le|\mathrm{diff}|$;
--      - a *whole-terrace move* $M_t\leftarrow M_t+\operatorname{sgn}(\mathrm{diff})$, admissible when the terrace length is $\le|\mathrm{diff}|$ and $M_t+\operatorname{sgn}(\mathrm{diff})\ge1$.
--
--      Only if no such move is admissible, an *endpoint peel* changes the first ring of some terrace of length $\ge2$ by $\operatorname{sgn}(\mathrm{diff})$.
--   3. **Output.** A Stage-1 output for $N\ge3$ is any vector reached from a pre-repair vector by finitely many loop iterations and satisfying $\sum_k m_k=N-2$.
--
--   **Formalization Note** Every tie-break (among minimizers, among least-cost moves, among peels) is allowed, so "Stage-1 output" is a predicate rather than a function. The peel is required to keep the peeled ring's population at least $1$, as the Ensure line of Algorithm 1a requires $m_k\ge1$.
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), §2.1 items 3–4 pp. 7 (PDF 8), App. C.2 pp. 19–21 (PDF 20–22), Algorithm 1a p. 21 (PDF 22)

import Definitions.Def_TerracedZonal_Excess_Rings

namespace TerracedZonal.Excess

open Real

/-- Stage 1 before the repair loop (§2.1 item 3, p. 7, PDF 8; Algorithm 1a lines 3–15, p. 21,
PDF 22): a population vector in the window (4) minimizing
`∑_k ψ_stretch(m_k, y_k) + c_step ∑_{k ≥ 1} ½(y_{k-1}+y_k) 1{m_k ≠ m_{k-1}} = G_{c_step}(m)`
over the whole window. The Viterbi recursion (7) computes such a minimizer exactly; any
exact minimizer is allowed here (the paper does not fix the tie-break). -/
def IsPreRepair (N : ℕ) (m : Pops N) : Prop :=
  InWindow N m ∧ ∀ m' : Pops N, InWindow N m' → Gcost cStep N m ≤ Gcost cStep N m'

/-- Population of ring `j`, read as a natural-number sequence (`0` past the last ring). -/
noncomputable def popAt {N : ℕ} (m : Pops N) (j : ℕ) : ℕ := if h : j < ringCount N then m ⟨j, h⟩ else 0

/-- The residual `diff = (N - 2) - ∑_k m_k`, App. C.2, p. 19 (PDF 20). -/
noncomputable def residual (N : ℕ) (m : Pops N) : ℤ := (N : ℤ) - 2 - ∑ k, (m k : ℤ)

/-- Rings `a, …, b` form a terrace: a maximal run of equal populations, App. C.2. -/
def IsTerrace {N : ℕ} (m : Pops N) (a b : ℕ) : Prop :=
  a ≤ b ∧ b < ringCount N ∧ (∀ j, a ≤ j → j ≤ b → popAt m j = popAt m a) ∧
  (a = 0 ∨ popAt m (a - 1) ≠ popAt m a) ∧ (b + 1 = ringCount N ∨ popAt m (b + 1) ≠ popAt m a)

/-- The seam-free moves of the repair loop, App. C.2, p. 19 (PDF 20). -/
inductive RepairMove
  /-- Right boundary shift: ring `k`, the first ring of terrace `t+1`, joins terrace `t`. -/
  | rightShift (k : ℕ)
  /-- Left boundary shift: ring `k`, the last ring of terrace `t`, joins terrace `t+1`. -/
  | leftShift (k : ℕ)
  /-- Whole-terrace increment/decrement of the terrace occupying rings `a, …, b`. -/
  | wholeTerrace (a b : ℕ)

/-- `M ↦ M + sgn(diff)` on a natural population (exact whenever `M + sgn(diff) ≥ 1`). -/
def bump (s : ℤ) (M : ℕ) : ℕ := ((M : ℤ) + s).toNat

/-- The population vector after a move (the sign used is `sgn(diff)` of the current vector). -/
noncomputable def moveResult (N : ℕ) (m : Pops N) : RepairMove → Pops N
  | .rightShift k => fun i => if i.val = k then popAt m (k - 1) else m i
  | .leftShift k => fun i => if i.val = k then popAt m (k + 1) else m i
  | .wholeTerrace a b => fun i =>
      if a ≤ i.val ∧ i.val ≤ b then bump (Int.sign (residual N m)) (m i) else m i

/-- `ΔS`: the change of the total population `∑_k m_k` caused by passing from `m` to `m'`. -/
noncomputable def massChange {N : ℕ} (m m' : Pops N) : ℤ := ∑ k, (m' k : ℤ) - ∑ k, (m k : ℤ)

/-- Admissibility of a seam-free move, App. C.2, p. 19 (PDF 20).
* Right boundary shift (for `t ≤ T-2`, `L_{t+1} > 1`): ring `k ≥ 1` starts a terrace of length
  `> 1` that is not the first; admissible if `0 < ΔS · sgn(diff) ≤ |diff|`.
* Left boundary shift (for `t ≤ T-2`, `L_t > 1`): ring `k` ends a terrace of length `> 1` that
  is not the last; same admissibility condition.
* Whole-terrace move: a terrace of length `L_t ≤ |diff|` whose population satisfies
  `M_t + sgn(diff) ≥ 1`. -/
def Admissible (N : ℕ) (m : Pops N) : RepairMove → Prop
  | .rightShift k =>
      1 ≤ k ∧ k + 1 < ringCount N ∧ popAt m k ≠ popAt m (k - 1) ∧ popAt m (k + 1) = popAt m k ∧
      0 < massChange m (moveResult N m (.rightShift k)) * Int.sign (residual N m) ∧
      massChange m (moveResult N m (.rightShift k)) * Int.sign (residual N m) ≤ |residual N m|
  | .leftShift k =>
      1 ≤ k ∧ k + 1 < ringCount N ∧ popAt m (k + 1) ≠ popAt m k ∧ popAt m (k - 1) = popAt m k ∧
      0 < massChange m (moveResult N m (.leftShift k)) * Int.sign (residual N m) ∧
      massChange m (moveResult N m (.leftShift k)) * Int.sign (residual N m) ≤ |residual N m|
  | .wholeTerrace a b =>
      IsTerrace m a b ∧ ((b - a + 1 : ℕ) : ℤ) ≤ |residual N m| ∧
      1 ≤ (popAt m a : ℤ) + Int.sign (residual N m)

/-- Marginal stretching cost per point `ΔΨ / |ΔS|` of a move. -/
noncomputable def moveRatio (N : ℕ) (m : Pops N) (mv : RepairMove) : ℝ :=
  (stretchCost N (moveResult N m mv) - stretchCost N m) /
    |((massChange m (moveResult N m mv) : ℤ) : ℝ)|

/-- One iteration of the repair loop, App. C.2, pp. 19–21 (PDF 20–22), Algorithm 1a lines
17–18: while `diff ≠ 0`, apply an admissible seam-free move of minimum `ΔΨ/|ΔS|` (any minimizer);
only if none is admissible, an endpoint peel changes the first ring `a` of some terrace of
length at least 2 by `sgn(diff)`. The peel is required to keep the ring population `≥ 1`
(the Ensure line of Algorithm 1a). -/
def RepairStep (N : ℕ) (m m' : Pops N) : Prop :=
  residual N m ≠ 0 ∧
  ((∃ mv, Admissible N m mv ∧ (∀ mv', Admissible N m mv' → moveRatio N m mv ≤ moveRatio N m mv') ∧
      m' = moveResult N m mv) ∨
   ((∀ mv, ¬ Admissible N m mv) ∧
      ∃ a b, IsTerrace m a b ∧ a < b ∧ 1 ≤ (popAt m a : ℤ) + Int.sign (residual N m) ∧
        m' = fun i => if i.val = a then bump (Int.sign (residual N m)) (m i) else m i))

/-- `m` is a possible output of Stage 1 of TerracedZonal for `N ≥ 3` points
(Algorithm 1a, p. 21, PDF 22): a window minimizer of `G_{c_step}` followed by finitely many
repair iterations, ending with `∑_k m_k = N - 2`. Every tie-break of the minimization and of
the repair loop is allowed. -/
def IsStage1Output (N : ℕ) (m : Pops N) : Prop :=
  3 ≤ N ∧ ∃ m₀ : Pops N, IsPreRepair N m₀ ∧ Relation.ReflTransGen (RepairStep N) m₀ m ∧
    ∑ k, m k + 2 = N

end TerracedZonal.Excess


