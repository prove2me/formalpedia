-- Prove2me | Definitions.Def_SublinearSteiner_ReusableSample
-- name    : SublinearSteiner_ReusableSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:29.695121+00:00
-- url     : https://prove2.me/theorems/28e65616-1098-46f2-a55e-6de6bea8eb64
-- title:
--   The reusable-sample selection rule (4.17)
-- statement:
--   The procedure of Lemma 4.10. Given rows $R_1,\dots,R_{N_r}$ of a universe and $N_s$ sample records: keep the records as live records and process the rows in order. If row $R_j$ contains $c$ live records, accept it with probability
--   $$p(c)=\frac1{1+\exp((H-c)/b)},\qquad H=2N_s/t,$$
--   and on acceptance delete its records. Stop after $t$ acceptances.
--
--   The guarantee `SelectionGood` says that every selected row contains at least $g/t$ elements outside the previously selected rows, and that in the end every row contains at most $4g/t$ elements outside the selected rows, where $g$ is the size of the universe.
--
--   **Formalization Note.** The coin of row $j$ is the event $u_j<p(c)$ for an independent uniform $u_j\in[0,1]$. `tests` counts one membership test for each live record of each processed row.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), proof of Lemma 4.10, (4.17), p.26

import Mathlib

open scoped Classical

namespace SublinearSteiner

/-!
# The reusable-sample procedure

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), proof of Lemma 4.10, (4.17), p.26.

"Keep the sample records as live records. Process the rows in order; if row `R_j` contains `c` live records, accept it
with probability `p(c) = 1/(1 + exp((H − c)/b))`, `H = 2N_s/t`, and on acceptance delete its records. Stop after `t`
acceptances."

**Formalization Note.**
* The acceptance coin of row `j` is the event `u j < p(c)` for a uniform `u j ∈ [0, 1]`, and the coins are independent.
* `tests` counts membership tests: each processed row tests its live records. A row processed after the `t`-th
  acceptance is not processed.
* The procedure reads the rows only through these membership tests, and its parameters do not depend on `|universe|`.
-/

variable {Uni : Type}

/-- `p(c) = 1/(1 + exp((H − c)/b))`, `H = 2N_s/t` (4.17). -/
noncomputable def acceptProb (Ns t : ℕ) (b : ℝ) (c : ℕ) : ℝ :=
  1 / (1 + Real.exp ((2 * (Ns : ℝ) / t - c) / b))

/-- The state of the procedure: live records, selected rows in order, membership tests so far. -/
structure SampleState (Ns Nr : ℕ) where
  /-- The live records. -/
  live : Finset (Fin Ns)
  /-- The selected rows, in order. -/
  selected : List (Fin Nr)
  /-- The number of membership tests so far. -/
  tests : ℕ

/-- Process one row. -/
noncomputable def sampleStep {Ns Nr : ℕ} (R : Fin Nr → Finset Uni) (X : Fin Ns → Uni) (u : Fin Nr → ℝ) (t : ℕ)
    (b : ℝ) (s : SampleState Ns Nr) (j : Fin Nr) : SampleState Ns Nr :=
  if s.selected.length < t then
    let hit := s.live.filter fun l => X l ∈ R j
    if u j < acceptProb Ns t b hit.card then
      ⟨s.live \ hit, s.selected ++ [j], s.tests + s.live.card⟩
    else ⟨s.live, s.selected, s.tests + s.live.card⟩
  else s

/-- The whole run, processing the rows in order. -/
noncomputable def sampleRun {Ns Nr : ℕ} (R : Fin Nr → Finset Uni) (X : Fin Ns → Uni) (u : Fin Nr → ℝ) (t : ℕ)
    (b : ℝ) : SampleState Ns Nr :=
  (List.finRange Nr).foldl (sampleStep R X u t b) ⟨Finset.univ, [], 0⟩

/-- The elements of a row outside a list of rows. -/
noncomputable def outsideRows {Nr : ℕ} (R : Fin Nr → Finset Uni) (L : List (Fin Nr)) (j : Fin Nr) : Finset Uni :=
  R j \ L.toFinset.biUnion R

/-- The guarantee of Lemma 4.10 for a list of selected rows: every selected row contains at least `g/t` elements outside
the previously selected rows, and in the end every row contains at most `4g/t` elements outside the selected rows. -/
def SelectionGood {Nr : ℕ} (R : Fin Nr → Finset Uni) (g t : ℕ) (L : List (Fin Nr)) : Prop :=
  (∀ (m : ℕ) (hm : m < L.length),
      (g : ℝ) / t ≤ ((outsideRows R (L.take m) (L.get ⟨m, hm⟩)).card : ℝ)) ∧
    ∀ j, ((outsideRows R L j).card : ℝ) ≤ 4 * (g : ℝ) / t

end SublinearSteiner


