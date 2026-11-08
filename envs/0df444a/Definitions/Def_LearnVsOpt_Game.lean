-- Prove2me | Definitions.Def_LearnVsOpt_Game
-- name    : LearnVsOpt_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:20.601788+00:00
-- url     : https://prove2.me/theorems/60e22df2-8cbe-4aa2-ae87-81027511e0db
-- title:
--   Repeated budgeted game: the matrices $U_O,U_L,C_O,C_L$ and $\hat n_O$
-- statement:
--   A **repeated budgeted game** between an optimizer with $n_O$ actions and a learner with $n_L$ actions is given by four matrices $U_O,U_L,C_O,C_L\in[0,1]^{n_O\times n_L}$. When the optimizer plays $i$ and the learner $j$, the entries $U_O[i,j]$ and $C_O[i,j]$ are the optimizer's utility and cost, and $U_L[i,j]$, $C_L[i,j]$ the learner's.
--
--   The number $\hat n_O=|\mathcal{UC}|$ counts the distinct utility-cost vectors $uc=(U_L[i,:],C_L[i,:])$, $i\in[n_O]$, which the optimizer can induce for the learner; two actions with the same vector are the same to the learner but may differ for the optimizer.
--
--   **Formalization Note** Actions are `Fin nO` and `Fin nL`. The budgets, the horizon and the null actions are arguments and hypotheses of the statements.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, §2, p.6; §3, p.7

import Mathlib

namespace LearnVsOpt

/-- **Repeated budgeted game** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in
Budgeted Games*, arXiv:2611.05580, §2, p.6). The optimizer has `nO` actions and the learner `nL`
actions; `UO i j`, `CO i j` are the optimizer's utility and cost and `UL i j`, `CL i j` the learner's,
all in `[0, 1]`.

**Formalization Note.** Actions are `Fin nO` and `Fin nL`. The budgets `ρL`, `ρO` and the horizon `T`
are arguments of the statements, and the null actions are hypotheses of the statements. -/
structure Game (nO nL : ℕ) where
  /-- The optimizer's utility `U_O`. -/
  UO : Matrix (Fin nO) (Fin nL) ℝ
  /-- The learner's utility `U_L`. -/
  UL : Matrix (Fin nO) (Fin nL) ℝ
  /-- The optimizer's cost `C_O`. -/
  CO : Matrix (Fin nO) (Fin nL) ℝ
  /-- The learner's cost `C_L`. -/
  CL : Matrix (Fin nO) (Fin nL) ℝ
  UO_mem : ∀ i j, UO i j ∈ Set.Icc (0 : ℝ) 1
  UL_mem : ∀ i j, UL i j ∈ Set.Icc (0 : ℝ) 1
  CO_mem : ∀ i j, CO i j ∈ Set.Icc (0 : ℝ) 1
  CL_mem : ∀ i j, CL i j ∈ Set.Icc (0 : ℝ) 1

/-- `n̂_O = |𝒰𝒞|` (§3, p.7): the number of distinct utility-cost vectors `(U_L[i, :], C_L[i, :])`,
`i ∈ [n_O]`, of the game. This is the game's count, not the size of a dictionary. -/
noncomputable def Game.nHat {nO nL : ℕ} (G : Game nO nL) : ℕ :=
  open Classical in (Finset.univ.image (fun i : Fin nO => (G.UL i, G.CL i))).card

end LearnVsOpt


