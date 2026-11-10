-- Prove2me | Definitions.Def_PrivGaussMS_Pruning
-- name    : PrivGaussMS_Pruning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:10:02.129751+00:00
-- url     : https://prove2.me/theorems/e9a82bfe-630a-4cb8-95c5-5490e41c1869
-- title:
--   Leverage pruning, thresholds $u_j$ (16), score $g$, weights $\rho_i$, statistic $B$ and recorded set $A$ (17)
-- statement:
--   At threshold $u$, pruning starts from $I=[n]$ and repeatedly deletes the smallest $i\in I$ with $n\,\tilde x_i^TT_I^{-1}\tilde x_i>u$, returning the survivors when no violation remains; if $T_I$ is singular at any point it returns the empty set. The factor $n$ stays fixed. For integers $k,\lambda\ge1$ the thresholds are
--   $$u_j=\frac{\lambda}{1-j\lambda/n},\qquad 0\le j\le 2k,$$
--   and $I_j$ is the survivor set at $u_j$. Then
--   $$g=\min\bigl(\{j\in\{0,\dots,k-1\}:|I_j|\ge n-j\}\cup\{k\}\bigr),\qquad \rho_i=\frac1k\sum_{j=k+1}^{2k}\mathbf 1\{i\in I_j\},\qquad B=\sum_i\rho_i\tilde x_i\tilde x_i^T,$$
--   and the recorded set is $A=[n]\setminus I_k$.
--
--   These are the stable weights of the private sampler.
--
--   **Formalization Note** A pruning run also records the deleted rows in deletion order and whether it stopped on a singular statistic. Smallest means least 0-based index.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), §B.3.2, eqs. (16)–(17), p.37

import Mathlib
import Definitions.Def_PrivGaussMS_Statistics

open MeasureTheory Matrix

namespace PrivGaussMS

/-!
# Leverage pruning, the thresholds (16), the score `g`, the weights `ρ` and the recorded set `A`

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), §B.3.2, eqs. (16)–(17), p.37.

"At threshold `u`, start with `I = [n]` and repeatedly delete the smallest `i ∈ I` satisfying
`n x̃_iᵀ T_I^{−1} x̃_i > u`. Return the survivors when no violation remains. If `T_I` is singular at
any point, return the empty set. The factor `n` is kept fixed throughout pruning." (p.37)

**Formalization Note.**
* `prune x u` runs this procedure deterministically and records, besides the survivor set, the
  list of deleted rows in deletion order and whether the run stopped on a singular statistic
  (`aborted`, survivors `∅`). "Smallest" is the least `Fin n` index. The recursion has fuel `n + 1`:
  every non-final step deletes a row, and after `n` deletions `T_∅ = 0` is singular, so the run
  always ends within the fuel (the fuel-`0` branch is unreachable).
* `uThr n λ j = λ/(1 − jλ/n)` (16); `survivorsAt x λ j = I_j` is pruning at `u_j` from the full
  dataset; `score x k λ = g = min({j < k : |I_j| ≥ n − j} ∪ {k})`; `weights x k λ i = ρ_i =
  k⁻¹ Σ_{j=k+1}^{2k} 1{i ∈ I_j}`; `Bstat x k λ = B = Σ ρ_i x̃_i x̃_iᵀ`; `recordedSet x k λ = [n] \ I_k`
  (recorded by the paper when `g < k`). `n − j` is natural subtraction; it is only evaluated at
  `j < k ≤ n` under the hypotheses `n ≥ 16kλ` of (16).
-/

variable {n d : ℕ}

/-- `n x̃_iᵀ T_I^{−1} x̃_i`, the leverage of row `i` in `T_I` multiplied by `n` (p.37). -/
noncomputable def leverage (x : Fin n → Vec d) (I : Finset (Fin n)) (i : Fin n) : ℝ :=
  (n : ℝ) * (aug x i ⬝ᵥ ((statI x I)⁻¹ *ᵥ aug x i))

/-- The output of a pruning run: survivors, the deleted rows in order, and whether the run
stopped on a singular statistic. -/
structure PruneResult (n : ℕ) where
  survivors : Finset (Fin n)
  deleted : List (Fin n)
  aborted : Bool

open Classical in
/-- One pruning run with fuel `f` from the current set `I` and deletion record `del`. -/
noncomputable def pruneAux (x : Fin n → Vec d) (u : ℝ) :
    ℕ → Finset (Fin n) → List (Fin n) → PruneResult n
  | 0, I, del => ⟨I, del, false⟩
  | f + 1, I, del =>
    if (statI x I).det = 0 then ⟨∅, del, true⟩
    else
      if h : (I.filter fun i => u < leverage x I i).Nonempty then
        pruneAux x u f (I.erase ((I.filter fun i => u < leverage x I i).min' h))
          (del ++ [(I.filter fun i => u < leverage x I i).min' h])
      else ⟨I, del, false⟩

/-- Pruning at threshold `u` from the full dataset (p.37). -/
noncomputable def prune (x : Fin n → Vec d) (u : ℝ) : PruneResult n :=
  pruneAux x u (n + 1) Finset.univ []

/-- The thresholds `u_j = λ/(1 − jλ/n)` of (16). -/
noncomputable def uThr (n lam j : ℕ) : ℝ := (lam : ℝ) / (1 - (j : ℝ) * lam / n)

/-- `I_j`: the survivor set of pruning at threshold `u_j` (p.37). -/
noncomputable def survivorsAt (x : Fin n → Vec d) (lam j : ℕ) : Finset (Fin n) :=
  (prune x (uThr n lam j)).survivors

open Classical in
/-- The stability score `g = min({j ∈ {0, …, k−1} : |I_j| ≥ n − j} ∪ {k})` (17). -/
noncomputable def score (x : Fin n → Vec d) (k lam : ℕ) : ℕ :=
  if h : ∃ j, j < k ∧ n - j ≤ (survivorsAt x lam j).card then Nat.find h else k

open Classical in
/-- The weights `ρ_i = k⁻¹ Σ_{j=k+1}^{2k} 1{i ∈ I_j}` (17). -/
noncomputable def weights (x : Fin n → Vec d) (k lam : ℕ) (i : Fin n) : ℝ :=
  (k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc (k + 1) (2 * k), if i ∈ survivorsAt x lam j then (1 : ℝ) else 0

/-- The stable weighted statistic `B = Σ_i ρ_i x̃_i x̃_iᵀ` (17). -/
noncomputable def Bstat (x : Fin n → Vec d) (k lam : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Bweighted x (weights x k lam)

/-- The recorded set `A = [n] \ I_k` (p.37). -/
noncomputable def recordedSet (x : Fin n → Vec d) (k lam : ℕ) : Finset (Fin n) :=
  Finset.univ \ survivorsAt x lam k

end PrivGaussMS


