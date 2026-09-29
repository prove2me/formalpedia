-- Prove2me | Definitions.Def_BealeConvexMin_SumLargest_sumLargest
-- name    : BealeConvexMin_SumLargest_sumLargest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:37:07.549591+00:00
-- url     : https://prove2.me/theorems/ef61f1bc-bb3c-4c83-828a-ecbb04dcbad5
-- title:
--   Beale (1955), §4: the sum of the $\tau$ largest of a finite family of reals
-- statement:
--   Let $v_1,\dots,v_k$ be real numbers and let $\tau$ be an integer with $0\le\tau\le k$. The **sum of the $\tau$ largest** of the $v_i$ is
--   $$\operatorname{top}_\tau(v)=\max_{S\subseteq\{1,\dots,k\},\ |S|=\tau}\ \sum_{i\in S}v_i .$$
--   If the $v_i$ are arranged in decreasing order $v_{(1)}\ge v_{(2)}\ge\dots\ge v_{(k)}$, this is $v_{(1)}+\dots+v_{(\tau)}$; ties cause no ambiguity, since equal values contribute the same amount whichever of them is chosen. For $\tau=0$ it is the empty sum $0$.
--
--   This is the nonlinear part of the objective in §4 of Beale's paper, where $C$ is "the sum of the $t$ largest of a set of $g$ linear forms"; it is the quantity an opponent who picks $t$ out of $g$ actions would realise.
--
--   **Formalization Note** The family is `v : Fin k → ℝ` and the maximum is `Finset.sup'` over `Finset.univ.powersetCard τ`, which is nonempty exactly when $\tau\le k$. For $\tau>k$ the Lean value is the junk $0$; no statement of the mission uses that case (Theorem 1 always has $\tau\le s+1$ forms).
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), §4, first paragraph and the ordering display

import Mathlib

namespace BealeConvexMin.SumLargest

/-- Beale (1955), §4, p. 177: "the sum of the `t` largest" of a finite family of reals.

For `v : Fin k → ℝ` and `τ ≤ k`, `sumLargest τ v` is the maximum, over all `τ`-element subsets
`S ⊆ {0, …, k-1}`, of `Σ_{i ∈ S} v i`. With ties this is still the sum of the `τ` largest values
counted with multiplicity. For `τ = 0` it is `0` (the empty sum).

For `τ > k` there is no `τ`-element subset and the value is the junk `0`; no statement of this
mission uses that case. -/
noncomputable def sumLargest {k : ℕ} (τ : ℕ) (v : Fin k → ℝ) : ℝ :=
  if h : τ ≤ k then
    (Finset.univ.powersetCard τ).sup'
      (Finset.powersetCard_nonempty.mpr (by simpa using h))
      (fun S => ∑ i ∈ S, v i)
  else 0

end BealeConvexMin.SumLargest


