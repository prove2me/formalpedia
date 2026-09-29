-- Prove2me | Definitions.Def_ModularCurve_JWidth
-- name    : ModularCurve_JWidth
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/522d0565-9365-5b25-9a44-98ea3388ccd9
-- title:
--   The width of a j-invariant: 0↦3, 1728↦2, else 1
-- statement:
--   For a field $K$ with decidable equality and an element $j \in K$, [`ModularCurve.jWidth j`](../def/ModularCurve_JWidth.html#L7) is the natural number defined by the three-way case distinction
--   $$\mathrm{jWidth}(j)=\begin{cases}3,& j=0,\\ 2,& j=1728,\\ 1,&\text{otherwise,}\end{cases}$$
--   where the tests are performed in the order shown, so that the value at $j=0$ is $3$ even in a field in which $0$ and $1728$ happen to coincide. The remaining declarations are the elementary facts about this function. The three defining clauses are recorded separately: `jWidth_of_eq_zero` gives the value $3$ when $j=0$; `jWidth_of_eq_1728` gives the value $2$ from the hypotheses $j=1728$ and $j \neq 0$ (the second hypothesis being what makes the clause correct when $1728=0$ in $K$); and `jWidth_of_ne` gives the value $1$ when $j$ is neither $0$ nor $1728$. The unfolding `jWidth_eq_ite` states that `jWidth j` equals the nested conditional itself. The numerical range is described by `jWidth_pos` ($0 < \mathrm{jWidth}(j)$), by `jWidth_eq_one_or` (the value is $1$, $2$ or $3$) and by `jWidth_dvd_six` (the value divides $6$). Finally, `jWidth_map` asserts invariance under change of field: for any ring homomorphism $f : K \to L$ of fields and any $j \in K$ one has $\mathrm{jWidth}(f(j)) = \mathrm{jWidth}(j)$, which uses that such an $f$ is injective and carries the numeral $1728$ to $1728$.
--
--   **Relation to Mathlib.** Mathlib has no such function; it is the project's own numerical bookkeeping device, a bare case distinction on an element of a field with decidable equality.
--
--   **Where it is used.** The function records, for a $j$-invariant in characteristic $0$ or $\geq 5$, the weight $\tfrac12\,\#\mathrm{Aut}(E)$ of an elliptic curve $E$ with $j(E)=j$ over an algebraically closed field, the quantity that also measures the thickness of the corresponding supersingular point on a modular curve in characteristic $p$. It is used throughout the project as the numerical weight attached to a $j$-invariant in such statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JWidth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

def jWidth {K : Type*} [Field K] [DecidableEq K] (j : K) : ℕ :=
  if j = 0 then 3 else if j = 1728 then 2 else 1

variable {K : Type*} [Field K] [DecidableEq K]

theorem jWidth_of_eq_zero {j : K} (h : j = 0) : jWidth j = 3 := by simp [jWidth, h]

theorem jWidth_of_eq_1728 {j : K} (h : j = 1728) (h0 : j ≠ 0) : jWidth j = 2 := by
  subst h; simp [jWidth, h0]

theorem jWidth_of_ne {j : K} (h0 : j ≠ 0) (h1728 : j ≠ 1728) : jWidth j = 1 := by
  simp [jWidth, h0, h1728]

theorem jWidth_eq_ite (j : K) :
    jWidth j = (if j = 0 then 3 else if j = 1728 then 2 else 1) := rfl

theorem jWidth_pos (j : K) : 0 < jWidth j := by
  unfold jWidth; split_ifs <;> decide

theorem jWidth_eq_one_or (j : K) : jWidth j = 1 ∨ jWidth j = 2 ∨ jWidth j = 3 := by
  unfold jWidth; split_ifs <;> simp

theorem jWidth_dvd_six (j : K) : jWidth j ∣ 6 := by
  unfold jWidth; split_ifs <;> decide

theorem jWidth_map {L : Type*} [Field L] [DecidableEq L] (f : K →+* L) (j : K) :
    jWidth (f j) = jWidth j := by
  have h1728 : f 1728 = (1728 : L) := map_ofNat f 1728
  unfold jWidth
  by_cases hj0 : j = 0
  · subst hj0; simp
  · have hne : f j ≠ 0 := (map_ne_zero_iff f f.injective).mpr hj0
    rw [if_neg hj0, if_neg hne]
    by_cases hj : j = 1728
    · have hfj : f j = 1728 := by rw [hj, h1728]
      rw [if_pos hj, if_pos hfj]
    · have hfj : f j ≠ 1728 := fun h => hj (f.injective (h.trans h1728.symm))
      rw [if_neg hj, if_neg hfj]

end ModularCurve


