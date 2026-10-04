-- Prove2me | Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel
-- name    : SecretaryWD_DiscUpper_DiscountedModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:36:46.052351+00:00
-- url     : https://prove2.me/theorems/a6fdef92-7d9d-4ae3-88d8-5aac91b5e0cc
-- title:
--   The discounted secretary problem: offline optimum, discount classes and $\mathsf{OPT}_c$
-- statement:
--   In the **discounted secretary problem** there are $n$ elements with values $v(e)\ge 0$ and a discount function $d$ on the times $\{1,\dots,n\}$ with $d(t)\ge 0$. The elements arrive in a uniformly random order $\pi$ (element $\pi(t)$ at time $t$), and selecting the element arriving at time $t$ earns $d(t)\,v(\pi(t))$.
--
--   1. The **offline optimum** on order $\pi$ is $\mathsf{OPT}(\pi)=\max_t d(t)\,v(\pi(t))$, and the benchmark is its expectation $\mathbb E_\pi[\mathsf{OPT}]$.
--   2. $d_{\max}=\max_t d(t)$ and $v_{\max}=\max_e v(e)$.
--   3. The **optimal time** on order $\pi$ is the smallest time $t$ attaining $\max_s d(s)\,v(\pi(s))$.
--   4. For $c\ge 1$, the **$c$-th discount class** is the set of times
--   $$P_c=\{\,i : d(i)\in I_c\,\},\qquad I_c=\bigl(2^{-c}d_{\max},\;2^{-(c-1)}d_{\max}\bigr].$$
--   5. $\mathsf{OPT}_c$ is the part of $\mathbb E_\pi[\mathsf{OPT}]$ earned at times of class $c$:
--   $$\mathsf{OPT}_c=\mathbb E_\pi\Bigl[\sum_{i\in P_c} \mathbf 1\{i \text{ is the optimal time}\}\; d(i)\,v(\pi(i))\Bigr]=\sum_{i\in P_c} d(i)\sum_j v(j)\,\Pr[\pi(i)=j \wedge i \text{ is the optimal time}].$$
--
--   The classes are disjoint and cover every time with $d(i)>0$; times with $d(i)=0$ lie in no class and contribute nothing to $\mathsf{OPT}$. These objects carry the analysis of Theorem 4.4.
--
--   **Formalization Note.** Times and elements are $\{0,\dots,n-1\}$. Maxima are taken as suprema over a finite index set (equal to $0$ when $n=0$, which no theorem of the mission uses). The paper's event "$d(i)v(j)\in\mathsf{OPT}$" presumes a unique optimal time; the formalization fixes the smallest maximizing time, so that the $\mathsf{OPT}_c$ add up to $\mathbb E_\pi[\mathsf{OPT}]$. The interval $I_c$ is written $d_{\max}/2^c < d(i) \le 2d_{\max}/2^c$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), pp. 3-4, Section 2 (discounted secretary problems, competitive ratio) and p. 7, proof of Theorem 4.4 (d_max, v_max, I_c, P_c, OPT_c)

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

namespace SecretaryWD.DiscUpper

/-- The offline optimum on arrival order `π`: `OPT(π) = max_t d(t) · v(π(t))`. -/
noncomputable def optValue {n : ℕ} (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ⨆ t : Fin n, d t * v (π t)

/-- `E_π[OPT]`, the expected offline optimum over the uniform arrival order. -/
noncomputable def expectedOpt {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  uniformAvg fun π => optValue d v π

/-- The maximum discount `d_max = max_t d(t)`. -/
noncomputable def dmax {n : ℕ} (d : Fin n → ℝ) : ℝ := ⨆ t : Fin n, d t

/-- The maximum value `v_max = max_e v(e)`. -/
noncomputable def vmax {n : ℕ} (v : Fin n → ℝ) : ℝ := ⨆ e : Fin n, v e

/-- `t` is *the* optimal time on order `π`: it attains `max_s d(s) v(π(s))`, and it is the
smallest time that does. -/
def IsOptTime {n : ℕ} (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n) : Prop :=
  (∀ s : Fin n, d s * v (π s) ≤ d t * v (π t)) ∧
    ∀ s : Fin n, s < t → d s * v (π s) < d t * v (π t)

/-- The `c`-th discount class `P_c = {i : d(i) ∈ (2^{-c} d_max, 2^{-(c-1)} d_max]}`, written
as `d_max / 2^c < d(i) ≤ 2 d_max / 2^c`. -/
noncomputable def discountClass {n : ℕ} (d : Fin n → ℝ) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => dmax d / 2 ^ c < d i ∧ d i ≤ 2 * dmax d / 2 ^ c

open Classical in
/-- `OPT_c`: the part of `E_π[OPT]` earned at times of class `c`,
`OPT_c = E_π[ ∑_{i ∈ P_c} 1{i is the optimal time} · d(i) v(π(i)) ]`. -/
noncomputable def optClass {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) : ℝ :=
  uniformAvg fun π =>
    ∑ t ∈ discountClass d c, if IsOptTime d v π t then d t * v (π t) else 0

end SecretaryWD.DiscUpper


