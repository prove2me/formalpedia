-- Prove2me | Definitions.Def_SecretaryWD_KnownOpt_Model
-- name    : SecretaryWD_KnownOpt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:36:26.848102+00:00
-- url     : https://prove2.me/theorems/4be2af41-04bc-46b1-82ac-ad31fe614bf5
-- title:
--   The discounted secretary problem, E[OPT], and the threshold algorithm A of §4.2
-- statement:
--   This file sets up the discounted secretary problem of Babaioff, Dinitz, Gupta, Immorlica and Talwar (§2) and the objects of their §4.2.
--
--   **The problem.** There are $n \ge 1$ elements. Each element $e$ has a value $v(e) \ge 0$, and each time $t \in \{1,\dots,n\}$ has a discount $d(t) \ge 0$. The elements arrive in a uniformly random order $\pi$, a bijection from times to elements: element $\pi(t)$ arrives at time $t$. Selecting the element that arrives at time $i$ earns $d(i)\,v(\pi(i))$.
--
--   **The offline optimum.** On the order $\pi$ the offline optimum is $\mathrm{OPT}(\pi)=\max_{i=1}^n d(i)\,v(\pi(i))$, and
--
--   $$\mathbf E[\mathrm{OPT}] = \sum_{\pi\in S_n}\frac{1}{n!}\max_{i=1}^n \{d(i)\,v(\pi(i))\}.$$
--
--   **Algorithm A.** For a real parameter $Z$, algorithm $\mathcal A$ picks the first element $e$ seen, say at time $j$, that satisfies $v(e)\,d(j)\ge Z/2$, and earns $d(j)\,v(\pi(j))$; if no time qualifies it picks nothing and earns $0$. It knows $Z$ and $d$, and decides at time $j$ from what it has seen up to time $j$. Its expected value is $\mathbf E[\mathcal A]=\sum_{\pi\in S_n}\frac1{n!}\,(\text{value of }\mathcal A\text{ on }\pi)$. The algorithm is defined for every real $Z$; the hypothesis $Z\le\mathbf E[\mathrm{OPT}]$ is part of the theorems, not of the definition.
--
--   **Proof objects of Theorem 4.7.**
--   1. The accepting permutations $S_{acc}=\{\pi\in S_n : \max_{i=1}^n d(i)v(\pi(i))\ge Z/2\}$, the orders on which $\mathcal A$ picks some element.
--   2. Their contribution to the optimum, $L=\sum_{\pi\in S_{acc}}\frac1{n!}\max_{i=1}^n\{d(i)v(\pi(i))\}$.
--   3. For a time $i$ and an element $j$, the set $G_{ij}$ of orders on which $\mathcal A$ chooses element $j$ at time $i$: $\pi(i)=j$ and $d(k)v(\pi(k))<Z/2$ for every earlier time $k<i$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Times and elements are both `Fin n`; the paper's time $t$ is the index $t-1$, and an order is `π : Equiv.Perm (Fin n)` read as time ↦ element. The type-class `[NeZero n]` makes the maximum over times a genuine maximum (`Finset.sup'`). Expectations are the finite averages $\frac1{n!}\sum_\pi$. The paper's "$v(i)d(j)$" in the definition of $\mathcal A$ is read as $v(e)d(j)$. All thresholds are non-strict ($\ge Z/2$) exactly as in the paper.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 3, §2 (Discounted Secretary Problems); p. 7, §4.2 (Algorithm A); p. 8, proof of Theorem 4.7 (E[OPT], S_acc, L, G_ij)

import Mathlib

namespace SecretaryWD.KnownOpt

open Finset

variable {n : ℕ}

/-- The product `d(i) · v(π(i))` earned by selecting, at time `i`, the element `π(i)` that
arrives then. Times and elements are both `Fin n`; the paper's time `t ∈ {1, …, n}` is the
index `t` shifted down by one, and `π : Equiv.Perm (Fin n)` is read as time ↦ element. -/
def discProd (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  d i * v (π i)

/-- The offline optimum on the order `π`: `OPT(π) = max_{i=1}^n d(i) v(π(i))`. The instance
`[NeZero n]` makes `Fin n` nonempty, so the maximum is a genuine maximum over all `n` times. -/
noncomputable def optValue [NeZero n] (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty (discProd d v π)

/-- `E[OPT] = Σ_{π ∈ S_n} (1/n!) max_{i=1}^n d(i) v(π(i))`, the expectation over a uniformly
random arrival order. -/
noncomputable def expectedOPT [NeZero n] (d v : Fin n → ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) * optValue d v π

/-- Algorithm A of §4.2 with parameter `Z`: on the order `π` it selects the first time `j` with
`d(j) · v(π(j)) ≥ Z/2`, or nothing (`none`) if there is no such time. It uses only `Z`, `d`
and the products seen at times up to `j`. -/
noncomputable def selectTime (d v : Fin n → ℝ) (Z : ℝ) (π : Equiv.Perm (Fin n)) : Option (Fin n) :=
  if h : ∃ j, Z / 2 ≤ discProd d v π j then
    some (Fin.find (fun j => Z / 2 ≤ discProd d v π j) h)
  else none

/-- The value algorithm A earns on the order `π`: `d(j) · v(π(j))` at the selected time `j`,
or `0` if it selects nothing. -/
noncomputable def algValue (d v : Fin n → ℝ) (Z : ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  match selectTime d v Z π with
  | none => 0
  | some j => discProd d v π j

/-- `E[A] = Σ_{π ∈ S_n} (1/n!) · (value of A on π)`. -/
noncomputable def expectedAlg (d v : Fin n → ℝ) (Z : ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) * algValue d v Z π

/-- The accepting permutations `S_acc = {π ∈ S_n : max_{i=1}^n d(i) v(π(i)) ≥ Z/2}`. -/
noncomputable def acceptingPerms [NeZero n] (d v : Fin n → ℝ) (Z : ℝ) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun π => Z / 2 ≤ optValue d v π)

/-- `L = Σ_{π ∈ S_acc} (1/n!) max_{i=1}^n d(i) v(π(i))`, the contribution of the accepting
permutations to `E[OPT]` (Eq. (4.1)). -/
noncomputable def acceptingContribution [NeZero n] (d v : Fin n → ℝ) (Z : ℝ) : ℝ :=
  ∑ π ∈ acceptingPerms d v Z, (1 / (n.factorial : ℝ)) * optValue d v π

/-- `G_{ij}`: the permutations on which algorithm A chooses element `j` at time `i`, i.e.
`π(i) = j` and `d(k) v(π(k)) < Z/2` for every earlier time `k < i`. -/
noncomputable def goodPerms (d v : Fin n → ℝ) (Z : ℝ) (i j : Fin n) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun π => π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2)

end SecretaryWD.KnownOpt


