-- Prove2me | Definitions.Def_WeberGittins_Submodular_PartialInterleavedSum
-- name    : WeberGittins_Submodular_PartialInterleavedSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:27.874397+00:00
-- url     : https://prove2.me/theorems/2af721ed-f63c-4f43-96a5-b1a7e1a2e2b7
-- title:
--   Proof of Theorem 4, p. 1030 — $U_t(I)$, the sum of the first $t$ terms of the nonincreasing interleaving of the sequences $(\gamma_{jk})_{k\ge0}$, $j\in I$
-- statement:
--   Let $n\ge0$ be the number of bandits, indexed by $j\in\{1,\dots,n\}$, and let $H_j=(H_{j0},H_{j1},H_{j2},\dots)$ be a sequence of real numbers for each bandit $j$ (in the application, $H_{jk}=\gamma_{jk}$ is the prevailing charge of bandit $j$ after it has been played $k$ times). For a set of bandits $I\subseteq\{1,\dots,n\}$ and a number of plays $t\ge0$, an **allocation of $t$ plays to $I$** is a vector $m=(m_1,\dots,m_n)$ of nonnegative integers with $m_j=0$ for $j\notin I$ and $m_1+\dots+m_n=t$. Define
--   $$
--   U_t(I)=\max\Big\{\sum_{j\in I}\sum_{u=0}^{m_j-1}H_{ju}\;:\;m\text{ an allocation of }t\text{ plays to }I\Big\}\quad(I\neq\emptyset),\qquad U_t(\emptyset)=0 .
--   $$
--   The set of allocations is finite and, for $I\neq\emptyset$, nonempty, so the maximum exists.
--
--   Weber defines $U_t(I)$ as the sum of the charges paid during the first $t$ plays of the restricted problem $P(I)$ played optimally, computed "by interleaving into nonincreasing order the sequences $\{\gamma_{jk}\}$, $j\in I$, and then summing the first $t$ elements of the resulting sequence". When every $H_j$ is nonincreasing, the first $t$ terms of any nonincreasing interleaving consist of an initial segment of each sequence, of lengths forming an allocation, and no other allocation collects more; so the maximum above is exactly Weber's $U_t(I)$, independently of how ties are broken. This is the quantity in inequality (10).
--
--   **Formalization Note** The maximum is `Finset.sup'` over the finite set `playAllocations I t` of maps `m : Fin n → ℕ` (each $m_j\le t$), with nonemptiness proved in the module. The case $I=\emptyset$ is set to $0$ explicitly: the problem with no bandits pays nothing. The definition makes sense for arbitrary real sequences; the monotonicity of $H_j$ is a hypothesis of the theorems that use it. Sequences are indexed from $k=0$, matching Weber's $\gamma_{j0}\ge\gamma_{j1}\ge\cdots$ (the printed range $\{\gamma_{jk}\}_{k=1}^\infty$ is a misprint for $k\ge0$).
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1030, proof of Theorem 4 (definition of U_t(I))

import Mathlib

namespace WeberGittins.Submodular

/-- The allocations of `t` plays to the bandits of `I`: the maps `m : Fin n → ℕ` (bandit `j`
is played `m j` times) with `m j = 0` for `j ∉ I` and `∑ j, m j = t`. Every such `m` has
`m j ≤ t`, so this finite set is cut out of the box `{0, …, t}ⁿ`. -/
def playAllocations {n : ℕ} (I : Finset (Fin n)) (t : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (t + 1)).filter
    fun m => (∀ j, j ∉ I → m j = 0) ∧ ∑ j, m j = t

lemma playAllocations_nonempty {n : ℕ} {I : Finset (Fin n)} (hI : I ≠ ∅) (t : ℕ) :
    (playAllocations I t).Nonempty := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hI
  refine ⟨Pi.single i t, ?_⟩
  simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · simp [h]
  · have : j ≠ i := fun h => hj (h ▸ hi)
    simp [this]
  · simp [Finset.sum_pi_single']

/-- Weber (1992), proof of Theorem 4, p. 1030: `U_t(I)`, the sum of the first `t` elements of the
interleaving into nonincreasing order of the sequences `(H j k)_{k ≥ 0}`, `j ∈ I`.

It is written as the largest total of `t` terms taken as initial segments of the sequences of the
bandits of `I`: `max { ∑_{j ∈ I} ∑_{u < m j} H j u : m ∈ playAllocations I t }`. When every
`H j` is nonincreasing, this maximum is exactly the sum of the first `t` terms of the nonincreasing
interleaving (whatever the tie-breaking). `U_t(∅) = 0`: with no bandit nothing is paid. -/
noncomputable def partialInterleavedSum {n : ℕ} (H : Fin n → ℕ → ℝ) (I : Finset (Fin n))
    (t : ℕ) : ℝ :=
  if hI : I = ∅ then 0 else
    (playAllocations I t).sup' (playAllocations_nonempty hI t)
      fun m => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u

end WeberGittins.Submodular


