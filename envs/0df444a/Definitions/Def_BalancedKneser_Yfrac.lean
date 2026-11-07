-- Prove2me | Definitions.Def_BalancedKneser_Yfrac
-- name    : BalancedKneser_Yfrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:51.671199+00:00
-- url     : https://prove2.me/theorems/b22c9d09-fe82-4f5d-a843-c5a232e4354d
-- title:
--   Fractional-center complex $Y_c$ (families with a common fractional radius-$c$ center)
-- statement:
--   Identify a $k$-subset $A$ of $[N]$ with its indicator vector in the **hypersimplex**
--   $$
--   \Delta(N,k)=\Big\{x\in[0,1]^N:\ \sum_i x_i=k\Big\},
--   $$
--   and write $x(A)=\sum_{i\in A}x_i$. A point $x\in\Delta(N,k)$ is a **fractional radius-$c$ center** of a family $\sigma$ of $k$-sets if $x(A)\ge k-c$ for every $A\in\sigma$. The complex $Y_c$ has the same vertices as $C_c(N,k)$, and its nonempty faces are the families having a fractional radius-$c$ center; equivalently, $Y_c$ is the nerve of the caps $P_{c,A}=\{x\in\Delta(N,k): x(A)\ge k-c\}$.
--
--   An integral center supplies a fractional one (its indicator vector), so $C_c(N,k)\subseteq Y_c$; the module proves this inclusion, which is the map $i_c$ of Theorem 11.1.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §4.2, p.9 (PDF p.11): hypersimplex, Y₂; §9.4, p.20 (PDF p.22): Y_c and i_c

import Mathlib
import Definitions.Def_BalancedKneser_CC

namespace BalancedKneser

/-- **The fractional-center complex** `Y_c` (Alipour–Jafari, arXiv:2611.04486v1, §4.2, p.9
(PDF p.11) and §9.4, p.20 (PDF p.22)). In the hypersimplex
`∆(N, k) = {x ∈ [0,1]^N : Σᵢ xᵢ = k}` a fractional radius-`c` center of a family `σ` of
`k`-subsets of `[N]` is a point `x` with `x(A) = Σ_{i ∈ A} xᵢ ≥ k − c` for every `A ∈ σ`. The
nonempty faces of `Y_c` are the families having a fractional radius-`c` center; equivalently,
`Y_c` is the nerve of the caps `P_{c,A}`.

Formalization Note: the vertex set (the `k`-subsets of `Fin N`) is the same as that of
`CC c N k`, so `CC c N k ⊆ Yfrac c N k` (`CC_subset_Yfrac`) gives the inclusion
`i_c : C_c(N, k) ↪ Y_c`. -/
def Yfrac (c N k : ℕ) : Set (Finset (KSet N k)) :=
  {σ | σ.Nonempty ∧ ∃ x : Fin N → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = k ∧
    ∀ A ∈ σ, (k : ℝ) - c ≤ ∑ i ∈ A.1, x i}

/-- An integral center supplies a fractional one (its indicator vector), so
`C_c(N, k) ⊆ Y_c` (arXiv:2611.04486v1, §9.4, p.20 (PDF p.22)). -/
theorem CC_subset_Yfrac (c N k : ℕ) : CC c N k ⊆ Yfrac c N k := by
  rintro σ ⟨hne, Z, hZ, hA⟩
  refine ⟨hne, fun i => if i ∈ Z then 1 else 0, fun i => ?_, ?_, fun A hAσ => ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · rw [Finset.sum_boole]
    have : (Finset.univ.filter (fun i => i ∈ Z)) = Z := by ext; simp
    simp only [this, hZ]
  · rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
    have h' : (k : ℝ) ≤ ((A.1 ∩ Z).card : ℝ) + c := by exact_mod_cast hA A hAσ
    linarith

end BalancedKneser


