-- Prove2me | Definitions.Def_AlmostMMS_Supplement_fracTauH
-- name    : AlmostMMS_Supplement_fracTauH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:01.740214+00:00
-- url     : https://prove2.me/theorems/4013c15e-8d31-4e8f-99b5-f9f7e2f0001f
-- title:
--   §2 tail value $T_i$, deficit $\Delta(\pi)$, tail load rate $\tau_i(\pi)$ and total tail load $\tau(x,\Pi)$ for a common head size $h$
-- statement:
--   Fix $n$ agents, items $e_1,\dots,e_m$ with item values $v_i(e)\ge0$, and a common **head size** $h$: items $e_1,\dots,e_h$ are head items and $e_{h+1},\dots,e_m$ are tail items.
--
--   1. The **tail value** of agent $i$ is $T_i=\sum_{e>h} v_i(e)$.
--   2. The **deficit** of a demand profile $\pi$ (a finite multiset of demands, with value $v(\pi)=\sum_{\alpha\in\pi}\alpha$) is $\Delta(\pi)=(1-v(\pi))_+=\max\{0,\,1-v(\pi)\}$.
--   3. The **tail load rate** of agent $i$ for $\pi$ is
--   $$
--   \tau_i(\pi)=\begin{cases}\Delta(\pi)/T_i, & \pi\ne\bot\text{ and }T_i>0,\\ 0, & \text{otherwise,}\end{cases}
--   $$
--   where $\bot$ is the no-profile (agent not selected).
--   4. For fractional profiles $x=\{x_i\}_{i\in N}$ over a shared set $\Pi$, the **total fractional tail load** is
--   $$
--   \tau(x,\Pi)=\sum_{i\in N}\sum_{\pi\in\Pi}x_i(\pi)\,\tau_i(\pi).
--   $$
--
--   $\tau_i(\pi)$ is the fraction of every tail item agent $i$ would need to make up the missing value $\Delta(\pi)$; the head-rounding theorem keeps the total $\tau(x,\Pi)$ from growing.
--
--   **Formalization Note** Item $e_j$ is position $j-1$, so a tail item is a position at least $h$. The head size is common to all agents, as in §2; this differs from the per-agent head threshold and the deficit $(1-1/q-v(\pi))_+$ of §3, which are separate published definitions.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 2.6, p.14; Definition 2.10, p.14; Definition 2.11, p.15; Definition 2.15, p.17

import Mathlib

namespace AlmostMMS.Supplement

open Finset

/-- **Tail value with a common head size** `T_i = ∑_{e > h} v_i(e)` (Definition 2.6, p.14).
Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** Item `e_j` is the position `⟨j - 1, _⟩ : Fin m`, so the tail item `e > h` is
a position with `h ≤ e.val`. The head size `h` is common to all agents (§2), unlike the per-agent
`AlmostMMS.headCount` of §3. -/
noncomputable def tailValH {n m : ℕ} (v : Fin n → Fin m → ℝ) (h : ℕ) (i : Fin n) : ℝ :=
  ∑ e with h ≤ e.val, v i e

/-- **Deficit** `Δ(π) = (1 - v(π))₊` of a head profile `π ≠ ⊥` (Definition 2.10, p.14), where
`v(π) = ∑_{α ∈ π} α` (Definition 2.2, p.12). This is the §2 deficit, not the §3 one
(`AlmostMMS.deficit`, which subtracts an extra `1/q`). -/
noncomputable def deficitH (π : Multiset ℝ) : ℝ :=
  max 0 (1 - π.sum)

/-- **Tail load rate** `τ_i(π)` (Definition 2.11, p.15): `Δ(π)/T_i` when `π ≠ ⊥` and `T_i > 0`, and
`0` otherwise. The no-profile `⊥` is `none`; a profile `π` is `some π`. -/
noncomputable def tauOfH {n m : ℕ} (v : Fin n → Fin m → ℝ) (h : ℕ) (i : Fin n) :
    Option (Multiset ℝ) → ℝ
  | none => 0
  | some π => if 0 < tailValH v h i then deficitH π / tailValH v h i else 0

/-- **Total fractional tail load** `τ(x, Π) = ∑_{i ∈ N} ∑_{π ∈ Π} x_i(π) τ_i(π)` (Definition 2.15,
p.17), with the §2 rate `τ_i` for head size `h`. -/
noncomputable def fracTauH {n m : ℕ} (v : Fin n → Fin m → ℝ) (h : ℕ)
    (Ps : Finset (Option (Multiset ℝ))) (x : Fin n → Option (Multiset ℝ) → ℝ) : ℝ :=
  ∑ i, ∑ π ∈ Ps, x i π * tauOfH v h i π

end AlmostMMS.Supplement


