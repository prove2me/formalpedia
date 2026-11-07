-- Prove2me | Definitions.Def_TIEMaximin_Comparison
-- name    : TIEMaximin_Comparison
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:42:17.475231+00:00
-- url     : https://prove2.me/theorems/7d14ee2b-2754-4170-a0a3-0e0ae0708126
-- title:
--   Popularity prefixes, $\rho$, eligibility, cost and comparison sets
-- statement:
--   Order the goods by decreasing $f_g$, ties broken by index, and let $P_t$ be the first $t$ goods, $0\le t\le m$. For $Q\subseteq M$, $\rho(Q)=\sum_{i\in N}h_i(M\setminus Q)$ is the expected number of reserved goods outside $Q$.
--
--   For a deficient agent $i$, a prefix $P_t$ is **eligible** if $x_{ig}\ge p_i/k_i$ for all $g\in L_i\setminus P_t$, and its **cost** is $|P_t\setminus H_i|+\lceil\rho(P_t)\rceil$. Let $\ell_i$ be the smallest $t$ minimizing the cost among eligible prefixes, $Q_i=P_{\ell_i}$ her **comparison set**, and $d_i$ its cost.
--
--   The comparison sets are the low goods an agent gives up; they are nested, which is what allows one matching to cap the reservations outside all of them.
--
--   **Formalization Note** $\ell_i$ is a natural-number infimum of a set that is never empty, since the full prefix $P_m=M$ is eligible.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definitions 3.13, 3.14, eqs. (10), (11), p.18

import Mathlib
import Definitions.Def_TIEMaximin_Deficient

namespace TIEMaximin

open Finset

/-- The position of good `g` in the popularity order (Definition 3.13, p.18), 0-based: the number of
goods with more nominations, or as many nominations and a smaller index (arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…). -/
noncomputable def rankP {n m : ℕ} (v : Fin n → Fin m → ℝ) (g : Fin m) : ℕ :=
  #{g' : Fin m | nom v g < nom v g' ∨ (nom v g' = nom v g ∧ g' < g)}

/-- **Popularity prefixes** `P_t` (Definition 3.13, p.18): the first `t` goods in order of decreasing
`f_g`, ties broken by index (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def prefixP {n m : ℕ} (v : Fin n → Fin m → ℝ) (t : ℕ) : Finset (Fin m) :=
  {g | rankP v g < t}

/-- `ρ(Q) = Σ_{i∈N} h_i(M ∖ Q)`, the expected number of reserved goods outside `Q` (Definition 3.13,
p.18 of arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def rho {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (Q : Finset (Fin m)) : ℝ :=
  ∑ i, ∑ g ∈ univ \ Q, hRet α v i g

/-- **Eligibility** (10), p.18: the prefix `P_t` is eligible for agent `i` if `x_ig ≥ p_i/k_i` for all
`g ∈ L_i ∖ P_t` (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
def IsEligible {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) (t : ℕ) : Prop :=
  ∀ g ∈ low α v i \ prefixP v t, pDef α v i / (kDef α v i : ℝ) ≤ xRule v i g

/-- **The cost** (11), p.18: `|P_t ∖ H_i| + ⌈ρ(P_t)⌉` (arXiv:2609.35670, version of 2026-11-03, sha256
4e68de70…). -/
noncomputable def cost {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) (t : ℕ) : ℤ :=
  (#(prefixP v t \ high α v i) : ℤ) + ⌈rho α v (prefixP v t)⌉

/-- `t ∈ {0, …, m}` minimizes the cost among the eligible prefixes (Definition 3.14, p.18 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
def IsMinimizer {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) (t : ℕ) : Prop :=
  t ≤ m ∧ IsEligible α v i t ∧ ∀ t' ≤ m, IsEligible α v i t' → cost α v i t ≤ cost α v i t'

/-- **`ℓ_i`** (Definition 3.14, p.18): the smallest `t` minimizing the cost among eligible prefixes.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 3.14, p.18.

**Formalization Note.** `sInf` on `ℕ` is the least element of a nonempty set. The set is never empty:
`P_m = M` is eligible, as the page notes, and `{0, …, m}` is finite. -/
noncomputable def ell {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : ℕ :=
  sInf {t | IsMinimizer α v i t}

/-- **The comparison set** `Q_i = P_{ℓ_i}` (Definition 3.14, p.18 of arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…). -/
noncomputable def compSet {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : Finset (Fin m) :=
  prefixP v (ell α v i)

/-- **`d_i`, the cost of the comparison set** (Definition 3.14, p.18 of arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…). -/
noncomputable def dCost {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : ℤ :=
  cost α v i (ell α v i)

end TIEMaximin


