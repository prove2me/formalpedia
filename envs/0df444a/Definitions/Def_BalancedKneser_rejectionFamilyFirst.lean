-- Prove2me | Definitions.Def_BalancedKneser_rejectionFamilyFirst
-- name    : BalancedKneser_rejectionFamilyFirst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:54.209381+00:00
-- url     : https://prove2.me/theorems/bffc8115-9cde-4754-b055-4e8415b99129
-- title:
--   Rejection family of an agent in the first or the second group
-- statement:
--   Fix goods $[N]$ and consider the allocations in which the first group receives a $k$-set $A$ (for $N=2n$, $k=n$: the balanced allocations) and the second group receives $A^c$. For an agent with valuation $u$ and allowance $c$:
--
--   1. if she belongs to the **first group**, her rejection family is the set of $k$-sets $A$ such that she rejects $A$ as EF$c$ against $A^c$;
--   2. if she belongs to the **second group**, her rejection family is the set of $k$-sets $A$ such that she rejects $A^c$ as EF$c$ against $A$.
--
--   Lemma 2.2 identifies the rejection families of monotone agents with the independent sets of $G_{n,c+1}$.
--
--   **Formalization Note** The families are sets of vertices of $KG(N,k,r)$, i.e. subsets of the subtype of $k$-subsets of $\mathrm{Fin}\,N$. The module defines both `rejectionFamilyFirst` and `rejectionFamilySecond`.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §2, Lemma 2.2 and its proof, p.4 (PDF p.6): rejection family

import Mathlib
import Definitions.Def_BalancedKneser_AcceptsEF
import Definitions.Def_BalancedKneser_KG

namespace BalancedKneser

/-- **Rejection family of a first-group agent** (Alipour–Jafari, arXiv:2611.04486v1, §2,
Lemma 2.2 and its proof, p.4 (PDF p.6)). With goods `[N]` and balanced allocations given by the
`k`-set `A` of the first group, a first-group agent with valuation `u` receives `A` and compares
it with `Aᶜ`; her rejection family is the set of allocations she rejects as EFc. -/
def rejectionFamilyFirst {N k : ℕ} (c : ℕ) (u : Finset (Fin N) → ℝ) : Set (KSet N k) :=
  {A | ¬ AcceptsEF c u A.1 (Finset.univ \ A.1)}

/-- **Rejection family of a second-group agent** (arXiv:2611.04486v1, §2, Lemma 2.2, p.4
(PDF p.6)). A second-group agent receives `Aᶜ` and compares it with `A`. -/
def rejectionFamilySecond {N k : ℕ} (c : ℕ) (u : Finset (Fin N) → ℝ) : Set (KSet N k) :=
  {A | ¬ AcceptsEF c u (Finset.univ \ A.1) A.1}

end BalancedKneser


