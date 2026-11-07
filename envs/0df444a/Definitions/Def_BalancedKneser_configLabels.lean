-- Prove2me | Definitions.Def_BalancedKneser_configLabels
-- name    : BalancedKneser_configLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:02.28377+00:00
-- url     : https://prove2.me/theorems/4a3c9442-0cfd-458f-9d57-d1d6f4763947
-- title:
--   Labels of a configuration placed in $[N]$: $I\cup e(A_i)$ and their complements
-- statement:
--   A small configuration on the point set $[q]$ is given by its labels $A_1,\dots,A_q\subseteq[q]$. To place it in $[N]$, choose an injection $e:[q]\hookrightarrow[N]$ (its image $D$ is a $q$-point set) and a core $I\subseteq[N]$. The **configuration labels** are the sets
--   $$
--   I\cup e(A_i)\qquad(1\le i\le q),
--   $$
--   and the **complemented configuration labels** are their complements $[N]\setminus\big(I\cup e(A_i)\big)$. Each is recorded as the family of those sets that are $k$-sets, a set of vertices of $KG(N,k,r)$ or $C_c(N,k)$. When $I$ is disjoint from $D$ and $|I|+|A_i|=k$, this family consists of exactly the $q$ labels.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8); §4.1, p.8 (PDF p.10); §9.2, p.18 (PDF p.20): configurations I ∪ Aᵢ and complements

import Mathlib
import Definitions.Def_BalancedKneser_KG

namespace BalancedKneser

/-- **Configuration labels** (Alipour–Jafari, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8); §4.1,
p.8 (PDF p.10); §9.2, p.18 (PDF p.20)). A small configuration on `[q]` is given by its labels
`Aᵢ ⊆ [q]` (`base i`). It is placed in `[N]` by an injection `e : [q] ↪ [N]` (whose image is the
`q`-point set `D`) and a core `I ⊆ [N]`; the resulting labels are the sets `I ∪ e(Aᵢ)`. This is
the set of those labels that are `k`-sets, as a family of vertices of `C_c(N, k)` or `KG(N, k, r)`.

Formalization Note: when `|I| + |Aᵢ| = k` and `I` is disjoint from `D`, all `q` labels are
`k`-sets, so the family is exactly `{I ∪ e(A₁), …, I ∪ e(A_q)}`. -/
def configLabels {q N : ℕ} (k : ℕ) (base : Fin q → Finset (Fin q)) (I : Finset (Fin N))
    (e : Fin q ↪ Fin N) : Finset (KSet N k) :=
  Finset.univ.filter (fun A => ∃ i, A.1 = I ∪ (base i).map e)

/-- **Complemented configuration labels** (arXiv:2611.04486v1, §3.2, p.6: "We also use the
cycles obtained by complementing all five n-sets"; §4.1, p.8: "Again include the complemented
configurations"): the complements `[N] ∖ (I ∪ e(Aᵢ))` of the configuration labels, as a family
of `k`-sets. -/
def configLabelsCompl {q N : ℕ} (k : ℕ) (base : Fin q → Finset (Fin q)) (I : Finset (Fin N))
    (e : Fin q ↪ Fin N) : Finset (KSet N k) :=
  Finset.univ.filter (fun A => ∃ i, A.1 = Finset.univ \ (I ∪ (base i).map e))

end BalancedKneser


