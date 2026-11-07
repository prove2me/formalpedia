-- Prove2me | Definitions.Def_MinSumClust_IsSplittable
-- name    : MinSumClust_IsSplittable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:15.829305+00:00
-- url     : https://prove2.me/theorems/51a8938e-a9d8-4a34-9c12-9440202e6191
-- title:
--   Definition 4: $\gamma$-splittable clusters
-- statement:
--   Fix a distance $d$, a vector $(\alpha_i)_{i\in D}$ (a dual solution) and the opening cost $f$. A pair of sets $\langle C_{\mathrm{core}},C_{\mathrm{out}}\rangle$ is **$\gamma$-splittable** if
--
--   1. $C_{\mathrm{core}}\ne\emptyset$ and $C_{\mathrm{core}}\cap C_{\mathrm{out}}=\emptyset$;
--   2. $\sum_{i\in C_{\mathrm{core}}}\alpha_i\ge f+\mathrm{cost}(C_{\mathrm{core}})$;
--   3. for each $i\in C_{\mathrm{out}}$: $\alpha_i\ge\gamma\sum_{j\in C_{\mathrm{core}}}d(i,j)$ and $\alpha_i\ge\max_{j\in C_{\mathrm{core}}}\alpha_j$.
--
--   The core pays for itself (the dual payment property), and every outer client can pay $\gamma$ times its connection to the core. Lemma 5 splits such a cluster into parts that each pay for themselves.
--
--   **Formalization Note** The maximum is written as $\alpha_j\le\alpha_i$ for every $j\in C_{\mathrm{core}}$; $\alpha$ is any real vector (§3: "any dual solution").
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Definition 4, pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_MinSumClust_cost

namespace MinSumClust

/-- **Definition 4 (γ-splittable clusters)**, pp.16–17.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Definition 4, pp.16–17 (PDF pp.18–19).

`⟨C_core, C_out⟩` is γ-splittable with respect to the dual solution `α` and the opening cost `f` if
1. `C_core ≠ ∅` and `C_core ∩ C_out = ∅`;
2. `∑_{i ∈ C_core} α_i ≥ f + cost(C_core)`;
3. for each `i ∈ C_out`: `α_i ≥ γ ∑_{j ∈ C_core} d(i, j)` and `α_i ≥ max_{j ∈ C_core} α_j`.

**Formalization Note.** "Dual solution" is any real vector `α` (§3, p.16: "any dual solution");
`max_{j ∈ C_core} α_j ≤ α_i` is written as `α_j ≤ α_i` for every `j ∈ C_core`. -/
def IsSplittable {D : Type*} (d : D → D → ℝ) (α : D → ℝ) (f γ : ℝ)
    (Ccore Cout : Finset D) : Prop :=
  Ccore.Nonempty ∧ Disjoint Ccore Cout ∧
    f + cost d Ccore ≤ ∑ i ∈ Ccore, α i ∧
    ∀ i ∈ Cout, γ * dist1 d i Ccore ≤ α i ∧ ∀ j ∈ Ccore, α j ≤ α i

end MinSumClust


