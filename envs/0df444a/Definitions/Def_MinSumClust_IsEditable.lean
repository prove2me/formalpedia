-- Prove2me | Definitions.Def_MinSumClust_IsEditable
-- name    : MinSumClust_IsEditable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:26.314277+00:00
-- url     : https://prove2.me/theorems/a5b11b1f-c3e5-4628-9c52-ddb7f2c03759
-- title:
--   Definition 6: $\gamma$-editable clusters
-- statement:
--   With $d$, $\alpha$ and $f$ as in Definition 4, a quadruple $\langle C_{\mathrm{core}},C_{\mathrm{del}},C_{\mathrm{ins}},C_{\mathrm{out}}\rangle$ is **$\gamma$-editable** if
--
--   1. $\langle C_{\mathrm{core}},C_{\mathrm{out}}\rangle$ is $\gamma$-splittable;
--   2. $C_{\mathrm{del}}\subseteq C_{\mathrm{core}}$, and $C_{\mathrm{core}}$, $C_{\mathrm{ins}}$, $C_{\mathrm{out}}$ are pairwise disjoint;
--   3. $|C_{\mathrm{ins}}|\le 2|C_{\mathrm{core}}|$ and $\sum_{i\in C_{\mathrm{ins}}}\alpha_i\ge 2\sum_{j\in C_{\mathrm{del}}}\alpha_j$;
--   4. for each $i\in C_{\mathrm{ins}}$: $\alpha_i\ge\gamma\, d(i,C_{\mathrm{core}})$.
--
--   Editing deletes some core clients and inserts others with weaker conditions than outer clients; Lemma 7 shows the edited cluster still splits into self-paying parts. Lemma 16 produces such clusters from Algorithm 3.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Definition 6, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsSplittable

namespace MinSumClust

/-- **Definition 6 (γ-editable clusters)**, p.18.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Definition 6, p.18 (PDF p.20).

`⟨C_core, C_del, C_ins, C_out⟩` is γ-editable with respect to `α` and `f` if
1. `⟨C_core, C_out⟩` is γ-splittable;
2. `C_del ⊆ C_core`, and `C_core`, `C_ins`, `C_out` are pairwise disjoint;
3. `|C_ins| ≤ 2|C_core|` and `∑_{i ∈ C_ins} α_i ≥ 2 ∑_{j ∈ C_del} α_j`;
4. for each `i ∈ C_ins`: `α_i ≥ γ · d(i, C_core)`. -/
def IsEditable {D : Type*} (d : D → D → ℝ) (α : D → ℝ) (f γ : ℝ)
    (Ccore Cdel Cins Cout : Finset D) : Prop :=
  IsSplittable d α f γ Ccore Cout ∧
    Cdel ⊆ Ccore ∧ Disjoint Ccore Cins ∧ Disjoint Ccore Cout ∧ Disjoint Cins Cout ∧
    Cins.card ≤ 2 * Ccore.card ∧ 2 * ∑ j ∈ Cdel, α j ≤ ∑ i ∈ Cins, α i ∧
    ∀ i ∈ Cins, γ * dist1 d i Ccore ≤ α i

end MinSumClust


