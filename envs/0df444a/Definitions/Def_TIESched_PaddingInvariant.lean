-- Prove2me | Definitions.Def_TIESched_PaddingInvariant
-- name    : TIESched_PaddingInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:41.302971+00:00
-- url     : https://prove2.me/theorems/8046efea-916e-4ce6-adb9-1d296cf3c3c3
-- title:
--   Padding-appending operations $T_v$ and padding invariance
-- statement:
--   A **padding job** is a column $v\in\mathbb R^m_{\ge0}$ with $\min_i v_i=0$. For a report $p$ on $S$ and a fresh label $k\notin S$, $p\oplus v$ is the report on $S\cup\{k\}$ that agrees with $p$ on $S$ and has column $v$ at $k$. The padding-appending operation $T_v$ runs the mechanism on the enlarged instance and keeps the jobs of $S$:
--   $$[T_v(x)]^S_{ij}(p)=x^{S\cup\{k\}}_{ij}(p\oplus v),\qquad [T_v(u)]^S_i(p)=u^{S\cup\{k\}}_i(p\oplus v)-u^{S\cup\{k\}}_i(p^{i,0}\oplus v),$$
--   where $p^{i,0}$ sets machine $i$'s row to zero. A family is **padding-invariant** if $T_v(x)=x$ and $T_v(u)=u$ for every padding job $v$.
--
--   Padding invariance yields the zero boundary condition of the utility interactions (Lemma 5.7).
--
--   **Formalization Note.** The identities are required on nonnegative reports and for every fresh label $k\notin S$ (the paper chooses one fresh label per job set; for the relabeling-equivariant families it constructs, the choice is immaterial, p.24). $\min_i v_i=0$ for $v\ge0$ is written as "some $v_i=0$".
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §5.2, pp.21–23

import Mathlib
import Definitions.Def_TIESched_FracMech

set_option autoImplicit false

namespace TIESched

/-- **Appending a padding job** `p ⊕ v` (arXiv:2611.05142, §5.2, p.22): for a report `p` on `S` and a
fresh label `k ∉ S`, the report on `S ∪ {k}` that agrees with `p` on the jobs of `S` and has the
additional column `(p ⊕ v)_ik = v_i`.

**Formalization Note.** The new job set is `insert k S`; a job of `insert k S` that is not in `S`
gets the column `v` (when `k ∉ S` this is exactly job `k`). -/
def pad {m : ℕ} {S : Finset ℕ} (k : ℕ) (p : Fin m → S → ℝ) (v : Fin m → ℝ) :
    Fin m → ↥(insert k S) → ℝ :=
  fun i j => if h : (j : ℕ) ∈ S then p i ⟨j, h⟩ else v i

/-- **Padding invariance** (arXiv:2611.05142, §5.2, pp.21–23, Lemma 5.6): the family is unchanged by
every padding-appending operation `T_v`, i.e. `T_v(x) = x` and `T_v(u) = u` for every padding job
`v ∈ ℝ^m_{≥0}` with `min_i v_i = 0`, where (p.22)
`[T_v(x)]^S_ij(p) = x^{S∪{k}}_ij(p ⊕ v)` and
`[T_v(u)]^S_i(p) = u^{S∪{k}}_i(p ⊕ v) − u^{S∪{k}}_i(p^{i,0} ⊕ v)`,
`u` the normalized utility and `p^{i,0}` the report with machine `i`'s row set to zero.

**Formalization Note.** The identities are required on nonnegative reports (the domain of the
mechanism) and for **every** fresh label `k ∉ S`; the paper fixes one fresh label per job set, and
for the relabeling-equivariant families of Lemma 5.6 the choice is immaterial (p.24).
`min_i v_i = 0` for `v ≥ 0` is written `∃ i, v i = 0`. -/
def PaddingInvariant {m : ℕ} (M : FracMech m) : Prop :=
  ∀ (v : Fin m → ℝ), (∀ i, 0 ≤ v i) → (∃ i, v i = 0) →
    ∀ (S : Finset ℕ) (k : ℕ), k ∉ S → ∀ (p : Fin m → S → ℝ), IsNonneg p →
      (∀ (i : Fin m) (j : S),
          M.alloc (insert k S) (pad k p v) i ⟨j, Finset.mem_insert_of_mem j.2⟩ = M.alloc S p i j) ∧
      ∀ i : Fin m,
        normalizedUtility M (insert k S) (pad k p v) i -
            normalizedUtility M (insert k S) (pad k (Function.update p i 0) v) i =
          normalizedUtility M S p i

end TIESched


