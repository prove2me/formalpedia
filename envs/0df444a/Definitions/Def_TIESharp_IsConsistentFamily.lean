-- Prove2me | Definitions.Def_TIESharp_IsConsistentFamily
-- name    : TIESharp_IsConsistentFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:08.34987+00:00
-- url     : https://prove2.me/theorems/5eabbf12-5829-447f-a6c5-4f7c1b999b38
-- title:
--   Consistency under adding free jobs (the properties of Lemma 4.2)
-- statement:
--   Call a column **free** if at least one of its entries is zero. A family is **consistent** if it is invariant under job and machine relabeling and, whenever column $j$ of a nonnegative profile $t$ with $m+1$ jobs is free:
--   1. job $j$ is assigned only to zero-cost machines: $q^{m+1}_{ij}(t)=0$ whenever $t_{ij}>0$;
--   2. deleting it preserves the entire retained assignment distribution: for every assignment $A'$ of the other $m$ jobs, $y^m_{A'}(t_{-j})=\sum_{A:\,A|_{[m+1]\setminus\{j\}}=A'}y^{m+1}_A(t)$;
--   3. deleting it preserves the normalized expected payments: $\bar p^m_i(t_{-j})=\bar p^{m+1}_i(t)$ for every machine $i$.
--
--   These are exactly the properties of the replacement family produced by Lemma 4.2, and the hypotheses on the family in Lemma 4.3.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.2, p.14

import Mathlib
import Definitions.Def_TIESharp_IsMachineEquivariant
import Definitions.Def_TIESharp_IsJobEquivariant
import Definitions.Def_TIESharp_deleteJob
import Definitions.Def_TIESharp_marg
import Definitions.Def_TIESharp_pbar

set_option autoImplicit false

namespace TIESharp

/-- The **consistency properties of Lemma 4.2** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 4.2, p.14): the family is invariant under job and machine
relabeling, and whenever a column `j` of a nonnegative profile has a zero entry ("free column"),
1. job `j` is assigned only to zero-cost machines: `q_ij = 0` whenever `t_ij > 0`;
2. deleting it preserves the entire retained assignment distribution: the law of
   `A ∘ j.succAbove` under `y^{m+1}(t)` is `y^m` at the profile without column `j`;
3. deleting it preserves the normalized expected payments `p̄`.

**Formalization Note.** Profiles with a free column have `m + 1` jobs; the retained jobs are
`Fin m` via `j.succAbove` (`deleteJob`). Clause 2 is an identity of weight functions on all
assignments `Fin m → Fin n`. -/
def IsConsistentFamily {n : ℕ} (F : Family n) : Prop :=
  IsJobEquivariant F ∧ IsMachineEquivariant F ∧
    ∀ (m : ℕ) (b : Fin n → Fin (m + 1) → ℝ) (j : Fin (m + 1)), Nonneg b → (∃ i, b i j = 0) →
      (∀ i, 0 < b i j → marg F (m + 1) b i j = 0) ∧
      (∀ A' : Fin m → Fin n, F.alloc m (deleteJob j b) A' =
        ∑ A ∈ Finset.univ.filter (fun A : Fin (m + 1) → Fin n => A ∘ j.succAbove = A'),
          F.alloc (m + 1) b A) ∧
      (∀ i, pbar F m (deleteJob j b) i = pbar F (m + 1) b i)

end TIESharp


