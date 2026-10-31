-- Prove2me | Definitions.Def_MultiServerAppt_Ublock
-- name    : MultiServerAppt_Ublock
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:00.801286+00:00
-- url     : https://prove2.me/theorems/599d4837-e0ae-475a-8a68-c540189be0d8
-- title:
--   The exit block $U^{(\ell+1)}$, Eq. (10)
-- statement:
--   Let $t=-S\mathbf 1$ be the exit-rate vector of $S$. The block $U^{(\ell+1)}$ goes from the phase vectors $m$ of $\ell+1$ busy servers to the phase vectors $m'$ of $\ell$ busy servers:
--
--   $$U^{(\ell+1)}_{m,m'}=\sum_{c=1}^{\ell+1} t_{m_c}\ \mathbf 1\{m' = m \text{ with coordinate } c \text{ removed}\}.$$
--
--   It describes a service completion when no client waits: one server becomes idle and the others keep their phases.
--
--   **Formalization Note** The index is shifted, so `Ublock S ℓ` is the page's $U^{(\ell+1)}$ and no natural-number subtraction occurs. The page's recursion (10) and $U^{(1)}=-S\mathbf 1$ are proved in the verification file.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (10), p.12

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MultiServerAppt

/-- The exit block `U^(ℓ+1)`: with `ℓ + 1` busy servers and no client waiting, the server `c` in
phase `m c` completes at rate `t (m c)`, where `t = -S𝟙`, and the remaining `ℓ` servers keep their
phases. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (10), p.12.

**Formalization Note** The index is shifted: `Ublock S ℓ` is the page's `U^(ℓ+1)`, which maps
`Fin (ℓ+1) → ι` to `Fin ℓ → ι`, so no truncated subtraction occurs. Entrywise; the page's recursion
is proved in `Solutions/verification/MultiServerAppt_Sanity.lean`, as is `U^(1) = -S𝟙`. -/
def Ublock {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (ℓ : ℕ) :
    Matrix (Fin (ℓ + 1) → ι) (Fin ℓ → ι) ℝ :=
  Matrix.of fun m m' =>
    ∑ c : Fin (ℓ + 1),
      if (fun d => m (c.succAbove d)) = m' then MatrixAnalytic.PH.exitRates S (m c) else 0

end MultiServerAppt


