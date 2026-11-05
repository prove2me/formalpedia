-- Prove2me | Definitions.Def_MagnonCode_AQEDC_IsDLocal
-- name    : MagnonCode_AQEDC_IsDLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:09.872698+00:00
-- url     : https://prove2.me/theorems/3ef0f9f4-b060-498c-9221-24dda243cdd5
-- title:
--   $d$-local operator
-- statement:
--   An operator $F$ on $(\mathbb C^p)^{\otimes n}$ is **$d$-local** if it acts non-trivially only on a subset of $d$ of the $n$ subsystems. The paper stresses that $d$-local refers to the weight of the error only: the errors need not be geometrically local, and their support may be disconnected.
--
--   This is the class of errors a code of distance $d$ is asked to detect.
--
--   **Formalization Note** The support is required to have at most $d$ elements. Since acting on $A$ implies acting on every superset of $A$, this equals "a subset of $d$" whenever $d\le n$.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, p. 5

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_IsLocalOn

namespace MagnonCode.AQEDC

/-- **`d`-local operator** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 5): an error "of weight `d`",
acting non-trivially only on a subset of `d` of the `n` subsystems. "`d`-local only refers to the
weight of the errors": the support may be disconnected.

**Formalization Note** The support has size at most `d`, which equals "a subset of `d`" whenever
`d ≤ n`, since `IsLocalOn` is monotone in the set. For `d > n` every operator is `d`-local. -/
def IsDLocal {n p : ℕ} (d : ℕ) (F : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ) : Prop :=
  ∃ A : Finset (Fin n), A.card ≤ d ∧ IsLocalOn A F

end MagnonCode.AQEDC


