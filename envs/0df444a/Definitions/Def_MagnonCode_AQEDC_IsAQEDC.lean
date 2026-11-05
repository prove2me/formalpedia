-- Prove2me | Definitions.Def_MagnonCode_AQEDC_IsAQEDC
-- name    : MagnonCode_AQEDC_IsAQEDC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:11.169315+00:00
-- url     : https://prove2.me/theorems/27b1c81e-468f-42d6-ab0b-8a62a1a49847
-- title:
--   Definition 3.3: $(\epsilon,\delta)[[n,k,d]]$-AQEDC
-- statement:
--   An **$(\epsilon,\delta)[[n,k,d]]$-AQEDC** (approximate quantum error-detecting code) is a $p^k$-dimensional subspace of $(\mathbb C^p)^{\otimes n}$ that is an $(\epsilon,\delta)$-error-detecting code for every CPTP map of the form $\mathcal N(\rho)=\sum_jp_jF_j\rho F_j^\dagger$ with each $F_j$ $d$-local and $\|F_j\|\le1$.
--
--   **Formalization Note** The subspace is represented by its orthogonal projector $P$ (Hermitian and idempotent), and its dimension is the rank of $P$. The number $k$ is real, because Theorem 7.9 has $k=\kappa\log_2n$; the dimension condition is the real equation $\operatorname{rank}P=p^k$.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Definition 3.3, p. 12

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting
import Definitions.Def_MagnonCode_AQEDC_IsDetecting
import Definitions.Def_MagnonCode_AQEDC_IsMixtureChannel

namespace MagnonCode.AQEDC

/-- **Definition 3.3** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 12): an `(ε, δ)[[n, k, d]]`-AQEDC is a `p^k`-dimensional subspace
of `(ℂ^p)^{⊗n}` that is an `(ε, δ)`-error-detecting code for every CPTP map of the form (7).

**Formalization Note** The subspace is given by its projector `P` (Definition 3.1, "with associated
projection `P`"), so its dimension is the rank of `P`. `k` is real, because Theorem 7.9 has
`k = κ log₂ n`; the dimension clause is an equation between reals. -/
def IsAQEDC (p n : ℕ) (k : ℝ) (d : ℕ) (ε δ : ℝ)
    (P : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ) : Prop :=
  EastinKnill.Transversal.IsCodeProjector P ∧ (P.rank : ℝ) = (p : ℝ) ^ k ∧
    ∀ N, IsMixtureChannel d N → IsDetecting ε δ P N

end MagnonCode.AQEDC


