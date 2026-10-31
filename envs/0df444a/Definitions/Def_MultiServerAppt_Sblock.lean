-- Prove2me | Definitions.Def_MultiServerAppt_Sblock
-- name    : MultiServerAppt_Sblock
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:58.165039+00:00
-- url     : https://prove2.me/theorems/a9cfd4e3-4f70-43f1-aa38-f4ad31b50b6b
-- title:
--   The Kronecker-sum block $S^{(\ell)}$, Eq. (9) (corrected: $S^{(1)}=S$)
-- statement:
--   Let $S$ be the $\iota\times\iota$ service matrix and let $\ell\ge 0$. The block $S^{(\ell)}$ acts on the phase vectors $m:\{1,\dots,\ell\}\to\iota$ of $\ell$ busy servers, and
--
--   $$S^{(\ell)}_{m,m'}=\sum_{c=1}^{\ell}\ \mathbf 1\{m_d=m'_d\ \text{for all } d\ne c\}\ S_{m_c,m'_c}.$$
--
--   So exactly one server changes phase at a time. This is the Kronecker sum of $\ell$ copies of $S$, the diagonal block of the system's transition matrix.
--
--   **Formalization Note** The definition is entrywise. The page's recursion $S^{(\ell)}=I\otimes S^{(\ell-1)}+S\otimes I$ of Eq. (9) is proved in the verification file of this mission. The printed start $S^{(1)}=1$ (p.12) is a misprint and $S^{(1)}=S$ here: with $s=1$, $S=(-1)$, $\alpha=(1)$ the printed value would give $F_M(t)=1-e^{t}<0$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (9), p.12

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MultiServerAppt

/-- The diagonal block `S^(ℓ)` of the system generator: the Kronecker sum of `ℓ` copies of the
service matrix `S`, on the phase vectors `m : Fin ℓ → ι` of `ℓ` busy servers. Entrywise, phases move
one server at a time: `S^(ℓ) m m' = ∑ c, S (m c) (m' c)` over the servers `c` outside which `m` and
`m'` agree. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (9), p.12.

**Formalization Note** Defined entrywise, on a type of phase vectors. The page's recursion
`S^(ℓ) = I ⊗ S^(ℓ-1) + S ⊗ I` is proved in `Solutions/verification/MultiServerAppt_Sanity.lean`.
The printed start `S^(1) = 1` (p.12) is a misprint: `S^(1) = S` here (also proved there); with
`S = (-1)`, `α = (1)`, `s = 1` the printed value gives `F_M(t) = 1 - e^t < 0`. -/
def Sblock {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (ℓ : ℕ) :
    Matrix (Fin ℓ → ι) (Fin ℓ → ι) ℝ :=
  Matrix.of fun m m' => ∑ c, if ∀ d, d ≠ c → m d = m' d then S (m c) (m' c) else 0

end MultiServerAppt


