-- Prove2me | Definitions.Def_MultiCollQ_Supplement_dbNorm
-- name    : MultiCollQ_Supplement_dbNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:57:44.213704+00:00
-- url     : https://prove2.me/theorems/b8246f3e-1f6a-4d20-9bc4-2770496d58b8
-- title:
--   Norm $\|\mathbf 1_S v\|$ of the database-$S$ component of a joint vector
-- statement:
--   Let $v$ be a vector (not necessarily normalized) on the tensor product of the algorithm's registers, with computational basis indexed by $c$, and the database register $\mathcal L$, whose basis states $|D\rangle$ are partial injections $D$ of $[N]$. For a set $S$ of databases, the diagonal projection $\mathbf 1_S=\sum_{D\in S}|D\rangle\langle D|$ (tensored with the identity on the algorithm's registers) gives
--
--   $$
--   \|\mathbf 1_S v\| = \Bigl(\sum_c\sum_{D\in S}|v(c,D)|^2\Bigr)^{1/2}.
--   $$
--
--   Theorem 3.2 uses it for the two boundary projections $G=\mathbf 1\{C_r=\ell-1,\ C_{r-1}\le L\}$ and $R=\mathbf 1\{C_r=\ell-1,\ C_{r-1}\ge L+1\}$, which split the databases just below the target threshold according to how many buckets hold $r-1$ recorded images. For $S=\{D: C_j(D)\ge m\}$ it is the database amplitude $\|P_{j,m}v\|$ of the base mission.
--
--   **Formalization Note** The norm is written as the sum over computational basis states, which is the norm of the diagonal projection.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 3.2, p.22 (the norms ‖Gv‖, ‖Rv‖)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm

namespace MultiCollQ.Supplement

open CompPermOracle

/-- The norm `‖1_S v‖` of the component of a joint vector `v` on (registers `C`) ⊗ (database
register `L`) whose database lies in the set `S`, where `1_S = Σ_{D ∈ S} |D⟩⟨D|` acts as the
identity on the registers `C` (Peng, Hou, Dong, *Quantum multi-collision lower bounds for arbitrary
bounded types*, manuscript (Oct. 2026), Theorem 3.2, p.22: the norms `‖Gv‖`, `‖Rv‖` of the
projections `G = 1{C_r = ℓ−1, C_{r−1} ≤ L}` and `R = 1{C_r = ℓ−1, C_{r−1} ≥ L+1}`).

**Formalization Note.** `1_S` is diagonal in the computational basis `|c, D⟩`, so
`‖1_S v‖ = (Σ_c Σ_{D ∈ S} |v(c, D)|²)^{1/2}`; this sum is the definition. The vector `v` need not be
normalized. For `S = {D : C_j(D) ≥ m}` this is `MultiCollQ.dbAmp b j m v`. -/
noncomputable def dbNorm {C : Type} [Fintype C] {N : ℕ} (S : PartialPerm N → Prop)
    (v : Hil (C × PartialPerm N)) : ℝ := by
  classical
  exact Real.sqrt (∑ c, ∑ D ∈ Finset.univ.filter S, ‖v (c, D)‖ ^ 2)

end MultiCollQ.Supplement


