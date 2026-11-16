-- Prove2me | Definitions.Def_PreprocOWS_Supplement_distAdvPost
-- name    : PreprocOWS_Supplement_distAdvPost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:10:18.409309+00:00
-- url     : https://prove2.me/theorems/a76a7af4-f41e-4941-9161-b4c8be3bc383
-- title:
--   Distinguishing game with $T$ post-queries: the advantage for a fixed phase function
-- statement:
--   For an isometry $V$, a projection $\Pi$ on $\mathbb C^M$, query access with $A_R = (O_RU)^T$, a phase function $f$ and an oracle $R$, the advantage of the **distinguishing game with $T$ post-queries** is
--   $$
--   \Big|\,\mathbb E_k\|\Pi A_R O_f V|\psi_{R,k}\rangle\|^2-\mathbb E_h\|\Pi A_R O_f V|\psi_h\rangle\|^2\Big| ,
--   $$
--   with $k$ uniform on $[K]$, $h$ uniform on $\{\pm1\}^N$, and both experiments using the same $R$ for the post-queries. Its maximum over $f$ is the $\Delta_{\mathcal A}(R)$ of Theorem 10.4. With pre-queries (§10.3) $V$ is replaced by $V_R$.
--
--   **Formalization Note** For a projection, $\|\Pi v\|^2 = \langle v,\Pi v\rangle$, the quadratic form of Definition 9.4.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §10.2, p.48 (PDF p.51); §10.3, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_Supplement_QAccess
import Definitions.Def_PreprocOWS_Supplement_distAdv
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- The distinguishing advantage of the **distinguishing game with `T` post-queries** for a fixed
phase function `f` (arXiv:2610.02101, §10.2, p.48, PDF p.51):
`| E_k ‖Π A_R O_f V ψ_{R,k}‖² − E_h ‖Π A_R O_f V ψ_h‖² |`, both experiments using the same `R` for
the post-queries; its maximum over `f` is `Δ_𝒜(R)`. With pre-queries (§10.3) `V` is `V_R`.

**Formalization Note.** For the projection `Π`, `‖Π v‖² = ⟨v|Π|v⟩`, the quadratic form of
Definition 9.4. -/
noncomputable def distAdvPost {K N M T : ℕ} (V : Matrix (Fin M) (Fin N) ℂ)
    (P : Matrix (Fin M) (Fin M) ℂ) (Q : QAccess K N M T) (f : Fin M → Bool) (R : Oracle K N) : ℝ :=
  |avg (fun k : Fin K => vnormSq (P *ᵥ (Q.postRun R *ᵥ (phaseF f *ᵥ (V *ᵥ chal R k))))) -
    avg (fun h : Fin N → Bool => vnormSq (P *ᵥ (Q.postRun R *ᵥ (phaseF f *ᵥ (V *ᵥ phaseVec h)))))|

end PreprocOWS.Supplement


