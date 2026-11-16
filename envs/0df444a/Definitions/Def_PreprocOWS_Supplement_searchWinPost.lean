-- Prove2me | Definitions.Def_PreprocOWS_Supplement_searchWinPost
-- name    : PreprocOWS_Supplement_searchWinPost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:09:39.20957+00:00
-- url     : https://prove2.me/theorems/85499d59-68eb-4147-83a2-8e74ff2e2253
-- title:
--   Search game with $T$ post-queries: $\mathbb E_k\|\Pi_k A_R O_f V|\psi_{R,k}\rangle\|^2$
-- statement:
--   For an isometry $V:\mathbb C^N\to\mathbb C^M$, a projective measurement $\{\Pi_k\}_{k\in[K]}$, query access with post-query computation $A_R = (O_RU)^T$, a phase function $f:[M]\to\{\pm1\}$ and an oracle $R$, the winning probability of the **search game with $T$ post-queries** is
--   $$
--   \mathbb E_k\,\big\|\Pi_k\,A_R\,O_f\,V\,|\psi_{R,k}\rangle\big\|^2 ,
--   $$
--   with $k$ uniform on $[K]$. Its maximum over $f$ is the $\mathrm{Win}(\mathcal A\mid R)$ of Theorem 10.1. With pre-queries (§10.3) the isometry $V$ is replaced by $V_R$.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §10.1.1, p.44 (PDF p.47); Theorem 10.1, p.43 (PDF p.46); §10.3, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_Supplement_QAccess
import Definitions.Def_PreprocOWS_Supplement_searchWin
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- The winning probability `E_k ‖Π_k A_R O_f V |ψ_{R,k}⟩‖²` of the **search game with `T`
post-queries** for a fixed phase function `f` (arXiv:2610.02101, §10.1.1, p.44, PDF p.47; Theorem
10.1, p.43); its maximum over `f` is `Win(𝒜 | R)`. With pre-queries (§10.3, p.49) `V` is `V_R`. -/
noncomputable def searchWinPost {K N M T : ℕ} (V : Matrix (Fin M) (Fin N) ℂ)
    (P : Fin K → Matrix (Fin M) (Fin M) ℂ) (Q : QAccess K N M T) (f : Fin M → Bool)
    (R : Oracle K N) : ℝ :=
  (K : ℝ)⁻¹ * ∑ k, vnormSq (P k *ᵥ (Q.postRun R *ᵥ (phaseF f *ᵥ (V *ᵥ chal R k))))

end PreprocOWS.Supplement


