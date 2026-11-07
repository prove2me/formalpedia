-- Prove2me | Definitions.Def_DoublingMST_IsAlg1Output
-- name    : DoublingMST_IsAlg1Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:58.539885+00:00
-- url     : https://prove2.me/theorems/c441f417-c7f0-4961-9a7b-77721ed15b59
-- title:
--   Output $\Psi$ of Algorithm 1
-- statement:
--   $\Psi$ is an **output of Algorithm 1** with parameter $t$ if some run of $\mathrm{WSPC}(r,r)$ with no marks, where $r$ is the root (the single point of $N_L$, at level $L$), returns $\Psi$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_DoublingMST_WSPCSteps

namespace DoublingMST

/-- **An output Ψ of Algorithm 1.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §3, p.14 (PDF p.16): "To construct a t-WSPC, we call Algorithm 1 with WSPC(r, r) and
parameter t, where r is the “root” of the net hierarchy (i.e., the only net point in N_L). It
returns a collection Ψ of pairs of net points".

`IsAlg1Output H t Ψ`: some run of `WSPC(r, r)` with parameter `t`, from no marks, where
`r = (root, L)`, returns `Ψ`. -/
def IsAlg1Output {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (t : ℝ)
    (Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ))) : Prop :=
  ∃ r ∈ H.N (topLevel d), ∃ m', WSPCSteps H t ∅ [((r, topLevel d), (r, topLevel d))] m' Ψ

end DoublingMST


