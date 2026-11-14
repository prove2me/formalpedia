-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
-- name    : InfoLossLAR_Native_AFT_TotalVariation
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:20:22.567395+00:00
-- url     : https://prove2.me/theorems/dda8f643-7514-427a-9348-4c89add3665e
-- title:
--   Finite total variation as positive mass of the difference
-- statement:
--   For probability laws $p,q$ on a finite set $X$, define $$d_{\mathrm{TV}}(p,q)=\sum_{x\in X}\max\{p(x)-q(x),0\}.$$ This positive mass definition is used to connect eventwise bounds, signed masses, and stochastic output channels.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/TotalVariation.lean; migrated source SHA256 f2fa473cd4ef588e937456f46108fb43aaac4cc9dc5a5a92e9d6376391a2630c; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Definitions.Def_InfoLossLAR_Native_AFT_PositiveRepair
import Definitions.Def_InfoLossLAR_Native_AFT_TransportBound
import Mathlib



/-! Exact finite total variation and contraction by a stochastic kernel. -/

namespace AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]



namespace FiniteDist

/-- Positive mass of the difference, equal to half the `L¹` distance. -/
noncomputable def totalVariation (p q : FiniteDist α) : ℝ :=
  positiveMass (fun a => p.weight a - q.weight a)

















end FiniteDist
end AFT


