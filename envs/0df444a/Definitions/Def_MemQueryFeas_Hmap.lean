-- Prove2me | Definitions.Def_MemQueryFeas_Hmap
-- name    : MemQueryFeas_Hmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:22.116795+00:00
-- url     : https://prove2.me/theorems/4a62e526-041c-4cc6-8741-311fbf7b7ce9
-- title:
--   The adjoint transform $H_v=T_v^{-\top}$
-- statement:
--   $H_v=T_v^{-\top}$, the adjoint of the inverse of $T_v$. It acts on subspaces: $T_v(E^\perp)=(H_v(E))^\perp$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 2, line 6, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MemQueryFeas_Tmap

namespace MemQueryFeas

/-- **The adjoint transform `H_v := T_v^{−⊤}`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1 and Algorithm 2, line 6, p.8 (PDF p.9):
"`H_v := T_v^{−⊤}`. Here, we introduce the adjoint transform `H_v` which intuitively applies to the
subspaces `E`".

**Formalization Note.** `T^{−⊤}` is the adjoint of the inverse (`Ring.inverse`, which is the inverse
of the invertible `T_v`: every stretch with a nonzero factor is invertible). -/
noncomputable def Hmap {d : ℕ} (δ : ℕ → ℕ → ℝ) (c : ℕ → List ℕ → ℕ → Op d) (v : List ℕ) :
    Op d :=
  ContinuousLinearMap.adjoint (Ring.inverse (Tmap δ c v))

end MemQueryFeas


