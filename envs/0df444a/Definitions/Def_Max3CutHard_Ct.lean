-- Prove2me | Definitions.Def_Max3CutHard_Ct
-- name    : Max3CutHard_Ct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:05.914658+00:00
-- url     : https://prove2.me/theorems/871f67d0-62eb-4dd5-ba17-a0a2876de750
-- title:
--   Completeness $C_t$ of the gadget $I_t$
-- statement:
--   Let $k\ge3$ and let $y^\circ=(0,1,\dots,k-1)$ be the canonical colouring of the globals. The **completeness** of the gadget $I_t$ of a family is
--
--   $$C_t=\min\{V_t(x,y^\circ):\ x\in\mathrm{sat}_t\},$$
--
--   where the colours $0,1,2$ of $x$ are read as colours in $[k]$.
--
--   It is the value each satisfied equation contributes in the completeness analysis (1).
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Gadgets, p.5

import Mathlib
import Definitions.Def_Max3CutHard_sat
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_Gadget_gval

namespace Max3CutHard

/-- **Completeness `C_t` of the gadget `I_t`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Gadgets, p.5: "they use only the
colours 0, 1, 2. The completeness of `I_t` is `C_t = min{V_t(x, y°) : x ∈ sat_t}`", with
"`y° = (0, 1, …, k − 1)` the canonical colouring of the globals".

**Formalization Note.** `y°` is `id : Fin k → Fin k`; the colours `0, 1, 2` of `x ∈ ℤ₃^3` are
embedded into `Fin k` by `Fin.castLE hk` (`ℤ₃ = Fin 3`, `3 ≤ k`). -/
noncomputable def Ct {k : ℕ} [NeZero k] (hk : 3 ≤ k) (F : Family k) (t : ZMod 3) : ℝ :=
  (sat t).inf' (sat_nonempty t) fun x => (F t).gval (fun j => Fin.castLE hk (x j)) id

end Max3CutHard


