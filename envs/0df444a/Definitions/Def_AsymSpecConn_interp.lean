-- Prove2me | Definitions.Def_AsymSpecConn_interp
-- name    : AsymSpecConn_interp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:55.397768+00:00
-- url     : https://prove2.me/theorems/fa67245c-3a6b-43d9-bf10-9c7de4ce0909
-- title:
--   Interpolation $F_t^{f_0}$ between spectral points
-- statement:
--   Fix $f_1\in\Delta$. For $f_0\in\Delta$ and $t\in[0,1]$, let $w_t(s)=f_0(s)^{1-t}f_1(s)^t$ be the geometric average of $f_0$ and $f_1$, and let
--   $$F_t=F_t^{f_0}=F_{w_t}.$$
--   This is the family of functions that the path-connectedness results show to be a path of spectral points from $f_0$ to $f_1$.
--
--   **Formalization Note** The value lies in $[0,\infty]$, like $F_w$. The parameter $t$ is a real number, used for $t\in[0,1]$.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §2.4, p.17

import Mathlib
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_Fw

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn

/-- **Interpolation** `F_t = F_t^{f₀} := F_{w_t}` (§2.4, p.17 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)), where
`w_t(s) := f₀(s)^{1−t} f₁(s)^t` is the geometric average of the spectral points `f₀, f₁`.

**Formalization Note** Valued in `ℝ≥0∞` like `Fw`; `t` is a real number (used for
`t ∈ [0, 1]`). -/
noncomputable def interp {S : Type*} [CommSemiring S] (P : Preorder S) (A : Set S)
    (f₀ f₁ : ↥(Spectrum S P)) (t : ℝ) (s : S) : ℝ≥0∞ :=
  Fw P A (fun x => (f₀.1 x) ^ (1 - t) * (f₁.1 x) ^ t) s

end AsymSpecConn


