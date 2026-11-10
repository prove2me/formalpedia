-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Potential
-- name    : DecrAlmostLinearSSSP_Decremental_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:51:27.861323+00:00
-- url     : https://prove2.me/theorems/b0796a30-d03b-496b-a4a6-5ff9d80598be
-- title:
--   Clipped logarithmic potential, capacities and signed gradients
-- statement:
--   For any real label vector $p$ and current normalized costs $c$, write $B$ for tail-minus-head incidence and define
--
--   $$\sigma_e=c_e+(Bp)_e,\qquad f_e=\frac{\mu_e}{\max(\sigma_e,\kappa)},\qquad \Psi(p)=\sum_e\mu_e\psi_\kappa(\sigma_e),$$
--
--   where $\psi_\kappa(t)=-\log t$ for $t\ge\kappa$ and $-\log\kappa+1-t/\kappa$ otherwise. The branches agree at $\kappa$. The weighted seminorm is $\|x\|_f=\sum_e f_e|(Bx)_e|$, and the vertex gradient is $g=-B^\top f$, or incoming minus outgoing capacity. Capacities are derived quantities, with no conservation assumption.
--
--   The balance predicate means $|g\cdot x|\le\|x\|_f/3$ for every source-normalized direction. The all-target conclusion means every logical slack strictly exceeds $\kappa$ and $p_v\le z_v\le(1+\epsilon/4)p_v$ for every nonsource vertex, where $z$ is normalized core distance.
--
--   The potential is defined for all real labels, including violated constraints; positivity and feasibility are never built into the label type. **Formalization Note** Extended nonnegative distances are compared with the corresponding real labels; the simultaneous strict return-slack conclusion itself gives $p_v>\kappa>0$.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 8, equations (3.8)–(3.11); p. 11, equations (3.16)–(3.17); pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Core

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Both branches agree at κ. All real slacks, including negative ones, are legal. -/
noncomputable def clippedLog (κ t : ℝ) : ℝ :=
  if κ ≤ t then -Real.log t else -Real.log κ + 1 - t / κ

noncomputable def incidence (b : Core) (x : Fin b.input.n → ℝ) (e : Edge b) : ℝ :=
  x (tail b e) - x (head b e)

noncomputable def slack (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (e : Edge b) : ℝ := cost b active e + incidence b p e

noncomputable def capacity (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (e : Edge b) : ℝ :=
  coefficient b e / max (slack b active p e) (kappa b)

noncomputable def potential (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) : ℝ :=
  ∑ e, coefficient b e * clippedLog (kappa b) (slack b active p e)

noncomputable def norm (b : Core) (f : Edge b → ℝ) (x : Fin b.input.n → ℝ) : ℝ :=
  ∑ e, f e * |incidence b x e|

noncomputable def gradient (b : Core) (f : Edge b → ℝ) (v : Fin b.input.n) : ℝ :=
  ∑ e, ((if head b e = v then f e else 0) - (if tail b e = v then f e else 0))

noncomputable def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ v, x v * y v

def Balanced (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) : Prop :=
  ∀ x : Fin b.input.n → ℝ, x b.input.source = 0 →
    |dot (gradient b (capacity b active p)) x| ≤ (1 / 3 : ℝ) * norm b (capacity b active p) x

def AllTarget (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) : Prop :=
  (∀ e, kappa b < slack b active p e) ∧
  ∀ v, v ≠ b.input.source →
    ENNReal.ofReal (p v) ≤ coreDistance b active v ∧
    coreDistance b active v ≤ ENNReal.ofReal ((1 + b.input.accuracy / 4) * p v)

end DecrAlmostLinearSSSP.Decremental


