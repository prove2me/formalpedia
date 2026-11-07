-- Prove2me | Definitions.Def_CritWinSpin_Wpot
-- name    : CritWinSpin_Wpot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:33.492812+00:00
-- url     : https://prove2.me/theorems/d2f3c282-f057-43b1-873c-71cbc06290d0
-- title:
--   Potentials $V$, $W$, $U_\alpha$, the envelope $g_s$, the kernel $K_z$
-- statement:
--   For $s>\tau$ put $f_s(t)=t^2/(2s)-\phi(t)$, let $a_s>0$ be the solution of $a_s=s\phi'(a_s)$, and let $g_s(t)=f_s(a_s)$ for $|t|\le a_s$ and $g_s(t)=f_s(t)$ otherwise. Further $d_s=f_s-g_s$, $\phi_s=\phi+d_s=t^2/(2s)-g_s$, and $\Delta_s=\sup_{|m|\le1}\{\frac s2m^2-I(m)\}$. For a matrix $L$ and a field $h$, define on $\mathbb R^N$
--   $$V(z)=\tfrac12\|z\|^2-\sum_i\phi((Lz)_i+h_i),\quad W(z)=\tfrac12\|z\|^2-\sum_i\phi_s((Lz)_i+h_i),\quad U_\alpha=W+\tfrac\alpha2\|z\|^2,$$
--   and $P(x\mid z)=\prod_i\rho_{(Lz)_i+h_i}(x_i)$. The kernel $K_z$ on $A^N\cup\{\bot\}$ draws $X\sim P(\cdot\mid z)$ with probability $e^{-(V(z)-W(z))}$ and outputs $\bot$ otherwise.
--
--   **Formalization Note** $a_s$ is written as the supremum of the solution set, which Lemma 4.2 proves is a singleton for $s>\tau$. The index type of $\Delta_s$ is nonempty and the family is bounded above.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §4.1, pp.13–14, eqs. (19), (20), (22); §4.2, p.15

import Mathlib
import Definitions.Def_CritWinSpin_gibbs
set_option autoImplicit false

namespace CritWinSpin

/-- `f_s(t) = t²/(2s) − ϕ(t)` (p.14). -/
noncomputable def fs (S : SpinLaw) (s t : ℝ) : ℝ := t ^ 2 / (2 * s) - phi S t

/-- `a_s`: the positive solution of `a_s = s ϕ'(a_s)` (p.14).

**Formalization Note.** Written as a supremum of the solution set; Lemma 4.2 states that the set
is a singleton when `s > τ`, so this is that solution and never the junk value of an empty set. -/
noncomputable def asOf (S : SpinLaw) (s : ℝ) : ℝ :=
  sSup {a : ℝ | 0 < a ∧ a = s * deriv (phi S) a}

/-- The convex envelope `g_s`: `f_s(a_s)` on `|t| ≤ a_s`, and `f_s(t)` otherwise (p.14). -/
noncomputable def gs (S : SpinLaw) (s t : ℝ) : ℝ :=
  if |t| ≤ asOf S s then fs S s (asOf S s) else fs S s t

/-- The discrepancy `d_s = f_s − g_s` (p.14). -/
noncomputable def ds (S : SpinLaw) (s t : ℝ) : ℝ := fs S s t - gs S s t

/-- The modified scalar potential `ϕ_s = ϕ + d_s = t²/(2s) − g_s` (p.14). -/
noncomputable def phis (S : SpinLaw) (s t : ℝ) : ℝ := t ^ 2 / (2 * s) - gs S s t

/-- `Δ_s = sup_{|m|≤1} {(s/2) m² − I(m)}`, eq. (22), p.14.

**Formalization Note.** The index type is nonempty and, since `I ≥ 0` on `[−1, 1]`, the family is
bounded above by `s/2`, so the real `⨆` is the true supremum. -/
noncomputable def deltaS (S : SpinLaw) (s : ℝ) : ℝ :=
  ⨆ m : {m : ℝ // |m| ≤ 1}, (s / 2) * (m : ℝ) ^ 2 - rateI S m

/-- The squared Euclidean norm `‖z‖²`. -/
noncomputable def normSq {N : ℕ} (z : Fin N → ℝ) : ℝ := ∑ i, z i ^ 2

/-- `V(z) = ½‖z‖² − ∑_i ϕ((Lz)_i + h_i)`, eq. (19), p.13. -/
noncomputable def hsV (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ) : ℝ :=
  (1 / 2) * normSq z - ∑ i, phi S (L.mulVec z i + h i)

/-- `P(x | z) = ∏_i ρ_{(Lz)_i + h_i}(x_i)`, eq. (19), p.13. -/
noncomputable def condP (S : SpinLaw) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ)
    (x : Config S (Fin N)) : ℝ :=
  ∏ i, tilt S (L.mulVec z i + h i) (x i : ℚ)

/-- **The convexified potential** `W(z) = ½‖z‖² − ∑_i ϕ_s((Lz)_i + h_i)`, eq. (20), p.14
(Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…). -/
noncomputable def Wpot (S : SpinLaw) (s : ℝ) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (h z : Fin N → ℝ) : ℝ :=
  (1 / 2) * normSq z - ∑ i, phis S s (L.mulVec z i + h i)

/-- The regularised potential `U_α = W + (α/2)‖z‖²`, p.15. -/
noncomputable def Ualpha (S : SpinLaw) (s α : ℝ) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (h z : Fin N → ℝ) : ℝ :=
  Wpot S s L h z + (α / 2) * normSq z

/-- The normalised density `e^{−U(z)} / ∫ e^{−U}` on `ℝ^N` of a potential `U`, p.15. -/
noncomputable def normDens {N : ℕ} (U : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) : ℝ :=
  Real.exp (-U z) / ∫ w, Real.exp (-U w)

/-- The kernel `K_z` on `A^N ∪ {⊥}`, p.15: draw `X ∼ P(· | z)` with probability
`e^{−(V(z)−W(z))}` and output `⊥` otherwise. -/
noncomputable def kernelK (S : SpinLaw) (s : ℝ) {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ)
    (h z : Fin N → ℝ) : Option (Config S (Fin N)) → ℝ
  | none => 1 - Real.exp (-(hsV S L h z - Wpot S s L h z))
  | some x => Real.exp (-(hsV S L h z - Wpot S s L h z)) * condP S L h z x

end CritWinSpin


