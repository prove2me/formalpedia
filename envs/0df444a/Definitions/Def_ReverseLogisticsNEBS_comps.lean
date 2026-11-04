-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_comps
-- name    : ReverseLogisticsNEBS_comps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:55.553688+00:00
-- url     : https://prove2.me/theorems/e5106655-1003-44a1-8952-6adae61ca4a6
-- title:
--   Component cost functions $g, u, v, w$ of (11)–(14), components $\tilde f_{jt}$, and basestock levels
-- statement:
--   Let the terminal value be additively convex, $f_{T+1}(\omega, y) = \sum_j f_{j,T+1}(\omega, y_j)$ (Assumption 1). Going backward from $T+1$, given the next period's components $\tilde f_{j,t+1}$, define for each location $j$ and Markov state $\omega$:
--
--   $$
--   g_{jt}(\omega,Y) := c_j Y + \alpha\,\mathbb E_\omega\big[\tilde f_{j,t+1}(\omega_{t+1}, Y - D_t(\omega))\big] \quad (11)
--   $$
--   $$
--   u_{1t} := \gamma_t(\omega,Y) - c^R_1 Y + g^+_{1t}(\omega,Y),\qquad u_{jt} := -c^R_j Y + g^+_{jt}(\omega,Y) + g^-_{j-1,t}(\omega,Y)\ (j \ge 2) \quad (12)
--   $$
--   $$
--   v_{1t} := c^E_1 Y + u^+_{1t}(\omega,[Y]^-) + u^-_{1t}(\omega,Y) + u^+_{2t}(\omega,Y),\quad v_{jt} := c^E_j Y + u^-_{jt} + u^+_{j+1,t}\ (2 \le j \le N-1),\quad v_{Nt} := c^E_N Y + u^-_{Nt} \quad (13)
--   $$
--   $$
--   w_{jt} := v_{jt} + w^-_{j-1,t},\quad w_{0t} := 0, \quad (14)
--   $$
--   and the components $\tilde f_{jt}(\omega, y) := -k^E_j y + w^+_{jt}(\omega, y)$.
--
--   The basestock levels of Theorem 4 are $S^E_{jt}(\omega) := \inf\arg\min_Y w_{jt}(\omega,Y)$, $S^R_{jt}(\omega) := \sup\arg\min_Y u_{jt}(\omega,Y)$ and $S_{jt}(\omega) := \sup\arg\min_Y g_{jt}(\omega,Y)$, in the extended reals.
--
--   **Nondegeneracy** (`Model.Nondeg`) from period $t$ on means: in every period $s \in [t, T]$ the functions $g_{js}, u_{js}, w_{js}$ have finite minimizers and the expectation in (11) is finite. This is the presupposition of the $\pm$ notation on p.14.
--
--   **Formalization Note** For $N = 1$ the cases $j = 1$ and $j = N$ of (13) coincide; the definition uses $v_{11} = c^E_1 Y + u^+_{11}(\omega,[Y]^-) + u^-_{11}(\omega,Y)$, which is what minimizing over $Y^R_1 \in [[Y^E_1]^-, Y^E_1]$ produces. The recursion uses the given terminal components; moving constants between components changes the functions only by additive constants and leaves the levels unchanged.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 3, (11)–(14), pp.14–15; Theorem 4 levels, p.15; Assumption 1, p.12

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Model
import Definitions.Def_ReverseLogisticsNEBS_fPlus

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

namespace Model

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model N Ω)

/-- **(11)**, p.14: `g_jt(ω, Y) := c_j Y + α E_ω[f̃_{j,t+1}(ω_{t+1}, Y − D_t(ω))]`, where `nxt j`
is the component `f̃_{j,t+1}` of the next period's value function. -/
noncomputable def gF (t : ℕ) (nxt : Fin N → Ω → ℝ → ℝ) (j : Fin N) (ω : Ω) (Y : ℝ) : ℝ :=
  M.c j * Y + M.α * ∫ z, nxt j z.2 (Y - z.1) ∂(M.κ t ω)

/-- **(12)**, p.14: `u_1t(ω, Y) := γ_t(ω, Y) − c^R_1 Y + g^+_1t(ω, Y)` and
`u_jt(ω, Y) := −c^R_j Y + g^+_jt(ω, Y) + g^−_{j−1,t}(ω, Y)` for `j ∈ [2, N]`. -/
noncomputable def uF (t : ℕ) (nxt : Fin N → Ω → ℝ → ℝ) (j : Fin N) (ω : Ω) (Y : ℝ) : ℝ :=
  if _h : j.val = 0 then M.gamma t ω Y - M.cR j * Y + fPlus (M.gF t nxt j ω) Y
  else -M.cR j * Y + fPlus (M.gF t nxt j ω) Y +
    fMinus (M.gF t nxt ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ ω) Y

/-- **(13)**, p.14: `v_1t(ω, Y) := c^E_1 Y + u^+_1t(ω, [Y]^−) + u^−_1t(ω, Y) + u^+_2t(ω, Y)`,
`v_jt(ω, Y) := c^E_j Y + u^−_jt(ω, Y) + u^+_{j+1,t}(ω, Y)` for `j ∈ [2, N − 1]`, and
`v_Nt(ω, Y) := c^E_N Y + u^−_Nt(ω, Y)`.

**Formalization Note.** The term `u^+_1t(ω, [Y]^−)` belongs to location `1`, and `u^+_{j+1,t}` is
absent at location `N`; for `N = 1` this gives `v_11 = c^E_1 Y + u^+_11(ω, [Y]^−) + u^−_11(ω, Y)`,
which is what the minimization over `Y^R_1 ∈ [[Y^E_1]^−, Y^E_1]` produces. -/
noncomputable def vF (t : ℕ) (nxt : Fin N → Ω → ℝ → ℝ) (j : Fin N) (ω : Ω) (Y : ℝ) : ℝ :=
  M.cE j * Y + (if j.val = 0 then fPlus (M.uF t nxt j ω) (negPartMin Y) else 0) +
    fMinus (M.uF t nxt j ω) Y +
    (if h : j.val + 1 < N then fPlus (M.uF t nxt ⟨j.val + 1, h⟩ ω) Y else 0)

/-- **(14)**, p.14: `w_jt(ω, Y) := v_jt(ω, Y) + w^−_{j−1,t}(ω, Y)` with `w_0t := 0`. -/
noncomputable def wF (t : ℕ) (nxt : Fin N → Ω → ℝ → ℝ) (j : Fin N) (ω : Ω) : ℝ → ℝ :=
  karushW (fun i => M.vF t nxt i ω) j.val

/-- The component `f̃_jt(ω, y) := −k^E_j y + w^+_jt(ω, y)` of Theorem 3 (p.15), computed from the
next period's components `nxt`. -/
noncomputable def compStep (t : ℕ) (nxt : Fin N → Ω → ℝ → ℝ) (j : Fin N) (ω : Ω) (y : ℝ) : ℝ :=
  -M.kE j * y + fPlus (M.wF t nxt j ω) y

/-- Backward recursion with `k` periods to go, starting in period `t`. -/
noncomputable def compsAux (fT : Fin N → Ω → ℝ → ℝ) : ℕ → ℕ → Fin N → Ω → ℝ → ℝ
  | 0, _ => fT
  | k + 1, t => M.compStep t (compsAux fT k (t + 1))

/-- **The components `f̃_jt` of Theorem 3** (pp.14–15), computed backward from the components
`fT j` of an additively convex terminal value `f_{T+1}(ω, y) = Σ_j fT j ω (y_j)` (Assumption 1,
p.12) by (11)–(14): `comps T fT t = fT` for `t > T`, and for `t ≤ T`,
`comps T fT t j ω y = −k^E_j y + w^+_jt(ω, y)` with `w_jt` built from `comps T fT (t + 1)`.

The module also defines the period-`t` functions `g_jt, u_jt, v_jt, w_jt`, the basestock levels
`S^E_jt, S^R_jt, S_jt` of Theorem 4 (p.15), and the nondegeneracy condition under which the `±`
notation of p.14 is defined.

**Formalization Note.** The components of `f_{T+1}` are a choice (any additive constants summing to
zero may be moved between them); the recursion uses the given `fT`, and every level and every
function `g, u, v, w` is unaffected by such a shift up to additive constants. -/
noncomputable def comps (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) : Fin N → Ω → ℝ → ℝ :=
  M.compsAux fT (T + 1 - t) t

/-- `g_jt` of (11) in the finite-horizon problem with horizon `T` and terminal components `fT`. -/
noncomputable def gT (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (j : Fin N) (ω : Ω) : ℝ → ℝ :=
  M.gF t (M.comps T fT (t + 1)) j ω

/-- `u_jt` of (12) in the finite-horizon problem. -/
noncomputable def uT (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (j : Fin N) (ω : Ω) : ℝ → ℝ :=
  M.uF t (M.comps T fT (t + 1)) j ω

/-- `v_jt` of (13) in the finite-horizon problem. -/
noncomputable def vT (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (j : Fin N) (ω : Ω) : ℝ → ℝ :=
  M.vF t (M.comps T fT (t + 1)) j ω

/-- `w_jt` of (14) in the finite-horizon problem. -/
noncomputable def wT (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (j : Fin N) (ω : Ω) : ℝ → ℝ :=
  M.wF t (M.comps T fT (t + 1)) j ω

/-- `S^E_jt(ω) := inf arg min_Y w_jt(ω, Y)` (Theorem 4(a), p.15), in `EReal`. -/
noncomputable def SEt (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (ω : Ω) (j : Fin N) : EReal :=
  infArgmin (M.wT T fT t j ω)

/-- `S^R_jt(ω) := sup arg min_Y u_jt(ω, Y)` (Theorem 4(b), p.15), in `EReal`. -/
noncomputable def SRt (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (ω : Ω) (j : Fin N) : EReal :=
  supArgmin (M.uT T fT t j ω)

/-- `S_jt(ω) := sup arg min_Y g_jt(ω, Y)` (Theorem 4(c), p.15), in `EReal`. -/
noncomputable def St (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) (ω : Ω) (j : Fin N) : EReal :=
  supArgmin (M.gT T fT t j ω)

/-- **Nondegeneracy from period `t` on**: in every period `s ∈ [t, T]`, at every location and
Markov state, the functions `g_js, u_js, w_js` to which the `±` notation of p.14 is applied have a
finite minimizer, and the expectation in (11) is finite (`f̃_{j,s+1}(ω_{s+1}, Y − D_s)` is
integrable for every `Y`). This is the presupposition of the notation on p.14 ("for any convex
function `f` with a finite minimizer `S`") and of the real-valued (11). -/
def Nondeg (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (t : ℕ) : Prop :=
  ∀ s, t ≤ s → s ≤ T → ∀ j ω,
    HasMin (M.gT T fT s j ω) ∧ HasMin (M.uT T fT s j ω) ∧ HasMin (M.wT T fT s j ω) ∧
      ∀ Y, Integrable (fun z : ℝ × Ω => M.comps T fT (s + 1) j z.2 (Y - z.1)) (M.κ s ω)

end Model

end ReverseLogisticsNEBS


