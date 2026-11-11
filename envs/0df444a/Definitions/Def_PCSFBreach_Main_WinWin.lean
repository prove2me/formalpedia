-- Prove2me | Definitions.Def_PCSFBreach_Main_WinWin
-- name    : PCSFBreach_Main_WinWin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:56:56.076309+00:00
-- url     : https://prove2.me/theorems/6614c0bd-12f2-4abf-a075-fad98e4ff762
-- title:
--   Algorithm 1 quantities: Q≥1/2, x_{D′}, x¹_Q, x²_Q, x̄_Q, x̄_{D′}, p, sl and q; the 2APX and bifactor guarantees
-- statement:
--   For a run of the primal-dual algorithm with capacity parameter $\lambda$, a coloring $a$ and a forest $F^*$ (§3, pp. 8–9):
--   $$x_{D'}=\sum_{U\in H}\sum_{i\in D(F^*)\cap D'}a_{Ui},\quad x^1_Q=\sum_{U\in H:\,d_{F^*}(U)=1}\ \sum_{i\in D(F^*)\cap Q}a_{Ui},\quad x^2_Q=\sum_{U\in H:\,d_{F^*}(U)\ge 2}\ \sum_{i\in D(F^*)\cap Q}a_{Ui},$$
--   $$\bar x_Q=\sum_{U\in H}\sum_{i\in\bar D(F^*)\cap Q}a_{Ui},\quad \bar x_{D'}=\sum_{U\in H}\sum_{i\in\bar D(F^*)\cap D'}a_{Ui},\quad p=\pi(\bar D(F^*)\cap D'),$$
--   $sl_c=c(F^*)-x_{D'}-x^1_Q-2x^2_Q$, $sl_\pi=p-\bar x_{D'}$, $sl=sl_c+sl_\pi$, $q=x^1_Q-x^2_Q+\bar x_Q$, and $Q_{\ge 1/2}=\{i: r_i\ge 1/2\}$.
--
--   An algorithm (a map $A$ from instances to edge sets) has the **2APX guarantee** if on every instance $J$ it returns a forest with $\mathrm{cost}(A(J))\le 2\,\mathrm{cost}(F)$ for every forest $F$ of $J$; it has the **bifactor guarantee** with constants $\delta,K$ if it returns a forest with $\mathrm{cost}\le(2-\delta)c(F)+K\pi(\bar D(F))$ for every forest $F$.
--
--   These are the quantities of Lemmas 3–5.
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), pp. 8–9, §3 (Algorithm 1 and the quantities x, p, sl, q); p. 4 (2APX); p. 7, Theorem 2 (bifactor guarantee)

import Mathlib
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
set_option autoImplicit false

namespace PCSFBreach.Main

open Finset

/-- An algorithm (any map from instances to edge sets) with the guarantee of **2APX**
([AGHJM24a], p. 4): on every instance it returns a forest whose cost is at most twice the cost of
every forest. -/
def IsTwoApprox (A : (J : Instance) → Finset J.Edge) : Prop :=
  ∀ J : Instance, J.IsForest (A J) ∧ ∀ F, J.IsForest F → J.cost (A J) ≤ 2 * J.cost F

/-- An algorithm with the **bifactor** guarantee of Theorem 2 (p. 7) for constants `δ, K`: on
every instance it returns a forest of cost at most `(2 − δ) c(F) + K π(D̄(F))` for every forest `F`. -/
def IsBifactor (δ K : ℝ) (B : (J : Instance) → Finset J.Edge) : Prop :=
  ∀ J : Instance, J.IsForest (B J) ∧ ∀ F, J.IsForest F →
    J.cost (B J) ≤ (2 - δ) * J.edgeCost F + K * J.penaltyOf (J.disconnectedPairs F)

namespace PDRun

variable {I : Instance} (R : PDRun I)

open scoped Classical in
/-- `Q_{≥1/2} = {i ∈ D : r_i ≥ 1/2}` (Algorithm 1, line 2, p. 8). -/
noncomputable def Qhalf (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) : Finset I.Pair :=
  univ.filter (fun i => (1 / 2 : ℝ) ≤ R.ratio lam a i)

/-- `x_{D′}` (p. 8): color on the pairs of `D(F*) ∩ D′`. -/
noncomputable def xDp (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  ∑ U ∈ R.H, ∑ i ∈ I.connectedPairs Fs ∩ R.D' lam, a U i

open scoped Classical in
/-- `x¹_Q` (p. 8): color on the pairs of `D(F*) ∩ Q` on moats crossed by `F*` exactly once. -/
noncomputable def x1Q (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  ∑ U ∈ R.H.filter (fun U => I.dF Fs U = 1), ∑ i ∈ I.connectedPairs Fs ∩ R.Q lam, a U i

open scoped Classical in
/-- `x²_Q` (p. 8): color on the pairs of `D(F*) ∩ Q` on moats crossed by `F*` at least twice. -/
noncomputable def x2Q (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  ∑ U ∈ R.H.filter (fun U => 2 ≤ I.dF Fs U), ∑ i ∈ I.connectedPairs Fs ∩ R.Q lam, a U i

/-- `x̄_Q` (p. 8): color on the pairs of `D̄(F*) ∩ Q`. -/
noncomputable def xbarQ (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  ∑ U ∈ R.H, ∑ i ∈ I.disconnectedPairs Fs ∩ R.Q lam, a U i

/-- `x̄_{D′}` (p. 8): color on the pairs of `D̄(F*) ∩ D′`. -/
noncomputable def xbarDp (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  ∑ U ∈ R.H, ∑ i ∈ I.disconnectedPairs Fs ∩ R.D' lam, a U i

/-- `p = π(D̄(F*) ∩ D′)` (p. 8). -/
noncomputable def pD (lam : ℝ) (Fs : Finset I.Edge) : ℝ :=
  (I.penaltyOf (I.disconnectedPairs Fs ∩ R.D' lam) : ℝ)

/-- `sl_c = c(F*) − x_{D′} − x¹_Q − 2 x²_Q` (p. 9). -/
noncomputable def slc (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  (I.edgeCost Fs : ℝ) - R.xDp lam a Fs - R.x1Q lam a Fs - 2 * R.x2Q lam a Fs

/-- `sl_π = p − x̄_{D′}` (p. 9). -/
noncomputable def slpi (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  R.pD lam Fs - R.xbarDp lam a Fs

/-- `sl = sl_c + sl_π` (p. 9). -/
noncomputable def sl (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  R.slc lam a Fs + R.slpi lam a Fs

/-- `q = x¹_Q − x²_Q + x̄_Q` (p. 9). -/
noncomputable def qQ (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (Fs : Finset I.Edge) : ℝ :=
  R.x1Q lam a Fs - R.x2Q lam a Fs + R.xbarQ lam a Fs

end PDRun

end PCSFBreach.Main


