-- Prove2me | Definitions.Def_MultiNashRepair_IDRH
-- name    : MultiNashRepair_IDRH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:10.134666+00:00
-- url     : https://prove2.me/theorems/73ab78bc-96e4-4c6e-a1c1-9995a31788a2
-- title:
--   Algorithm 1 (IDRH) as a run relation: states, descent and repair steps, reachable states, outputs
-- statement:
--   A **state** of Algorithm 1 consists of a mixed profile $x$, historical weights $h=(h_i)$, their total $H$, and a list of stored repair generations (analysis-only).
--
--   Fix admissible controls for $\sigma$ and a game $u$, and write $\varsigma=m(1-\mathrm{Reg}(x))$, $\mu=S_u(H)-\varsigma-d$.
--   1. A state is **terminal** if $\varsigma\ge\sigma$. An **initial** state has a rational mixed profile with $\varsigma\ge1$ (Lemma 2.2), $h=0$, $H=0$ and no generations.
--   2. **Descent step** (lines 9–11): the LP passes and $z$ is an optimal rational LP solution; then $x\mapsto x^+$ by (3.2), $h\mapsto Ph$, $H\mapsto PH$, and every stored mass is multiplied by $P$.
--   3. **Repair step** (lines 13–17): the LP fails and $(w,\alpha)$ is an optimal rational dual. With $\lambda,b$ from (3.4), $v_i=mh_i-H$, $\tau=\sum_i\lambda_iv_i$,
--   $$\gamma_i=\lambda_i\frac{G_0-Qv_i}{G_0-Q\tau},\qquad D=\beta(G_0+QH),\qquad \delta_i=\frac Dm-\beta\gamma_i-\nu h_i\qquad(3.6),$$
--   activation (3.7), the reverse sweep (3.8) with budgets $\delta$, $C_{\mathrm{raw}}=\rho\prod_i(1-t\gamma_i)$, the frozen deficits (3.9) and the forward correction (3.10) give the new profile; $h\mapsto c(h+t\gamma)$, $H\mapsto c(H+t)$ (3.11); old masses are multiplied by $c$ and the new generation $(x,b,\gamma,t)$ is stored with mass $c$.
--   4. A **step** is a descent or a repair step from a nonterminal state. A state is **reachable at iteration $k$** if a run of $k$ steps from an initial state ends there.
--   5. An **output** of Algorithm 1 is, for $m<m_0$, an initial profile, and for $m\ge m_0$, the profile of a terminal reachable state.
--
--   The repair is **legal** when $G_0-Q\tau>0$, $\gamma$ is a probability vector with $0\le t\gamma_i<1$, the budgets are nonnegative with total $1-\rho$ and every prefix $1-\sum_{j\le i}\delta_j\ge\rho>0$, every $\theta_i\in[0,1)$, and the activated and raw profiles are mixed.
--
--   **Formalization Note** Every choice the pseudocode leaves open (the optimal rational LP solution, the optimal rational dual, the best responses) is existentially witnessed, so statements about runs hold for all choices; the only fixed tie is $b_i=e_0$ when $\lambda_i=0$. No condition of a step reads the stored generations.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Algorithm 1, p.7; (3.2)–(3.11), pp.7–10; (3.13), p.10; §5.5, p.39

import Mathlib
import Definitions.Def_MultiNashRepair_Controls
import Definitions.Def_MultiNashRepair_DescentLP
import Definitions.Def_MultiNashRepair_Generation
import Definitions.Def_MultiNashRepair_Sweeps

open NashAmplification.Filtering (Mixed Utility Tuple)
open Finset

noncomputable section

namespace MultiNashRepair

/-- **A state of Algorithm 1 (IDRH)** (Tang, Ding, Fang, arXiv:2611.06076, Algorithm 1, p.7):
the current product profile `x^{(k)}`, the historical weights `h^{(k)}`, their total `H^{(k)}`,
and the list of stored repair generations (§5.3, §5.5).

**Formalization Note.** `gens` is ghost data for the analysis (Lemma 5.2, pp.19–23; p.43:
"Its common masses, original-column certificates, and stored generations are witnesses for the
analysis"). No condition of the step relation reads it; the step only updates it. -/
structure State {m : ℕ} (n : Fin m → ℕ) where
  /-- the current profile `x^{(k)}` -/
  x : Mixed n
  /-- the historical weights `h^{(k)}` -/
  h : Fin m → ℝ
  /-- the total historical weight `H^{(k)}` -/
  H : ℝ
  /-- the stored repair generations (ghost) -/
  gens : List (Gen n)

variable {m : ℕ} {n : Fin m → ℕ}

section repair

variable (k : Knobs) (u : Utility n) (s : State n) (w : (i : Fin m) → Fin (n i) → ℝ)

/-- The centered weight `v_i = m h_i − H` ((3.5), p.8). -/
def rV (i : Fin m) : ℝ := (m : ℝ) * s.h i - s.H

/-- `τ = Σ_i λ_i v_i` ((3.5), p.8). -/
def rTau : ℝ := ∑ i, lam w i * rV s i

/-- The activation weight `γ_i = λ_i (G0 − Q v_i)/(G0 − Q τ)` ((3.6), p.8). -/
def rGamma (i : Fin m) : ℝ :=
  lam w i * (k.G0 - k.Q * rV s i) / (k.G0 - k.Q * rTau s w)

/-- The reverse budget `δ_i = D/m − β γ_i − ν h_i`, `D = β (G0 + Q H)` ((3.6), p.8). -/
def rDelta (i : Fin m) : ℝ :=
  k.Dsh s.H / m - k.beta * rGamma k s w i - k.nu * s.h i

/-- The activated profile `y` ((3.7), p.9). -/
def rY : Mixed n := actY s.x (bdev w) k.t (rGamma k s w)

/-- The raw profile `x̃` of the reverse sweep ((3.8), p.9). -/
def rXt (arev : (i : Fin m) → Fin (n i)) : Mixed n := revSweep (rY k s w) (rDelta k s w) arev

/-- `C_raw = ρ Π_i (1 − t γ_i)` ((3.9), p.9). -/
def rCraw : ℝ := k.rho * ∏ i, (1 - k.t * rGamma k s w i)

/-- The frozen correction deficits `e_i` ((3.9), p.9), with `ς = m(1 − Reg(x))` of the current
profile. -/
def rE (arev : (i : Fin m) → Fin (n i)) (i : Fin m) : ℝ :=
  corrDef u (scaled u s.x) (rCraw k s w) (k.Dsh s.H) (rXt k s w arev) i

/-- The total correction deficit `E = Σ_i e_i` ((3.9), p.9). -/
def rEtot (arev : (i : Fin m) → Fin (n i)) : ℝ := ∑ i, rE k u s w arev i

/-- The state after a repair with dual weights `w` and sweep actions `arev`, `acor`: the corrected
profile (3.10), `h⁺ = c(h + tγ)`, `H⁺ = c(H + t)` (3.11), and the generations with every old
mass multiplied by `c` and the new generation `(x, b, γ, t, c)` appended (Lemma 5.2 (C5)). -/
def repairState (arev acor : (i : Fin m) → Fin (n i)) : State n where
  x := fwdSweep (rXt k s w arev) (rE k u s w arev) acor
  h := k.c • (s.h + k.t • rGamma k s w)
  H := k.c * (s.H + k.t)
  gens := s.gens.map (fun g => { g with A := k.c * g.A }) ++
    [⟨s.x, bdev w, rGamma k s w, k.t, k.c⟩]

/-- The legality of a repair (Proposition 4.3, p.11 "a feasible repair"; Lemma 5.12, p.40 "a
legal repair"; Lemma 5.2, p.19): the normalizer `G0 − Qτ` is positive, `γ` is a probability
vector with `0 ≤ t γ_i < 1`, the reverse budgets are nonnegative with total `1 − ρ`, every prefix
`1 − Σ_{j ≤ i} δ_j` is at least `ρ > 0`, every forward probability lies in `[0, 1)`, and the
activated and raw profiles are mixed profiles. -/
def RepairLegal (arev : (i : Fin m) → Fin (n i)) : Prop :=
  0 < k.G0 - k.Q * rTau s w ∧ AGT.IsLottery (rGamma k s w) ∧
    (∀ i, 0 ≤ k.t * rGamma k s w i ∧ k.t * rGamma k s w i < 1) ∧
    (∀ i, 0 ≤ rDelta k s w i) ∧ ∑ i, rDelta k s w i = 1 - k.rho ∧
    0 < k.rho ∧ (∀ i, k.rho ≤ 1 - ∑ j ∈ univ.filter (· ≤ i), rDelta k s w j) ∧
    (∀ i, 0 ≤ fwdProb (rE k u s w arev) i ∧ fwdProb (rE k u s w arev) i < 1) ∧
    AGT.IsMixedProfile (rY k s w) ∧ AGT.IsMixedProfile (rXt k s w arev)

end repair

/-- The state after a descent with direction `z` ((3.2)–(3.3), p.7): the descent profile,
`h⁺ = P h`, `H⁺ = P H`, and every stored mass multiplied by `P` (Lemma 5.2 (C3)). -/
def descentState (η : ℝ) (s : State n) (z : (j : Fin m) → Fin (n j) → ℝ) : State n where
  x := descentProfile s.x η z
  h := descentFactor η z • s.h
  H := descentFactor η z * s.H
  gens := s.gens.map (fun g => { g with A := descentFactor η z * g.A })

variable {σ : ℚ} (ctrl : Controls σ) (u : Utility n)

/-- The stopping test `ς ≥ σ` (Algorithm 1 line 7, p.7; equivalently `Reg(x) ≤ 1 − σ/m`). -/
def Terminal (σ : ℚ) (u : Utility n) (s : State n) : Prop :=
  (σ : ℝ) ≤ scaled u s.x

/-- An initial state (Algorithm 1 lines 2–3): `x^{(0)}` is a rational mixed profile with
`σ^{(0)} ≥ 1` (the specification of Lemma 2.2), `h^{(0)} = 0`, `H^{(0)} = 0`, no generations. -/
def Init (s : State n) : Prop :=
  AGT.IsMixedProfile s.x ∧ (∀ i a, IsRat (s.x i a)) ∧ 1 ≤ scaled u s.x ∧
    s.h = 0 ∧ s.H = 0 ∧ s.gens = []

/-- The LP test of Algorithm 1 line 9 at a state, with `η` and `µ = S_u(H) − ς − d`. -/
def Passes (s : State n) : Prop :=
  LPPasses u s.x ctrl.η (ctrl.mu (scaled u s.x) s.H)

/-- **The descent branch** (Algorithm 1 lines 9–11): the LP passes, and `z` is an optimal
rational solution. -/
def DescentStep (s s' : State n) : Prop :=
  Passes ctrl u s ∧ ∃ z : (j : Fin m) → Fin (n j) → ℝ,
    LPOptimal u s.x ctrl.η z ∧ (∀ j b, IsRat (z j b)) ∧ s' = descentState ctrl.η s z

/-- **The repair branch** (Algorithm 1 lines 13–17): the LP fails, `(w, α)` is an optimal
rational dual solution, `arev` and `acor` are pure best responses of the two sweeps. -/
def RepairStep (s s' : State n) : Prop :=
  ¬ Passes ctrl u s ∧ ∃ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ)
      (arev acor : (i : Fin m) → Fin (n i)),
    DualOptimal u s.x ctrl.η w α ∧ (∀ i a, IsRat (w i a)) ∧
    IsRevBR u (rY ctrl.knobs s w) (rDelta ctrl.knobs s w) arev ∧
    IsFwdBR u (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor ∧
    s' = repairState ctrl.knobs u s w arev acor

/-- **One iteration of Algorithm 1** (lines 7–19): from a nonterminal state, a descent or a
repair.

**Formalization Note.** Every choice the pseudocode leaves open (the optimal rational LP
solution, the optimal rational dual, the pure best responses of both sweeps) is existentially
witnessed, so statements about runs hold for every choice. The only fixed tie is `b_i = e_0`
when `λ_i = 0` (p.8). -/
def Step (s s' : State n) : Prop :=
  ¬ Terminal σ u s ∧ (DescentStep ctrl u s s' ∨ RepairStep ctrl u s s')

/-- `Reach ctrl u k s`: some run of Algorithm 1 with controls `ctrl` on the game `u` is in state
`s` at the beginning of iteration `k`. -/
inductive Reach : ℕ → State n → Prop
  | init {s : State n} : Init u s → Reach 0 s
  | step {k : ℕ} {s s' : State n} : Reach k s → Step ctrl u s s' → Reach (k + 1) s'

/-- **An output of Algorithm 1** (lines 4–5 and 21): for `m < m0`, an initial profile (a rational
mixed profile with `σ^{(0)} ≥ 1`); for `m ≥ m0`, the profile of a terminal reachable state. -/
def IDRHOutput (x : Mixed n) : Prop :=
  (m < ctrl.m0 ∧ AGT.IsMixedProfile x ∧ (∀ i a, IsRat (x i a)) ∧ 1 ≤ scaled u x) ∨
    (ctrl.m0 ≤ m ∧ ∃ (k : ℕ) (s : State n), Reach ctrl u k s ∧ Terminal σ u s ∧ s.x = x)

end MultiNashRepair


