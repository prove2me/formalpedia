-- Prove2me | Definitions.Def_TemporalVoter_minoritySet
-- name    : TemporalVoter_minoritySet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:57.876526+00:00
-- url     : https://prove2.me/theorems/bddde512-0f79-402c-a5d2-a5ffa3d7af29
-- title:
--   Two-opinion objects: opinion-0 set $A_t$, minority set $S_t$, stopping times $T_j$, histories, stability, $\psi$ and $\chi$
-- statement:
--   Consider the voter model with two opinions on a temporal graph with fixed degrees.
--
--   1. The **opinion-0 set** of a state $x$ is $A=x^{-1}(0)$; along the process $A_t=\xi_t^{-1}(0)$.
--   2. The **minority set** is $S=A$ if $\mathrm{Vol}(A)\le\mathrm{Vol}(\overline A)$, and $S=\overline A$ otherwise; $S_t$ is the minority set of $\xi_t$.
--   3. The **history** at time $t$ is $\mathcal H_t=(A_0,\dots,A_t)$. The event $\{\mathcal H_t=H\}$ is represented by a path $h$: the process agrees with $h$ up to time $t$.
--   4. Given interval lengths $\Delta_0,\Delta_1,\ldots\ge1$, the **stopping times** are $T_0=0$ and $T_{j+1}=\min\{I^+_j+1,\ T_{j,\min}\}$, where
--   $$T_{j,\min}=\min\Bigl\{t\ge T_j:\ \mathrm{Vol}(S_t)\notin\bigl[\tfrac12\mathrm{Vol}(S_{T_j}),\tfrac32\mathrm{Vol}(S_{T_j})\bigr]\text{ or }S_t=\emptyset\Bigr\}$$
--   (and $T_{j,\min}=\infty$ if no such $t$ exists). The event $\{\mathcal H_{T_j}=H\}$ is: $T_j=t_j$ and the process agrees with $h$ up to $t_j$.
--   5. A possible value $H$ of $\mathcal H_{T_j}$ with $s=S_{T_j}\neq\emptyset$ is **stable** if
--   $$\mathbb E\bigl[\,|\mathrm{Vol}(S_{T_{j+1}})-\mathrm{Vol}(s)|\ \big|\ \mathcal H_{T_j}=H\bigr]<\mathrm{Vol}(s)/8,$$
--   and **unstable** otherwise.
--   6. The potentials are $\psi(S)=\sqrt{\mathrm{Vol}(S)}$ and $\chi(S)=\log(1+\mathrm{Vol}(S))$ (natural logarithm).
--
--   These are the objects of the two-opinion analysis: the volume of the minority set is a supermartingale, and its drift is studied separately on stable and unstable intervals between consecutive stopping times.
--
--   **Formalization Note** Conditioning on a value of a history is elementary conditioning on an event of positive probability (`ProbabilityTheory.cond`) under the voter law started at $\sigma_0$. $T_{j+1}$ is the infimum of the nonempty set $\{t\ge T_j:\dots\}\cup\{I^+_j+1\}$, which is the stated minimum.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), §1.2, p.5 (A_t); Definition 2.3, p.12; Definition 2.6, p.13; Definition 3.2, p.15; Definition 3.4, p.16; p.9 (ψ); Definition 3.10, p.21

import Mathlib
import Definitions.Def_TemporalVoter_temporalConductance
import Definitions.Def_TemporalVoter_voterLaw

open scoped Classical
open MeasureTheory ProbabilityTheory

namespace TemporalVoter

variable {V : Type} [Fintype V]

/-- The opinion-0 set `A_t = ξ_t⁻¹(0)` of a two-opinion state (arXiv:2606.13374, version of
2 Nov 2026, §1.2, p.5). -/
def opinionZeroSet (x : V → Fin 2) : Finset V :=
  Finset.univ.filter fun v => x v = 0

/-- The **minority set** (Definition 2.6, p.13): `S = A` if `Vol(A) ≤ Vol(Ā)`, otherwise `S = Ā`,
where `A` is the opinion-0 set of the state `x` (ties go to `A`). -/
noncomputable def minoritySet (T : TemporalGraph V) (x : V → Fin 2) : Finset V :=
  if T.vol (opinionZeroSet x) ≤ T.vol (opinionZeroSet x)ᶜ then opinionZeroSet x
  else (opinionZeroSet x)ᶜ

/-- The event `{H_t = H}` that the history `H_t = (ξ_0, …, ξ_t)` (Definition 2.3, p.12) of a path
agrees with the history of the path `h` up to time `t`.

**Formalization Note** A value of `H_t` is represented by any path `h` extending it; only
`h 0, …, h t` matter. "A possible value" means `0 < ℙ(H_t = H)` (elementary conditioning). -/
def historyEvent {α : Type} (t : ℕ) (h : ℕ → α) : Set (ℕ → α) :=
  {ω | ∀ s ≤ t, ω s = h s}

/-- The **stopping times** `T_j` of Definition 3.2 (p.15), for the two-opinion voter model with
interval lengths `Δ`: `T_0 = 0` and `T_{j+1} = min{I⁺_j + 1, T_{j,min}}` with
`T_{j,min} = min{t ≥ T_j : Vol(S_t) ∉ [½Vol(S_{T_j}), 3/2·Vol(S_{T_j})] or S_t = ∅}`.

**Formalization Note** `T_{j+1}` is the infimum of the nonempty set `{t ≥ T_j : …} ∪ {I⁺_j + 1}`,
which is the paper's minimum with the convention `T_{j,min} = ∞` when no such `t` exists. -/
noncomputable def stoppingTimes (T : TemporalGraph V) (Δ : ℕ → ℕ) :
    ℕ → (ℕ → V → Fin 2) → ℕ
  | 0, _ => 0
  | j + 1, ω =>
    sInf ({t | stoppingTimes T Δ j ω ≤ t ∧
        (T.vol (minoritySet T (ω t)) ∉
            Set.Icc (T.vol (minoritySet T (ω (stoppingTimes T Δ j ω))) / 2)
              (3 * T.vol (minoritySet T (ω (stoppingTimes T Δ j ω))) / 2) ∨
          minoritySet T (ω t) = ∅)} ∪ {Iplus Δ j + 1})

/-- The event `{H_{T_j} = H}`: `T_j = t_j` and the history up to `t_j` is that of `h`
(Definitions 3.2 and 2.3, pp.12–15). -/
noncomputable def stoppedHistoryEvent (T : TemporalGraph V) (Δ : ℕ → ℕ) (j tj : ℕ)
    (h : ℕ → V → Fin 2) : Set (ℕ → V → Fin 2) :=
  {ω | stoppingTimes T Δ j ω = tj ∧ ∀ s ≤ tj, ω s = h s}

/-- **Stable** value of `H_{T_j}` (Definition 3.4, p.16): with `s = S_{T_j}` the value determined
by `H_{T_j} = H`, `E[|Vol(S_{T_{j+1}}) − Vol(s)| | H_{T_j} = H] < Vol(s)/8`; otherwise it is
unstable. The conditioning is elementary conditioning of the voter law started at `σ₀`. -/
noncomputable def IsStable (T : TemporalGraph V) (σ₀ : V → Fin 2) (Δ : ℕ → ℕ) (j tj : ℕ)
    (h : ℕ → V → Fin 2) : Prop :=
  ∫ ω, |T.vol (minoritySet T (ω (stoppingTimes T Δ (j + 1) ω))) - T.vol (minoritySet T (h tj))|
      ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h]
    < T.vol (minoritySet T (h tj)) / 8

/-- The potential `ψ(S) = √Vol(S)` (p.9). -/
noncomputable def psi (T : TemporalGraph V) (S : Finset V) : ℝ :=
  Real.sqrt (T.vol S)

/-- The potential `χ(S) = log(1 + Vol(S))`, natural logarithm (Definition 3.10, p.21; p.12). -/
noncomputable def chi (T : TemporalGraph V) (S : Finset V) : ℝ :=
  Real.log (1 + T.vol S)

end TemporalVoter


