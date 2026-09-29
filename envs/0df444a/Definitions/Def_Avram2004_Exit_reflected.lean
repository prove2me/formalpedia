-- Prove2me | Definitions.Def_Avram2004_Exit_reflected
-- name    : Avram2004_Exit_reflected
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:19:46.70629+00:00
-- url     : https://prove2.me/theorems/e72c7160-80b3-438e-8740-66eea697ad03
-- title:
--   The running maximum X̄, the reflected process Y = X̄ − X, the exit time τ_k and the hitting time τ_{0}
-- statement:
--   Let $X$ be a real-valued process indexed by $t\ge0$ with $X_0=0$. Under $\mathbb P_{s,x}$ the process starts at $x$ with a prior maximum $s\ge x$: its path is $t\mapsto x+X_t$ and its **running maximum** is
--   $$\overline X_t=\max\Big\{s,\ \sup_{0\le u\le t}(x+X_u)\Big\}.$$
--   The **reflected process** is $Y_t=\overline X_t-(x+X_t)$, so $Y_0=s-x=:z$. For $k>0$,
--   $$\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\},\qquad \tau_{\{0\}}=\inf\{t\ge0:Y_t=0\},$$
--   with $\inf\emptyset=\infty$: $\tau_k$ is the first exit time of $Y$ from $[0,k)$ and $\tau_{\{0\}}$ the first time $Y$ hits zero. Two derived quantities are used: the stopped time $t\wedge\tau_k$ (always finite), and the functional $e^{-u\tau_k-vY_{\tau_k}}$, given the value $0$ on $\{\tau_k=\infty\}$.
--
--   These are the objects of Theorem 1, which computes the joint Laplace transform of $(\tau_k,Y_{\tau_k})$.
--
--   **Formalization Note** The supremum is of a set that is bounded above because a càdlàg path is bounded on compact intervals. $\tau_k$ keeps the paper's set $\{Y_t\notin[0,k)\}$ and the infimum over $t\ge0$ (not $t>0$). Values at $\tau_k$ are taken by cases on whether $\tau_k$ is finite; nothing is evaluated at a default time.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, pp. 220–221, Section 4 (definitions of X̄, Y, τ_k) and proof of Theorem 1 (τ_{0})

import Mathlib

open scoped NNReal

namespace Avram2004.Exit

/-- §4, p. 220: the running maximum `X̄_t = max {s, sup_{0 ≤ u ≤ t} X_u}` under `ℙ_{s,x}`, i.e. for the
path `u ↦ x + X_u` started at `x` with prior maximum `s`. (For a càdlàg path the set is bounded above.) -/
noncomputable def runMax {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max s (sSup ((fun u => x + X u ω) '' Set.Icc 0 t))

/-- §4, p. 220: the reflected process `Y = X̄ - X` under `ℙ_{s,x}`. -/
noncomputable def refl {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  runMax s x X t ω - (x + X t ω)

/-- §4, p. 220: `τ_k = inf {t ≥ 0 : Y_t ∉ [0, k)}` under `ℙ_{s,x}`, with `inf ∅ = ⊤` (never). -/
noncomputable def tau {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (k : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | refl s x X t ω ∉ Set.Ico 0 k}, (t : WithTop ℝ≥0)

/-- p. 221: `τ_{0}`, the first time that `Y` hits zero, `inf {t ≥ 0 : Y_t = 0}`, with `inf ∅ = ⊤`. -/
noncomputable def tauZero {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | refl s x X t ω = 0}, (t : WithTop ℝ≥0)

/-- The time `t ∧ T` for a random time `T` (always finite). -/
def stopAt (t : ℝ≥0) (T : WithTop ℝ≥0) : ℝ≥0 :=
  match T with
  | none => t
  | some r => min t r

/-- The functional `e^{-u τ_k - v Y_{τ_k}}` of Theorem 1 under `ℙ_{s,x}`, with the value `0` on the
event `{τ_k = ∞}`. -/
noncomputable def exitFunctional {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (k u v : ℝ) (ω : Ω) : ℝ :=
  match tau s x X k ω with
  | none => 0
  | some t => Real.exp (-u * (t : ℝ) - v * refl s x X t ω)

end Avram2004.Exit


