-- Prove2me | Definitions.Def_Avram2004_Exit_passageTimes
-- name    : Avram2004_Exit_passageTimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:19:24.078508+00:00
-- url     : https://prove2.me/theorems/b34ebf26-06df-4dd3-9dcf-57f5d4c260c3
-- title:
--   Definition 4: first passage times T_k^− and T_k^+, and the discount factor e^{−qT}
-- statement:
--   Let $X$ be a real-valued process indexed by $t\ge0$ with $X_0=0$, and consider the process started at $x$, i.e. the path $t\mapsto x+X_t$ (the paper's measure $\mathbb P_x$). Definition 4, (8), introduces the first passage times below and above a level $k$:
--   $$T_k^-=\inf\{t>0:X_t\le k\},\qquad T_k^+=\inf\{t>0:X_t\ge k\},$$
--   with $\inf\emptyset=\infty$. For a random time $T$ and $q\in\mathbb R$ the **discount factor** $e^{-qT}$ is given the value $0$ on $\{T=\infty\}$.
--
--   These times describe the two-sided exit problem of Proposition 1: $T_a^-\wedge T_b^+$ is the exit time of $X$ from the interval $(a,b)$.
--
--   **Formalization Note** Times take values in $[0,\infty]$ (`WithTop ℝ≥0`), with $\infty$ standing for "never". The infima are over $t>0$ strictly, as printed. In every expectation of the mission the discount factor is multiplied by an indicator on which the time is finite, so the convention at $\infty$ never affects a value.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 219, Definition 4, Eq. (8)

import Mathlib

open scoped NNReal

namespace Avram2004.Exit

/-- Definition 4, (8): for the process started at `x` (the path `t ↦ x + X_t`), the first passage
time below `k`, `T_k^- = inf {t > 0 : X_t ≤ k}`, with `inf ∅ = ⊤` (never). -/
noncomputable def Tminus {Ω : Type*} (x : ℝ) (X : ℝ≥0 → Ω → ℝ) (k : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | 0 < t ∧ x + X t ω ≤ k}, (t : WithTop ℝ≥0)

/-- Definition 4, (8): for the process started at `x`, the first passage time above `k`,
`T_k^+ = inf {t > 0 : X_t ≥ k}`, with `inf ∅ = ⊤` (never). -/
noncomputable def Tplus {Ω : Type*} (x : ℝ) (X : ℝ≥0 → Ω → ℝ) (k : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | 0 < t ∧ k ≤ x + X t ω}, (t : WithTop ℝ≥0)

/-- The discount factor `e^{-qT}` of a random time `T`, with the value `0` when `T = ⊤` (never). -/
noncomputable def discount (q : ℝ) (T : WithTop ℝ≥0) : ℝ :=
  match T with
  | none => 0
  | some t => Real.exp (-q * (t : ℝ))

end Avram2004.Exit


