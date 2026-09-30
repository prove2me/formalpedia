-- Prove2me | Definitions.Def_Avram2004_Shared_reflected
-- name    : Avram2004_Shared_reflected
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:03:56.459098+00:00
-- url     : https://prove2.me/theorems/5e4ba030-682f-4a3f-a57a-87a2b5dd1ba4
-- title:
--   Running maximum X̄, reflected process Y = X̄ − X and passage time τ_k = inf{t ≥ 0 : Y_t ∉ [0, k)}
-- statement:
--   Let $X=\{X_t,\ t\ge0\}$ be a real process with $X_0=0$ and càdlàg paths. For real numbers $s\ge x$ consider the process started at $x$, i.e. the path $u\mapsto x+X_u$, with a "prior maximum" $s$ (the paper's measure $\mathbb P_{s,x}$).
--
--   1. The **running maximum** is
--   $$\overline X_t=\max\Big\{s,\ \sup_{0\le u\le t}(x+X_u)\Big\}.$$
--   2. The **reflected process** is $Y_t=\overline X_t-(x+X_t)$; it is nonnegative and $Y_0=s-x$.
--   3. For real $k$, the **passage time**
--   $$\tau_k=\inf\{t\ge0:\ Y_t\notin[0,k)\},$$
--   with $\inf\emptyset=+\infty$.
--   4. For $t\ge0$ and a random time $T\in[0,\infty]$, $t\wedge T$ denotes the minimum (equal to $t$ when $T=\infty$).
--
--   The paper exchanges freely between $\mathbb P_{s,x}$ and $\mathbb P_{-(s-x)}$: the reflected process depends on $(s,x)$ only through $z=s-x$. Under $\mathbb P_{-z}$ (that is, $s=0$, $x=-z$) the process $Y$ starts at $Y_0=z$. The Russian problem (28) is posed in terms of $Y$ under $\mathbb P^1_{-z}$, and its optimal stopping time is $\tau_{\kappa^*}$; the Canadized Russian problem (32) likewise, with optimal stopping time $\tau_{\kappa_*}$.
--
--   **Formalization Note** Time is $[0,\infty)$ and random times take values in $[0,\infty]$. The supremum in $\overline X_t$ is of a set that is bounded above because a càdlàg path is bounded on compacts. The paper defines $\tau_k$ for $k>0$; for $k\le0$ the set $[0,k)$ is empty and the same formula gives $\tau_k=0$, which is the reading the paper uses when it says "$\kappa^*=0$ and it is optimal to stop immediately".
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `02-russian` (Theorem 2: Remarks 3–4 and Lemma 1 p. 218, the Russian problem (27)–(28) pp. 227–228, Corollary 1 p. 228, Lemma 2 and Theorem 2 p. 229, proof of Theorem 2 pp. 230–231); `03-canadized-russian` (Theorem 3: Corollary 1 p. 228, Lemma 2 (i) p. 229, the Canadized problem (32) and Lemma 3 pp. 231–233, Theorem 3 p. 233, Lemma 4 p. 234, proof of Theorem 3 pp. 234–235).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 220, Section 4, first paragraph (definitions of X̄, ℙ_{s,x}, Y and τ_k)

import Mathlib

open scoped NNReal

namespace Avram2004.Shared

/-- §4, p. 220: the running maximum `X̄_t = max {s, sup_{0 ≤ u ≤ t} X_u}` under `ℙ_{s,x}`, i.e. for the
path `u ↦ x + X_u` started at `x` with prior maximum `s`. (For a càdlàg path the set is bounded above.) -/
noncomputable def runMax {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max s (sSup ((fun u => x + X u ω) '' Set.Icc 0 t))

/-- §4, p. 220: the reflected process `Y = X̄ - X` under `ℙ_{s,x}`. -/
noncomputable def refl {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  runMax s x X t ω - (x + X t ω)

/-- §4, p. 220: `τ_k = inf {t ≥ 0 : Y_t ∉ [0, k)}` under `ℙ_{s,x}`, with `inf ∅ = ⊤` (never).
For `k ≤ 0` the set `[0, k)` is empty and `τ_k = 0`. -/
noncomputable def tau {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (k : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | refl s x X t ω ∉ Set.Ico 0 k}, (t : WithTop ℝ≥0)

/-- The time `t ∧ T` for a random time `T` (always finite; `t ∧ ⊤ = t`). -/
def stopAt (t : ℝ≥0) (T : WithTop ℝ≥0) : ℝ≥0 :=
  match T with
  | none => t
  | some r => min t r

end Avram2004.Shared


