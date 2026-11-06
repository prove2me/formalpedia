-- Prove2me | Definitions.Def_RandomLPIPM_algo1Step
-- name    : RandomLPIPM_algo1Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:14.24766+00:00
-- url     : https://prove2.me/theorems/5627ec6a-6b71-4d55-a714-15c87218521f
-- title:
--   One transition of Algorithm 1 (smoothed-divergence path following IPM)
-- statement:
--   Algorithm 1 takes an instance $(A,b,c)$ of (LP), a section $[\mu_{\mathrm{end}},\mu_{\mathrm{start}}]$, a proximity parameter $\varepsilon$, a strictly feasible $x^0$ and a Lipschitz constant $C$; with $C'=\max\{C,1\}$ it runs
--   1. while $\mu>\mu_{\mathrm{end}}$:
--   2. $\quad\mu\leftarrow\max\{\mu_{\mathrm{end}},(1-\tfrac1{64C'})\mu\}$; $P_x\leftarrow I-XA^\top(AX^2A^\top)^{-1}AX$; $u\leftarrow0$;
--   3. $\quad$while $\|P_x\nabla\Phi_{x,\mu}(u)\|_2^2>\varepsilon^2/16$: $u\leftarrow u-\tfrac12P_x\nabla\Phi_{x,\mu}(u)$;
--   4. $\quad x\leftarrow x(\mathbf 1_n+u)$;
--   5. return $(\hat x,\hat\mu)=(x,\mu)$.
--
--   This definition is one transition of that program: at the outer test it either returns (if $\mu\le\mu_{\mathrm{end}}$) or decreases $\mu$ and resets $u$; in the inner loop it evaluates $g=P_x\nabla\Phi_{x,\mu}(u)$ at the current $x$ and new $\mu$ (counting the evaluation), and either takes the step $u\leftarrow u-g/2$ or, once $\|g\|_2^2\le\varepsilon^2/16$, updates $x\leftarrow x(\mathbf 1+u)$ and returns to the outer test; a returned state is unchanged.
--
--   **Formalization Note** The run is the iteration of this map from the initial state; it is deterministic. The test of line 7 compares the **squared** Euclidean norm with $\varepsilon^2/16$. The counter counts evaluations of line 7, each one application of $P_x$. The data $b$ and $\mu_{\mathrm{start}}$ enter only through the initial state.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Algorithm 1, p.80

import Mathlib
import Definitions.Def_RandomLPIPM_Algo1State
import Definitions.Def_RandomLPIPM_Px
import Definitions.Def_RandomLPIPM_gradPhi
import Definitions.Def_ColumnRandLP_Norms

open Matrix

namespace RandomLPIPM

/-- **One transition of Algorithm 1 (smoothed-divergence path following IPM).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…),
Algorithm 1, p.80, with inputs `A, c` (an instance of (LP)), `μ_end`, the proximity parameter `ε` and
the Lipschitz constant `C`:

* `outer` (lines 3–6): if `μ ≤ μ_end` the loop exits (line 10, `done`); otherwise
  `μ ← max{μ_end, (1 − 1/(64C′))μ}` with `C′ = max{C, 1}` (lines 1, 4), `u ← 0` (line 6), and
  the inner loop starts.
* `inner` (lines 7–9): `g := P_x ∇Φ_{x,μ}(u)` with `P_x = I − XAᵀ(AX²Aᵀ)⁻¹AX` (line 5) at the current
  `x` and the new `μ`; this evaluation is counted in `solves`. If `‖g‖₂² > ε²/16` then
  `u ← u − ½g` (line 8); otherwise `x ← x(1 + u)` (line 9) and control returns to line 3.
* `done`: the state is unchanged.

**Formalization Note.** The run is `(algo1Step …)^[j] (algo1Init x0 μstart)`; it is deterministic,
so "some `j` reaches `done`" names the one run, and its output is `(x̂, μ̂) = (s.x, s.μ)`. The
threshold of line 7 is the *squared* Euclidean norm against `ε²/16` (rendered page; the text layer
drops the square). `solves` counts line-7 evaluations, each one application of `P_x`. The data `b`
and `μ_start` enter only through the initial state. -/
noncomputable def algo1Step {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (c : Fin n → ℝ)
    (μend ε C : ℝ) (s : Algo1State n) : Algo1State n :=
  match s.phase with
  | Algo1Phase.outer =>
      if s.μ ≤ μend then { s with phase := Algo1Phase.done }
      else { s with μ := max μend ((1 - 1 / (64 * max C 1)) * s.μ), u := 0,
                    phase := Algo1Phase.inner }
  | Algo1Phase.inner =>
      let g := Px A s.x *ᵥ gradPhi c s.x s.μ s.u
      if ε ^ 2 / 16 < ColumnRandLP.l2Norm g ^ 2 then
        { s with u := s.u - (1 / 2 : ℝ) • g, solves := s.solves + 1 }
      else
        { s with x := s.x * (1 + s.u), phase := Algo1Phase.outer, solves := s.solves + 1 }
  | Algo1Phase.done => s

end RandomLPIPM


