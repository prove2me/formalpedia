-- Prove2me | Definitions.Def_GeomRescale_Step
-- name    : GeomRescale_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:55.144317+00:00
-- url     : https://prove2.me/theorems/81655393-035b-4bb5-91aa-5a65e3a8fcaf
-- title:
--   One step of Algorithm 2
-- statement:
--   The steps of Rescaling-SFM are:
--
--   1. lines 2–3: $\mu := \max\{0, -f(V)\}$; $W := V$ if $f(V) < 0$, else $W := \emptyset$;
--   2. leaving the `for` loop after $T$ iterations and returning $W$;
--   3. starting the call of line 5;
--   4. one iteration of Algorithm 1;
--   5. leaving the call, when $\|y\|_Q \le \varepsilon$;
--   6. line 6: if $y = 0$, returning $W$;
--   7. lines 7–8: otherwise, rescaling by (10), setting $Q := R^{-1}$ and adding $g_1, \dots, g_k$ to $\Gamma$.
--
--   **Formalization Note** The test $y = 0$ is exact. $Q$ is literally the matrix inverse of $R$. $f$ is read only in steps that charge `evals`: one evaluation for lines 2–3 and $n$ per greedy vector. Operations: $n^2$ for lines 2–3, $n^2$ for the exit test, $n$ for line 6, $k n^2 + n^3$ for line 7, and $k$ for line 8.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10

import Mathlib
import Definitions.Def_GeomRescale_eps
import Definitions.Def_GeomRescale_numRounds
import Definitions.Def_GeomRescale_St
import Definitions.Def_GeomRescale_vnStart
import Definitions.Def_GeomRescale_VNStep
import Definitions.Def_GeomRescale_rescaled

namespace GeomRescale

/-- One step of Algorithm Rescaling-SFM (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10), with `T = numRounds n Λ` and
`ε = 1/(20n)`.

* `start`: lines 2–3. `μ := max {0, −f(V)}`; `W := V` if `f(V) < 0`, else `W := ∅`.
* `finish`: the `for` loop is exhausted, and `W` is returned.
* `call`: line 5 begins; lines 1–3 of Algorithm 1 run on the order `σ`.
* `iterate`: one iteration of the `while` loop of Algorithm 1.
* `exit`: the test of line 4 of Algorithm 1 fails, and the call returns.
* `stop`: line 6, `y = 0`, and `W` is returned.
* `rescale`: lines 7–8. `R` and `Q := R⁻¹` are updated, and `g₁, …, g_k` join `Γ`.

**Formalization Note.** `Q` after line 7 is literally `R⁻¹` (`Matrix.inv`); that `R` is invertible
along a run is a consequence, not a field. The test `y = 0` is exact: `‖y‖_Q ≤ ε` with `y ≠ 0`
rescales. The function `f` is read only through `vnStart`, `VNStep` and `start`, each of which pays
for it in `evals`. Charges: `start` costs one evaluation and `n²` operations; `exit` costs `n²`
operations; `stop` costs `n`; `rescale` costs `n` for line 6, `k n² + n³` for line 7, and `k` for
line 8, with `k = data.length`. -/
inductive Step {n : ℕ} (f : Finset (Fin n) → ℤ) (Λ : ℝ) : St n → St n → Prop
  | start (s : St n) :
      s.mode = Mode.start →
      Step f Λ s
        { s with
          vn :=
            { s.vn with
              μ := max 0 (-f Finset.univ)
              W := if f Finset.univ < 0 then Finset.univ else ∅
              evals := s.vn.evals + 1
              ops := s.vn.ops + n ^ 2 }
          mode := Mode.head }
  | finish (s : St n) :
      s.mode = Mode.head →
      numRounds n Λ ≤ s.i →
      Step f Λ s { s with mode := Mode.done s.vn.W }
  | call (s : St n) (σ : Equiv.Perm (Fin n)) :
      s.mode = Mode.head →
      s.i < numRounds n Λ →
      Step f Λ s
        { s with
          vn := vnStart f s.vn.μ s.vn.W s.Q σ s.vn.evals s.vn.ops
          mode := Mode.inner }
  | iterate (s : St n) (v' : VN n) :
      s.mode = Mode.inner →
      VNStep f s.Q (eps n) s.vn v' →
      Step f Λ s { s with vn := v' }
  | exit (s : St n) :
      s.mode = Mode.inner →
      qnorm s.Q s.vn.y ≤ eps n →
      Step f Λ s
        { s with
          vn := { s.vn with ops := s.vn.ops + n ^ 2 }
          mode := Mode.afterCall }
  | stop (s : St n) :
      s.mode = Mode.afterCall →
      s.vn.y = 0 →
      Step f Λ s
        { s with
          vn := { s.vn with ops := s.vn.ops + n }
          mode := Mode.done s.vn.W }
  | rescale (s : St n) :
      s.mode = Mode.afterCall →
      s.vn.y ≠ 0 →
      Step f Λ s
        { s with
          vn :=
            { s.vn with
              ops := s.vn.ops + n + (s.vn.data.length * n ^ 2 + n ^ 3) + s.vn.data.length }
          R := rescaled (eps n) s.Q s.R s.vn.data
          Q := (rescaled (eps n) s.Q s.R s.vn.data)⁻¹
          Γ := s.Γ ++ s.vn.data.map Prod.fst
          i := s.i + 1
          mode := Mode.head }

end GeomRescale


