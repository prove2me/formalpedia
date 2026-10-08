-- Prove2me | Definitions.Def_SchedComplexity_PrecChain_Construction
-- name    : SchedComplexity_PrecChain_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:02:46.697772+00:00
-- url     : https://prove2.me/theorems/1f52f214-da05-40c5-98ce-321376446be0
-- title:
--   The construction of Theorem 1(l): n'' = (n'−1)y' added unit jobs in a chain after all jobs, and y = ny' + ½n''(n''+1)
-- statement:
--   The instance built in the proof of Theorem 1(l). Let $I$ be an instance with $n'$ jobs, $m$ machines, processing times $p_j$ and precedence relation $<$, and let $y' \in \mathbb N$ (the paper chooses $0 \le y' \le n'p_*$). Define
--
--   $$n'' = (n'-1)\,y', \qquad n = n' + n'', \qquad y = n y' + \tfrac12 n''(n''+1).$$
--
--   The new instance keeps the $n'$ jobs of $I$, the $m$ machines, the processing times and the precedence constraints of $I$, and adds $n''$ jobs $J_{n'+k}$, $k = 1,\dots,n''$, with
--
--   $$p_{n'+k,1} = 1, \qquad J_j < J_{n'+k} \quad (j = 1,\dots,n'+k-1),$$
--
--   so each added job must follow every original job and every earlier added job. No other precedence constraints are added.
--
--   The threshold $y$ is an integer, since $n''(n''+1)$ is even; it is given both as a rational number, exactly as printed, and as a natural number (with exact division by $2$).
--
--   **Formalization Note** With 0-based indices the added jobs are $n', \dots, n'+n''-1$; an added job $k$ has processing time $1$ and is preceded by exactly the jobs with index smaller than $k$. The difference $n'-1$ is computed in $\mathbb N$; under the paper's choice $y' \le n'p_*$, $n' = 0$ forces $y' = 0$, so the truncation never changes $n''$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, proof of Theorem 1(l)

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model

namespace SchedComplexity.PrecChain

/-- The number of added jobs in the proof of Theorem 1(l) (p. 9): `n'' = (n' − 1) y'`. The
paper chooses `0 ≤ y' ≤ n' p_*`, so `n' = 0` forces `y' = 0` and the truncated subtraction of
`ℕ` never matters. -/
def nNew (n' y' : ℕ) : ℕ := (n' - 1) * y'

/-- The threshold `y = n y' + ½ n'' (n'' + 1)` of the proof of Theorem 1(l) (p. 9), with
`n = n' + n''`, computed in `ℚ` exactly as printed. -/
def chainThresholdQ (n' y' : ℕ) : ℚ :=
  ((n' + nNew n' y' : ℕ) : ℚ) * y' + (1 / 2 : ℚ) * (nNew n' y' : ℚ) * ((nNew n' y' : ℚ) + 1)

/-- The same threshold as a natural number: `n'' (n'' + 1)` is even, so the division by `2` is
exact and `(chainThreshold n' y' : ℚ) = chainThresholdQ n' y'`. -/
def chainThreshold (n' y' : ℕ) : ℕ :=
  (n' + nNew n' y') * y' + nNew n' y' * (nNew n' y' + 1) / 2

/-- The instance of `P` built from an instance `I` of `P'` and a threshold `y'` in the proof of
Theorem 1(l) (p. 9): keep the `n'` jobs of `I`, the `m` machines, the processing times and the
precedence constraints of `I`, and add `n'' = (n' − 1) y'` jobs `J_{n'+k}` (`k = 1, …, n''`)
with `p_{n'+k,1} = 1` and `J_j < J_{n'+k}` for `j = 1, …, n' + k − 1`. With 0-based indices the
added jobs are `n', …, n' + n'' − 1`; a job `k ≥ n'` has processing time `1` and is preceded by
exactly the jobs `j < k`. No job is required to precede a job of `I` except as in `I`. -/
def chainExtend (I : Instance) (y' : ℕ) : Instance where
  n := I.n + nNew I.n y'
  m := I.m
  p := fun j => if h : (j : ℕ) < I.n then I.p ⟨j, h⟩ else 1
  prec := fun j k =>
    if hk : (k : ℕ) < I.n then
      (if hj : (j : ℕ) < I.n then I.prec ⟨j, hj⟩ ⟨k, hk⟩ else false)
    else decide ((j : ℕ) < k)

end SchedComplexity.PrecChain


