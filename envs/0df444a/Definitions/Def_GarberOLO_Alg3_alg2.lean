-- Prove2me | Definitions.Def_GarberOLO_Alg3_alg2
-- name    : GarberOLO_Alg3_alg2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:15.141794+00:00
-- url     : https://prove2.me/theorems/cbb5a3de-a963-4604-bf95-7d784105fb12
-- title:
--   Algorithm 2: (infeasible) projection onto $\mathrm{CH}(\alpha K)$
-- statement:
--   Run the iterates $\tilde y_1, \tilde y_2, \dots$ of Algorithm 2 on $(y, \varepsilon)$. If pass $k$ is the first at which the Separation-or-Decomposition procedure returns decomposition data $(v_i, s_i)_{i \le N}$ (with $N = N(\tilde y_k)$), Algorithm 2 returns
--
--   1. the point $\tilde y = \tilde y_k$,
--   2. the oracle outputs $(v_i, s_i)_{i\le N}$ and the weights $a = \mathrm{sel}(N, \tilde y_k, (v_i)_i)$, an optimal solution of Problem (5),
--   3. the loop count $k$ and the total number of oracle calls over passes $1, \dots, k$.
--
--   This is the projection step of Algorithm 3: $\tilde y$ satisfies the infeasible-projection inequality (3) for $\mathrm{CH}(\alpha K)$, and $\sum_i a_i v_i$ is within $3\varepsilon$ of $\tilde y$ (Lemma 7).
--
--   **Formalization Note** If the loop never returns, the record is a placeholder; every theorem that reads it states or assumes termination, so the placeholder is never used. The selector and the constant $c$ of $N$ are parameters.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 2, p. 12

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_sepOrDec
import Definitions.Def_GarberOLO_Alg3_Nprescribed
import Definitions.Def_GarberOLO_Alg3_alg2Iter
import Definitions.Def_GarberOLO_Alg3_Alg2Out

namespace GarberOLO.Alg3

open Classical in
/-- **Algorithm 2: (infeasible) projection onto CH(αK)**, with its output and oracle count.
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Algorithm 2, p. 12: "1: input: point y ∈ ℝᵈ, tolerance ε > 0 2: ỹ ← y/max{1, ‖y‖/(αR)} 3: for t = 1 . . . do 4: call the Separation-or-Decompostion procedure described in Lemma 5 with parameters (ỹ, ε) 5: if the procedure outputs a separating hyperplane w then 6: ỹ ← ỹ − εw 7: else 8: let (a₁, …, a_N), {(v₁, s₁), …, (v_N, s_N)} be the decomposition returned, where N is as prescribed in Lemma 5. 9: return ỹ, (a₁, …, a_N), {(v₁, s₁), …, (v_N, s_N)}".

Let `ỹᵢ := alg2Iter S OK c ε y i`, `Nᵢ := Nprescribed S c ε ỹᵢ` and
`outᵢ := sepOrDec S OK ỹᵢ ε Nᵢ`. If some pass returns a decomposition, let `k₀` be the first
such `i`; then `alg2 S OK sel c ε y` has `yt = ỹ_{k₀}`, `N = N_{k₀}`, `vs = out_{k₀}.vs`,
`a = sel N ỹ_{k₀} (v₁, …, v_N)` (an optimal solution of Problem (5) when `sel` is an optimal
selector), `loops = k₀ + 1`, and `calls = Σ_{i ≤ k₀} outᵢ.calls`.

**Formalization Note.** If the loop never returns, the output is a placeholder
(`N = 0`, `yt = y`, `loops = calls = 0`). Every theorem of the mission that reads `alg2` also
states, or is guarded by, termination (`alg2Terminates`), so the placeholder is never used. The
selector `sel` (Reading 5) and the constant `c` (Reading 2) are parameters. -/
noncomputable def alg2 {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ)
    (c ε : ℝ) (y : EuclideanSpace ℝ (Fin d)) : Alg2Out d :=
  if h : ∃ i : ℕ, (sepOrDec S OK (alg2Iter S OK c ε y i) ε
      (Nprescribed S c ε (alg2Iter S OK c ε y i))).isSep = false then
    { N := Nprescribed S c ε (alg2Iter S OK c ε y (Nat.find h))
      yt := alg2Iter S OK c ε y (Nat.find h)
      vs := (sepOrDec S OK (alg2Iter S OK c ε y (Nat.find h)) ε
        (Nprescribed S c ε (alg2Iter S OK c ε y (Nat.find h)))).vs
      a := sel (Nprescribed S c ε (alg2Iter S OK c ε y (Nat.find h)))
        (alg2Iter S OK c ε y (Nat.find h))
        (fun j => ((sepOrDec S OK (alg2Iter S OK c ε y (Nat.find h)) ε
          (Nprescribed S c ε (alg2Iter S OK c ε y (Nat.find h)))).vs j).1)
      loops := Nat.find h + 1
      calls := ∑ i ∈ Finset.range (Nat.find h + 1),
        (sepOrDec S OK (alg2Iter S OK c ε y i) ε (Nprescribed S c ε (alg2Iter S OK c ε y i))).calls }
  else
    { N := 0, yt := y, a := Fin.elim0, vs := Fin.elim0, loops := 0, calls := 0 }

end GarberOLO.Alg3


