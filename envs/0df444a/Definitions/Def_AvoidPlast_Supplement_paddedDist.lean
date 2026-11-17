-- Prove2me | Definitions.Def_AvoidPlast_Supplement_paddedDist
-- name    : AvoidPlast_Supplement_paddedDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:56:33.818076+00:00
-- url     : https://prove2.me/theorems/699b2438-eebd-493b-ae2a-afc2c6099b1b
-- title:
--   The padded distribution $XY^{T_0}$ (Definition 5.3)
-- statement:
--   For ensembles $X,Y$ and $T_0:\mathbb N\to\mathbb N$, a sample of $(XY^{T_0})_N$ is drawn as follows: let $n$ be the largest integer with $N\ge n+T_0(n)$, draw $r_1\sim X_n$ and $r_2\sim Y_{N-n}$, and output $r_1\circ r_2\in\{0,1\}^N$.
--
--   When $X$ and $Y$ are uniform, $XY^{T_0}$ is uniform. Theorem 5.4 assumes hardness of Avoid over this distribution.
--
--   **Formalization Note** When no $n\le N$ satisfies $N\ge n+T_0(n)$ (only for $N<T_0(0)$) the source leaves the distribution undefined; here $n=0$. Only finitely many lengths are affected and every use is asymptotic.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_Ensemble

namespace AvoidPlast.Supplement

open AvoidPlast

open Classical in
/-- The padded distribution `XY^{T₀}` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.3, p.22): to sample at length
`N`, let `n` be the largest integer with `N ≥ n + T₀(n)`, draw `r₁ ∼ X_n`, `r₂ ∼ Y_{N-n}`, and
output `r₁ ∘ r₂`.

**Formalization Note** When no `n ≤ N` has `n + T₀(n) ≤ N` (only `N < T₀(0)`), the definition
is undefined in the source; here `n = 0`. Only finitely many lengths are affected, and every
statement about this distribution is asymptotic. -/
noncomputable def paddedDist (X Y : Ensemble) (T₀ : ℕ → ℕ) (N : ℕ) : PMF (List Bool) :=
  let n := Nat.findGreatest (fun n => n + T₀ n ≤ N) N
  (X.dist n).bind fun r₁ => (Y.dist (N - n)).map fun r₂ => r₁ ++ r₂

end AvoidPlast.Supplement


