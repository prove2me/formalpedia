-- Prove2me | Definitions.Def_CEPolytopeHard_condVar
-- name    : CEPolytopeHard_condVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:38.542951+00:00
-- url     : https://prove2.me/theorems/993016e2-4fe1-41ce-a807-627dc9745099
-- title:
--   Conditional mean $\bar x_i(s)$ and averaged conditional variance $V(s)$
-- statement:
--   For points $x_1, \dots, x_k \in \mathbb R^d$, a stochastic matrix $P$ with stationary distribution $\mu$ and $0 < s \le 1$,
--   $$
--   \bar x_i(s) := \mathbb E_{j \sim P_i(s)} x_j, \qquad V(s) := \mathbb E_{i \sim \mu,\, j \sim P_i(s)} \|x_j - \bar x_i(s)\|_2^2 ,
--   $$
--   with the normalized norm. $V(s)$ is the variance of $x_j$ under $j \sim P_i(s)$, averaged over $i \sim \mu$; Section 3.2 shows that it is small at a well-chosen scale.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 3.2, p.16

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_geo

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **conditional mean `x̄_i(s)`** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Section 3.2, p.16: "x̄_i(s) := E_{j∼P_i(s)} x_j") of
points `x_1, …, x_k ∈ ℝ^ι`. -/
noncomputable def xbar {k : ℕ} {ι : Type*} (P : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ι → ℝ)
    (s : ℝ) (i : Fin k) : ι → ℝ :=
  ∑ j, geo P s i j • x j

/-- The **averaged conditional variance `V(s)`** (Section 3.2, p.16: "V(s) := E_{i∼µ,j∼P_i(s)}
∥x_j − x̄_i(s)∥₂²"), with the normalized norm `nnorm` (p.9). -/
noncomputable def condVar {k : ℕ} {ι : Type*} [Fintype ι] (P : Matrix (Fin k) (Fin k) ℝ)
    (μ : Fin k → ℝ) (x : Fin k → ι → ℝ) (s : ℝ) : ℝ :=
  ∑ i, μ i * ∑ j, geo P s i j * nnorm (x j - xbar P x s i) ^ 2

end CEPolytopeHard


