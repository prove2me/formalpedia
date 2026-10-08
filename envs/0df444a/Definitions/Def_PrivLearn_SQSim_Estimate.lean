-- Prove2me | Definitions.Def_PrivLearn_SQSim_Estimate
-- name    : PrivLearn_SQSim_Estimate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:46.513999+00:00
-- url     : https://prove2.me/theorems/74d6ba63-4a46-48df-a753-70f23b5b7cae
-- title:
--   The quantities of algorithm B_{R,ε} (p. 22) — p(w), the rescaled query g, the estimate p̃, τ = β/(3e^{2ε}t) and φ = β/(3t)
-- statement:
--   Fix a probability distribution $P$ on $D$, a randomizer $R$ with discrete output $W$, a reference input $u_0\in D$ (the paper's arbitrary input $\mathbf 0$), $\varepsilon>0$, $\beta>0$ and $t\ge1$.
--
--   1. The **target probability** of an output $w$ is $p(w)=\Pr_{z_i\sim P}[R(z_i)=w]=\mathbb E_{z_i\sim P}\Pr[R(z_i)=w]$.
--   2. For a weight function $r:D\to\mathbb R$ the **rescaled query** and the **estimate** obtained from an answer $v$ are
--
--   $$g(u)=\frac{r(u)-r(u_0)}{r(u_0)\,(e^{\varepsilon}-e^{-\varepsilon})},\qquad \tilde p=v\,r(u_0)\,(e^{\varepsilon}-e^{-\varepsilon})+r(u_0).$$
--
--   With $r(u)=\Pr[R(u)=w]$ these are Steps 2 and 3 of the algorithm $\mathcal B_{R,\varepsilon}$; with the weights $r_1,r_2$ of the proof of Claim 5.10 they are the queries $g_1,g_2$.
--   3. The **tolerance** is $\tau=\beta/(3e^{2\varepsilon}t)$ and the **accuracy** is $\varphi=\beta/(3t)$.
--
--   These names keep the statements of display (5) and of the proof of Claim 5.10 readable.
--
--   **Formalization Note.** Divisions follow Lean's convention $x/0=0$; every theorem that uses them assumes $\varepsilon>0$, $t\ge1$ and $r(u_0)>0$, where the formulas are the paper's.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 22 (proof of Claim 5.9, algorithm B_{R,ε}, display (5)), p. 24 (proof of Claim 5.10, queries g_1, g_2)

import Mathlib

namespace PrivLearn.SQSim

open MeasureTheory

/-- Proof of Claim 5.9 (p. 22): the target probability `p(w) = Pr_{z_i∼P}[R(z_i) = w]
= E_{z_i∼P} Pr[R(z_i) = w]` of the output `w` of the randomizer `R` applied to a random entry. -/
noncomputable def pTarget {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    (R : Dom → PMF W) (w : W) : ℝ :=
  ∫ u, (R u w).toReal ∂P

/-- Step 2 of `B_{R,ε}` (p. 22) and the queries `g₁, g₂` of Claim 5.10 (p. 24): the rescaled query
`g(u) = (r(u) − r(u₀)) / (r(u₀)(e^ε − e^{−ε}))` built from a weight `r : Dom → ℝ` and the reference
input `u₀` (the paper's "0"). With `r(u) = Pr[R(u) = w]` it is the query of Claim 5.9. -/
noncomputable def sqQuery {Dom : Type*} (r : Dom → ℝ) (u₀ : Dom) (ε : ℝ) (u : Dom) : ℝ :=
  (r u - r u₀) / (r u₀ * (Real.exp ε - Real.exp (-ε)))

/-- Step 3 of `B_{R,ε}` (p. 22): the estimate `p̃ = v · r(u₀)(e^ε − e^{−ε}) + r(u₀)` obtained from
the oracle's answer `v` to the query `sqQuery r u₀ ε`. -/
noncomputable def sqEstimate {Dom : Type*} (r : Dom → ℝ) (u₀ : Dom) (ε v : ℝ) : ℝ :=
  v * r u₀ * (Real.exp ε - Real.exp (-ε)) + r u₀

/-- Step 2 of `B_{R,ε}` (p. 22): the tolerance `τ = β / (3 e^{2ε} t)`. -/
noncomputable def simTolerance (ε β : ℝ) (t : ℕ) : ℝ :=
  β / (3 * Real.exp (2 * ε) * t)

/-- Display (5) (p. 22): the accuracy `φ = β / (3t)`. -/
noncomputable def simPhi (β : ℝ) (t : ℕ) : ℝ :=
  β / (3 * t)

end PrivLearn.SQSim


