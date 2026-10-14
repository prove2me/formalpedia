-- Prove2me | Definitions.Def_Multihoming_Hump_Model
-- name    : Multihoming_Hump_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:57.854598+00:00
-- url     : https://prove2.me/theorems/f2eb3c41-6c71-471a-af6f-8bdc9fb2e973
-- title:
--   §3.2, (14), (15), (26), App. A1, PDF pp. 17, 20, 28 — multihoming demand, reaction function, symmetric price and profit, roots r₁, r₂
-- statement:
--   The symmetric multihoming model of Foros, Kind and Stähler. Two firms $i \in \{0,1\}$ sit at the ends of a Hotelling line of unit length with mismatch cost $t>0$; buying a good gives a network benefit of strength $\mu \ge 0$ times its expected number of users; both goods carry the same amount $e$ of exclusive features. All objects below are real-valued functions of real parameters.
--
--   1. **Multihoming demand (14).** Under fulfilled expectations, the demand for good $i$ at own price $p_i$ and rival price $p_j$, when some consumers buy both goods, is
--   $$x_i^M(p_i,p_j)=\frac{\mu}{t+\mu}+t\,\frac{e-p_i}{t^2-\mu^2}-\mu\,\frac{e-p_j}{t^2-\mu^2}.$$
--   2. **Reaction function (15).**
--   $$p_i^M(p_j)=\frac{t\mu-\mu^2+te}{2t}+\mu\,\frac{p_j-e}{2t}.$$
--   3. **Symmetric price and profit (26).**
--   $$p^M=\frac{(t-\mu)(\mu+e)}{2t-\mu},\qquad \pi^M=\frac{t\,(t-\mu)\,(e+\mu)^2}{(t+\mu)\,(2t-\mu)^2}.$$
--   4. **The roots of $d\pi^M/d\mu$ (Appendix A1).**
--   $$r_1=\frac{t\sqrt{3(4t^2-e^2)}-2t^2+et}{2(e+t)},\qquad r_2=\frac{t\left(2t-e+\sqrt{3(4t^2-e^2)}\right)}{2(e+t)}.$$
--
--   The demand (14), the reaction function (15) and the price $p^M$ are taken from the shared module `Multihoming.Thresholds.Model` (as `demandM`, `reactM`, `pM`); this module adds $\pi^M$, $r_1$ and $r_2$. These are the objects of Proposition 3: the price $p^M$ and profit $\pi^M$ as functions of the network-effect strength $\mu$, and the points that locate the profit's peak.
--
--   **Formalization Note** The functions are total: Lean evaluates division by zero to $0$ and the square root of a negative number to $0$. Every statement that uses them keeps $t>0$, $0\le\mu<t$ (for the demand) or $0\le\mu\le t$ (for $p^M$, $\pi^M$), and $0\le e<2t$ (for $r_1,r_2$), so all denominators are positive and the square-root argument is positive. The profit $\pi^M$ is the printed closed form (26), not price times demand, because the paper studies it on the closed interval $\mu\in[0,t]$ and the demand (14) divides by $t^2-\mu^2=0$ at $\mu=t$; a separate theorem shows that $\pi^M=p^M x^M$ on $[0,t)$. The overlapping features $o$ cancel from all these objects and are not a parameter. The derivation of (14) from the consumer model and the full pricing game are not formalized.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF pp. 17, 20, 28 (printed pp. 11, 14, 22), (14), (15), (26), Appendix A1 definitions of r₁, r₂

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Hump

/-- (26), PDF p. 20: symmetric partial-multihoming profit
πᴹ = t(t − μ)(e + μ)² / ((t + μ)(2t − μ)²), as printed (defined on all of μ ∈ [0, t]). -/
noncomputable def piM (t μ e : ℝ) : ℝ :=
  t * (t - μ) * (e + μ) ^ 2 / ((t + μ) * (2 * t - μ) ^ 2)

/-- Appendix A1, PDF p. 28: r₁ = (t√(3(4t² − e²)) − 2t² + et)/(2(e + t)). -/
noncomputable def r1 (t e : ℝ) : ℝ :=
  (t * Real.sqrt (3 * (4 * t ^ 2 - e ^ 2)) - 2 * t ^ 2 + e * t) / (2 * (e + t))

/-- Appendix A1, PDF p. 28: r₂ = t(2t − e + √(3(4t² − e²)))/(2(e + t)). -/
noncomputable def r2 (t e : ℝ) : ℝ :=
  t * (2 * t - e + Real.sqrt (3 * (4 * t ^ 2 - e ^ 2))) / (2 * (e + t))

end Multihoming.Hump


