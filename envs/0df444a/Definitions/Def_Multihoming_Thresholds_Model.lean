-- Prove2me | Definitions.Def_Multihoming_Thresholds_Model
-- name    : Multihoming_Thresholds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:59.923032+00:00
-- url     : https://prove2.me/theorems/69ab7e33-0805-462b-a551-7ec7129c4ffd
-- title:
--   §3.2, (14), (15), (24), (26), A1, PDF pp. 17–20, 27 — symmetric multihoming demand, reaction function, price, profit, ranges and thresholds
-- statement:
--   This file fixes the symmetric version of the Hotelling model with endogenous multihoming of Foros, Kind and Stähler. Two firms $i \in \{0,1\}$ sit at the ends of a unit Hotelling line; $t>0$ is the mismatch (transport) cost, $\mu \ge 0$ the strength of the network effect, and both goods carry the same amount $e$ of exclusive features. All quantities are real-valued functions of these parameters.
--
--   1. **Multihoming demand (14).** Under fulfilled expectations, the demand for good $i$ when some consumers buy both goods is
--   $$x_i^M(p_i,p_j)=\frac{\mu}{t+\mu}+t\,\frac{e-p_i}{t^2-\mu^2}-\mu\,\frac{e-p_j}{t^2-\mu^2}.$$
--   2. **Reaction function (15).** $p_i^M(p_j)=\dfrac{t\mu-\mu^2+te}{2t}+\mu\,\dfrac{p_j-e}{2t}$.
--   3. **Symmetric price (26).** $p^M=\dfrac{(t-\mu)(\mu+e)}{2t-\mu}$.
--   4. **Symmetric profit.** $\pi^M=p^M\cdot x_i^M(p^M,p^M)$, price times the demand (14) at the symmetric prices (marginal costs are zero).
--   5. **Partial-multihoming range (24).** $\underline e=\dfrac{(t-\mu)(2t+\mu)}{2t}$ and $\overline e=\dfrac{2t^2-\mu^2}{t}$; partial multihoming is possible for $e\in[\underline e,\overline e]$.
--   6. **Thresholds.** The price threshold $e_p\equiv 2(t-\mu)$ (PDF p. 20) and the profit threshold of Appendix A1,
--   $$e_\pi=\frac{4t^2(t-\mu)+2t(2t-\mu)\sqrt{t^2-\mu^2}}{4t^2-3t\mu+\mu^2}.$$
--
--   The case "without network effects" is the same functions evaluated at $\mu=0$: $p^M=e/2$ and $\pi^M=e^2/(4t)$.
--
--   **Formalization Note** The profit is defined from the model (price times demand (14)); its closed form (26) is a separate theorem. The overlapping features $o$ cancel from every object and are not a parameter. Every denominator is positive when $0\le\mu<t$; the definitions are total functions, and the theorems that use them carry those hypotheses. $e_\pi$ is the printed closed form with the real square root, not the root of an equation.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF pp. 17, 19, 20, 27 (printed pp. 11, 13, 14, 21), (14), (15), (24), (26), e_p (p. 14), e_π (Appendix A1)

import Mathlib

namespace Multihoming.Thresholds

/-- (14), PDF 17, with symmetric exclusive features eᵢ = eⱼ = e: the multihoming demand
for good i at prices (pᵢ, pⱼ) under fulfilled expectations. -/
noncomputable def demandM (t μ e pi pj : ℝ) : ℝ :=
  μ / (t + μ) + t * (e - pi) / (t ^ 2 - μ ^ 2) - μ * (e - pj) / (t ^ 2 - μ ^ 2)

/-- (15), PDF 17, with eᵢ = eⱼ = e: firm i's reaction function to the rival price pⱼ. -/
noncomputable def reactM (t μ e pj : ℝ) : ℝ :=
  (t * μ - μ ^ 2 + t * e) / (2 * t) + μ * (pj - e) / (2 * t)

/-- (26), PDF 20: the symmetric partial-multihoming price pᴹ. -/
noncomputable def pM (t μ e : ℝ) : ℝ := (t - μ) * (μ + e) / (2 * t - μ)

/-- The symmetric profit πᴹ = pᴹ · xᴹ, with xᴹ the demand (14) at the symmetric prices. -/
noncomputable def piM (t μ e : ℝ) : ℝ := pM t μ e * demandM t μ e (pM t μ e) (pM t μ e)

/-- (24), PDF 19: lower end e̲ of the partial-multihoming range. -/
noncomputable def eLow (t μ : ℝ) : ℝ := (t - μ) * (2 * t + μ) / (2 * t)

/-- (24), PDF 19: upper end ē of the partial-multihoming range. -/
noncomputable def eBar (t μ : ℝ) : ℝ := (2 * t ^ 2 - μ ^ 2) / t

/-- PDF 20: the price threshold e_p ≡ 2(t − μ). -/
def eP (t μ : ℝ) : ℝ := 2 * (t - μ)

/-- Appendix A1, PDF 27: the profit threshold e_π. -/
noncomputable def ePi (t μ : ℝ) : ℝ :=
  (4 * t ^ 2 * (t - μ) + 2 * t * (2 * t - μ) * Real.sqrt (t ^ 2 - μ ^ 2)) /
    (4 * t ^ 2 - 3 * t * μ + μ ^ 2)

end Multihoming.Thresholds


