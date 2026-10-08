-- Prove2me | Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage
-- name    : MitigateSupplyRisk_Improvement_FirstStage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:09.271189+00:00
-- url     : https://prove2.me/theorems/67dd16fd-c76f-401c-99be-3861d121a308
-- title:
--   §3.2 and §4.2.1, Eq. (7), pp. 493, 496 — improvement data (θ, m, a⁰, z) and the first-stage profit Π₁(a) = −m z(a) + θ Π₂*(a) + (1 − θ) Π₂*(a⁰)
-- statement:
--   This file adds the first stage of the paper's model: the firm may exert effort to raise its supplier's reliability index before ordering.
--
--   **Data.** The supplier's initial reliability index is $a^0$. Effort $z \ge 0$ costs $m z$ and succeeds with probability $\theta$; on success the index becomes $a(z) \ge a^0$, otherwise it stays at $a^0$. The paper takes $a(\cdot)$ concave increasing with $a(0) = a^0$, and then reparametrizes the first stage by the target index: $z(a)$ is the effort needed to reach index $a \ge a^0$. The standing assumptions (`Effort.Assumptions`) are
--   1. $0 \le \theta \le 1$ and $m \ge 0$;
--   2. $z$ is convex and nondecreasing on $[a^0, \infty)$ with $z(a^0) = 0$.
--
--   **First-stage profit.** With early commitment to this supplier (§4.2.1), the firm's expected profit as a function of the target index $a \ge a^0$ is Eq. (7):
--   $$\Pi_1(a) = -m\, z(a) + \theta\, \Pi_2^*(a) + (1-\theta)\, \Pi_2^*(a^0),$$
--   where $\Pi_2^*$ is the optimal second-stage profit of the model file. The firm's improvement problem is $\max_{a \ge a^0} \Pi_1(a)$.
--
--   **Formalization Note** Taking $z$ as primitive assumes every index $a \ge a^0$ is reachable by finite effort, as in the paper's example $a(z) = a^0 + \log(1+z)$. $\Pi_1$ is defined for every real $a$ but only its restriction to $[a^0, \infty)$ is used.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 493 (PDF 5), §3.2 and Eqs. (4)–(5); p. 496 (PDF 8), §4.2.1, Eq. (7)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model

open Set

namespace MitigateSupplyRisk.Improvement

/-- Improvement data of §3.2 (p. 493), in the paper's reparametrisation by the reliability index:
initial index `a0` (= `a_i⁰`), success probability `θ`, unit effort cost `m`, and the effort
`z a` needed to reach index `a ≥ a0`. -/
structure Effort where
  θ : ℝ
  m : ℝ
  a0 : ℝ
  z : ℝ → ℝ

/-- Standing assumptions on the improvement data (p. 493): `θ ∈ [0, 1]`, `m ≥ 0`, and `z` is convex,
nondecreasing on `[a0, ∞)` with `z a0 = 0` ("`z_i(a_i)` is a convex increasing function of `a_i`",
the inverse of the concave increasing `a_i(z_i)` with `a_i(0) = a_i⁰`). -/
structure Effort.Assumptions (I : Effort) : Prop where
  θ_nonneg : 0 ≤ I.θ
  θ_le_one : I.θ ≤ 1
  m_nonneg : 0 ≤ I.m
  z_convex : ConvexOn ℝ (Ici I.a0) I.z
  z_mono : MonotoneOn I.z (Ici I.a0)
  z_a0 : I.z I.a0 = 0

/-- First-stage expected profit of early commitment, Eq. (7) (p. 496):
`Π₁(a) = −m z(a) + θ Π₂*(a) + (1 − θ) Π₂*(a⁰)`, meaningful for `a ≥ a0`. -/
noncomputable def Pi1 (M : Model) (I : Effort) (a : ℝ) : ℝ :=
  -I.m * I.z a + I.θ * M.Pi2star a + (1 - I.θ) * M.Pi2star I.a0

end MitigateSupplyRisk.Improvement


