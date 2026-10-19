-- Prove2me | Definitions.Def_PersuadeEarly_Private_PrivateMech
-- name    : PersuadeEarly_Private_PrivateMech
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:29.343119+00:00
-- url     : https://prove2.me/theorems/26462e7e-79fc-4564-95c2-847789ae9804
-- title:
--   §5.2, pp. 16–17 — the personalized mechanism (PS1)–(PS2): $\sigma_H$ (13), (14), $\bar v$ (15), $R_{private}$ (16)
-- statement:
--   This file defines the paper's personalized Buy/Wait/No mechanism.
--
--   Let $p_1=\bar F^{-1}(q_L)$ (PS1). For a period-2 price $p_2$, the H-state *Buy* probability (13) is
--   $$\sigma_H(v)=\min\Big\{\frac{P(L)}{P(H)}\,\frac{v-p_1}{p_1-p_2},\,1\Big\},$$
--   and (15) $\bar v=\sup\{v\in[0,b]:\sigma_H(v)<1\}$. The price condition (14) on $p_2$ is
--   $$\bar F(p_2)-p_2 f(p_2)=\bar F(\bar v),$$
--   i.e. $\frac{d}{dp_2}\,p_2\bar F(p_2)=\bar F(\bar v)$.
--
--   The mechanism (PS2), at prices $p_1$ and $p_2$, uses a single latent signal:
--   1. if $Q=q_L$: *Buy* to customers with $v\ge p_1$, *No* to all others;
--   2. if $Q=q_H$: *Buy* with probability $\sigma_H(v)$, independently across customers, and *Wait* otherwise, to customers with $v\ge p_1$; *Wait* to $p_2\le v<p_1$; *No* to $v<p_2$.
--
--   Its revenue formula (16) is
--   $$R_{private}=P(H)p_2\bar F(p_2)+P(H)(p_1-p_2)\bar F(\bar v)+P(L)\int_{p_1}^{\bar v}(v-p_1)f(v)\,dv+P(L)p_1q_L.$$
--
--   The goal theorem asserts that this mechanism, with $p_2$ solving (14), is optimal when $q_L\le\bar F(p^m)$.
--
--   **Formalization Note** The derivative in (14) is written as $\bar F(p_2)-p_2f(p_2)$, the paper's own expansion (p. 45). (PS2)(a) says "valuations greater than $p_1$"; the mission uses $v\ge p_1$ as in (b)(i); the two differ on a null set.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 16, (13); p. 17, (PS1)–(PS2), (14)–(16)

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism

open MeasureTheory Set

namespace PersuadeEarly.Private

variable (M : Model)

/-- The period-1 price of the private mechanism, `p1 = F̄^{-1}(qL)` ((PS1), p. 17). -/
noncomputable def psP1 : ℝ := M.FbarInv M.qL

/-- The H-state *Buy* probability (13), p. 16:
`σ_H(v) = min{ P(L)/P(H) · (v − p1)/(p1 − p2), 1 }`, with `p1 = F̄^{-1}(qL)`. -/
noncomputable def sigmaH (p2 v : ℝ) : ℝ :=
  min (M.pL / M.pH * ((v - psP1 M) / (psP1 M - p2))) 1

/-- `v̄ = sup{v ∈ V : σ_H(v) < 1}` (15), p. 17, with `V = [0, b]`. -/
noncomputable def vbar (p2 : ℝ) : ℝ :=
  sSup {v ∈ Icc 0 M.b | sigmaH M p2 v < 1}

/-- The price condition (14), p. 17, `d/dp2 [p2 F̄(p2)] = F̄(v̄)`, with the derivative written as
`F̄(p2) − p2 f(p2)`.

**Formalization Note** This is the paper's own expansion of the derivative (p. 45); the
two-sided derivative of `F̄` exists on `(0, b)`, where the root lies. -/
def PS14 (p2 : ℝ) : Prop :=
  M.Fbar p2 - p2 * M.f p2 = M.Fbar (vbar M p2)

/-- The private signaling mechanism (PS2), p. 17, at prices `p1 = F̄^{-1}(qL)` and `p2`, with a
single (trivial) latent index:
* state `L`: *Buy* to customers with `v ≥ p1`, *No* to all others;
* state `H`: *Buy* with probability `σ_H(v)` and *Wait* otherwise to `v ≥ p1`; *Wait* to
  `p2 ≤ v < p1`; *No* to `v < p2`.

**Formalization Note** (PS2)(a) says "valuations greater than p1"; the mission uses `v ≥ p1`, as in
(b)(i). The two differ on the null set `{p1}`. -/
noncomputable def psMech (p2 : ℝ) : Mech M 1 where
  p1 := psP1 M
  p2 := p2
  piH := fun _ => 1
  piL := fun _ => 1
  buyH := fun _ v => if psP1 M ≤ v then sigmaH M p2 v else 0
  buyL := fun _ v => if psP1 M ≤ v then 1 else 0
  waitH := fun _ v => if psP1 M ≤ v then 1 - sigmaH M p2 v else if p2 ≤ v then 1 else 0
  waitL := fun _ _ => 0

/-- The revenue formula (16), p. 17:
`R_private = P(H) p2 F̄(p2) + P(H)(p1 − p2) F̄(v̄) + P(L) ∫_{p1}^{v̄} (v − p1) dF(v) + P(L) p1 qL`,
with `p1 = F̄^{-1}(qL)` and `dF(v) = f(v) dv`. -/
noncomputable def Rprivate (p2 : ℝ) : ℝ :=
  M.pH * p2 * M.Fbar p2 + M.pH * (psP1 M - p2) * M.Fbar (vbar M p2) +
    M.pL * (∫ v in (psP1 M)..(vbar M p2), (v - psP1 M) * M.f v) + M.pL * psP1 M * M.qL

end PersuadeEarly.Private


