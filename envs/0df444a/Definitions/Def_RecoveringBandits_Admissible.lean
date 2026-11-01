-- Prove2me | Definitions.Def_RecoveringBandits_Admissible
-- name    : RecoveringBandits_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:29.920763+00:00
-- url     : https://prove2.me/theorems/d419669c-2b88-4487-83ef-2b6a203c1351
-- title:
--   Admissible recovering-rewards instance (Assumptions 1–2)
-- statement:
--   There are $N$ arms. For each arm $i$ the **recovery function** $R_i:\{0,1,2,\dots\}\to\mathbb R$ gives the mean reward $R_i(d)$ of pulling arm $i$ when it has been idle for $d$ periods. An instance is **admissible** with bound $R_{\max}$ when, for every arm $i$ and every $d\ge 0$,
--
--   1. $R_i(0)=0$;
--   2. $R_i(d)\ge 0$;
--   3. $R_i$ is non-decreasing (Assumption 1, monotonicity);
--   4. $R_i(d)\le R_{\max}$ (Assumption 2, boundedness).
--
--   These are the standing assumptions of the model of recovering rewards; no concavity or parametric shape is assumed.
--
--   **Formalization Note** Assumption 2 bounds the random rewards; only their means enter the offline problem, so it is stated for the means. Assumption 2′ (finite-time recovery) is not included: the offline guarantee does not use it. The arms are indexed by `Fin N`, and `ArmAdmissible` is the condition for one arm.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §2, Assumptions 1–2, pp.6–7

import Mathlib

namespace RecoveringBandits

/-- **One arm's recovery function is admissible.**
Simchi-Levi–Zheng–Zhu, *Offline Planning and Online Learning under Recovering Rewards*,
arXiv:2106.14813v2, §2, pp.6–7 (PDF 6–7): the mean rewards `{R_i(d)}_{d=0,1,2,…}` are
"non-negative scalars", "We let `R_i(0) = 0` for completeness", Assumption 1 (Monotonicity: `R_i`
is non-decreasing in `d`), and Assumption 2 (Boundedness: rewards bounded by a known constant
`Rmax`).

`r d` is the mean reward of pulling the arm when it has been idle for `d` periods.

**Formalization Note.** Assumption 2 bounds the random rewards by `Rmax`; only the mean rewards
enter the offline problem (p.7: "The randomness in the system does not impact the policy design
for the offline problem"), so the assumption is stated for the means, `r d ≤ Rmax`.
Assumption 2′ (finite-time recovery) is deliberately not part of this predicate: Theorem 1 does
not use it (p.7). -/
def ArmAdmissible (r : ℕ → ℝ) (Rmax : ℝ) : Prop :=
  r 0 = 0 ∧ (∀ d, 0 ≤ r d) ∧ Monotone r ∧ ∀ d, r d ≤ Rmax

/-- **An admissible recovering-rewards instance** (arXiv:2106.14813v2, §2, pp.6–7): `N` arms indexed
by `Fin N`, recovery functions `R i : ℕ → ℝ`, each admissible with the common bound `Rmax`
(`ArmAdmissible`).

**Formalization Note.** The paper fixes `K ≤ N` and `N ≥ 1` in §2; neither is part of this
predicate, and each statement says which of them it needs. -/
def Admissible {N : ℕ} (R : Fin N → ℕ → ℝ) (Rmax : ℝ) : Prop :=
  ∀ i, ArmAdmissible (R i) Rmax

end RecoveringBandits


