-- Prove2me | Definitions.Def_PersuadeEarly_Private_Valuation
-- name    : PersuadeEarly_Private_Valuation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:14.381983+00:00
-- url     : https://prove2.me/theorems/c19cb179-a1de-4ed0-a6ff-81b58eedc13c
-- title:
--   §3.1, p. 5 — valuations with a non-decreasing hazard rate on $[0,b]$, random inventory, $\bar F$, $p^m$ and $\bar F^{-1}$
-- statement:
--   This file sets up the primitives of the model of Drakopoulos, Jain and Randhawa: a monopolist selling one product over two periods to a unit mass of customers with random inventory.
--
--   **Primitives.** A model consists of
--   1. the top $b$ of the support $V=[0,b]$ of the customers' valuations, and a density $f$ of the valuation distribution $F$;
--   2. the prior probability $P(H)$ that the inventory is high, $Q=q_H=1$ (enough for every customer), and the low inventory level $q_L$, realized with probability $P(L)=1-P(H)$.
--
--   The valuation distribution is the measure $\mu$ with density $f$ on $[0,b]$, and
--   $$\bar F(y)=\mu\big((y,\infty)\big)=1-F(y)$$
--   is the mass of customers with valuation above $y$; so $\bar F=1$ below $0$ and $\bar F=0$ above $b$.
--
--   **Standing assumptions.** Every theorem of the mission assumes:
--   1. $b>0$; $f$ is continuous on $[0,b]$, positive on $[0,b)$, and $\int_0^b f=1$;
--   2. the hazard rate $f(v)/\bar F(v)$ is non-decreasing on $[0,b)$;
--   3. $0<P(H)<1$ and $0<q_L\le 1$.
--
--   **Derived objects.** The monopoly price (6) is the maximizer of the static revenue,
--   $$p^m=\arg\max_{p\in[0,b]} p\,\bar F(p),$$
--   defined as the largest maximizer (the maximizer is unique under the standing assumptions). The inverse $\bar F^{-1}(q)$ is the smallest $v\in[0,b]$ with $\bar F(v)\le q$; for $q\in(0,1)$ it is the unique $v$ with $\bar F(v)=q$.
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** The paper says only that $F$ has "support $V$" and a non-decreasing hazard rate. The bounded support $[0,b]$, the continuous density positive on $[0,b)$, and the bounds $0<P(H)<1$, $0<q_L$ are disclosed additions (the proofs divide by $P(H)$, $P(L)$ and by the density; the paper's examples are uniform on $[0,1]$). The normalizations $q_H=1$ and customer mass $d=1$ are the paper's own (p. 5) and are built in.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 5, §3.1; p. 9, (6); p. 15, F̄^{-1}

import Mathlib

open MeasureTheory Set

namespace PersuadeEarly.Private

/-- The primitives of the model of Drakopoulos, Jain, Randhawa, *Persuading Customers to Buy
Early: The Value of Personalized Information Provisioning*, SSRN 3191629 (version of April 17,
2020), p. 5, §3.1: valuations are distributed on the support `V = [0, b]` with density `f`; the
inventory is high (`qH = 1`) with probability `pH = P(H)` and low (`qL`) with probability
`P(L) = 1 - pH`. The customer mass is normalized to `d = 1`.

**Formalization Note** The paper says only that `F` has "support `V`" and a non-decreasing hazard
rate. The mission fixes `V = [0, b]` with `b > 0` and a density `f` (see `Model.Standing`);
`qH = 1` and `d = 1` are the paper's normalizations (p. 5) and are built in. -/
structure Model where
  /-- the top of the support `V = [0, b]` of the valuation distribution -/
  b : ℝ
  /-- the density of the valuation distribution `F` -/
  f : ℝ → ℝ
  /-- the prior probability `P(H)` of high inventory `qH = 1` -/
  pH : ℝ
  /-- the low inventory level `qL` -/
  qL : ℝ

namespace Model

variable (M : Model)

/-- The valuation distribution `F` as a measure: the density `f` restricted to `[0, b]`. -/
noncomputable def mu : Measure ℝ :=
  (volume.restrict (Icc 0 M.b)).withDensity (fun v => ENNReal.ofReal (M.f v))

/-- The complementary distribution function `F̄(y) = 1 - F(y)`, the mass of valuations strictly
above `y` (p. 5). It equals `1` below `0` and `0` above `b`. -/
noncomputable def Fbar (y : ℝ) : ℝ :=
  (M.mu (Ioi y)).toReal

/-- The standing assumptions of the paper (p. 5), made explicit:
1. `b > 0`, `f` continuous on `[0, b]`, positive on `[0, b)`, integrating to `1` over `[0, b]`;
2. the hazard rate `f / F̄` is non-decreasing on `[0, b)` ("F has a non-decreasing hazard rate");
3. `0 < P(H) < 1` and `0 < qL ≤ 1`.

**Formalization Note** The bounded support, the continuous positive density and the bounds on
`P(H)` and `qL` are disclosed additions: the proofs divide by `P(H)`, `P(L)` and by the density,
and the paper's examples are uniform on `[0, 1]`. -/
structure Standing : Prop where
  b_pos : 0 < M.b
  f_cont : ContinuousOn M.f (Icc 0 M.b)
  f_pos : ∀ v ∈ Ico 0 M.b, 0 < M.f v
  f_int : ∫ v in (0)..M.b, M.f v = 1
  hazard_mono : MonotoneOn (fun v => M.f v / M.Fbar v) (Ico 0 M.b)
  pH_pos : 0 < M.pH
  pH_lt_one : M.pH < 1
  qL_pos : 0 < M.qL
  qL_le_one : M.qL ≤ 1

/-- `P(L) = 1 - P(H)`. -/
def pL : ℝ := 1 - M.pH

/-- The monopoly price `p^m = arg max_p p F̄(p)` (6), p. 9: the largest maximizer of `p F̄(p)` over
the support `[0, b]` (the maximizer is unique under `Standing`). -/
noncomputable def pm : ℝ :=
  sSup {p ∈ Icc 0 M.b | ∀ q ∈ Icc 0 M.b, q * M.Fbar q ≤ p * M.Fbar p}

/-- The inverse `F̄^{-1}(q)`: the smallest valuation `v ∈ [0, b]` with `F̄(v) ≤ q`. For
`q ∈ (0, 1)` it is the unique `v` with `F̄(v) = q`. -/
noncomputable def FbarInv (q : ℝ) : ℝ :=
  sInf {v ∈ Icc 0 M.b | M.Fbar v ≤ q}

end Model

end PersuadeEarly.Private


