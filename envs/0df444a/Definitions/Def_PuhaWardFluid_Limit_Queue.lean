-- Prove2me | Definitions.Def_PuhaWardFluid_Limit_Queue
-- name    : PuhaWardFluid_Limit_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:20.402117+00:00
-- url     : https://prove2.me/theorems/6e9b9170-67dc-4dfd-8b6f-66019f5f1a6e
-- title:
--   §2, pp. 5–13 — the N-server queue, admissible HL control policies (Definitions 1–3), fluid scaling and Assumptions 1–5
-- statement:
--   This file defines the sequence of multiclass $N$-server queues with reneging of Puha–Ward (§2, pp. 5–13), admissible head-of-the-line (HL) control policies, the fluid scaling, and Assumptions 1–5 (§4, pp. 16–17).
--
--   **Primitive inputs** (§2.1). For each $N\in\mathbb N$ and class $j$: an arrival counting process $E^N_j$ (batches allowed), service times $\{v_{j,i}\}_{i\in\mathbb Z}$ i.i.d. $G^s_j$, patience times $\{r_{j,i}\}_{i\in\mathbb N}$ i.i.d. $G^r_j$ on $[0,\infty]$, and i.i.d. uniform $(0,1)$ sequences $V^N_{j,i},R^N_{j,i}$ ($i\le0$) and $\epsilon^N_i,d^N_i$ ($i\ge1$). These sequences are mutually independent and independent of $E^N$; the coordinates of $E^N$ are independent; $\alpha^N_j$ (time since the last class-$j$ batch, (3)) is Markov in its own filtration; $\mathbb P(e^N_{j,1}<\infty)=1$.
--
--   **Initial state** (§2.2–2.3). $Y^N(0)$ gives the numbers in system $x^N_{0,j}$, in service $b^N_{0,j}$, potentially waiting $\langle1,\eta^N_{0,j}\rangle$, the ages in service $a^N_{j,i}(0)$ and potential waiting times $w^N_{j,i}(0)$, with (S.1) $b_{0,j}\le x_{0,j}\le b_{0,j}+\langle1,\eta_{0,j}\rangle$, (S.2) $\sum_jb_{0,j}\le N$ and the orderings (6), (8). It is independent of the primitive inputs and $\max_j\mathbb E[X^N_j(0)+\langle1,\eta^N_j(0)\rangle]<\infty$.
--
--   **Dynamics.** From these and the entry-into-service times $k^N_{j,i}\in(0,\infty]$ (the control) one computes $w^N_{j,i}(t)=\min([t-e^N_{j,i}]^+,r^N_{j,i})$, $a^N_{j,i}(t)=\min([t-k^N_{j,i}]^+,v^N_{j,i})$,
--   $$\eta^N_j(t)=\sum_{i=-\langle1,\eta^N_{0,j}\rangle+1}^{E^N_j(t)}\delta_{w^N_{j,i}(t)}1_{\{0\le t-e^N_{j,i}<r^N_{j,i}\}},\qquad \nu^N_j(t)=\sum_{i=-x^N_{0,j}+1}^{E^N_j(t)}\delta_{a^N_{j,i}(t)}1_{\{0\le t-k^N_{j,i}<v^N_{j,i}\}},$$
--   $B^N_j=\langle1,\nu^N_j\rangle$, the entry, departure, potential-reneging and reneging counts $K^N_j,D^N_j,S^N_j,R^N_j$, $X^N_j=X^N_j(0)+E^N_j-D^N_j-R^N_j$ (17), $Q^N_j=X^N_j-B^N_j$, $I^N=N-\sum_jB^N_j$, the marked point processes $\mathcal D^N_j(\varphi,\cdot)$, $\mathcal S^N_j(\psi,\cdot)$ and the compensators $\mathcal A^N_{s,j}(\varphi,t)=\int_0^t\langle\varphi(\cdot,u)h^s_j,\nu^N_j(u)\rangle du$, $\mathcal A^N_{r,j}(\psi,t)=\int_0^t\langle\psi(\cdot,u)h^r_j,\eta^N_j(u)\rangle du$.
--
--   **HL control policy** (Definitions 1–2). Almost surely: customers enter service no earlier than they arrive and before they abandon, (9) $e^N_{j,i}\le k^N_{j,i}<e^N_{j,i}+r^N_{j,i}$ when $k^N_{j,i}<\infty$; within a class in order of arrival: if customer $l$ enters service at $k^N_{j,l}<\infty$, every earlier customer $i<l$ has entered by then or abandoned by then, $k^N_{j,i}\le k^N_{j,l}$ or $e^N_{j,i}+r^N_{j,i}\le k^N_{j,l}$ (the HL condition of pp. 8–9, which contains (10)); the state process $Y^N$ is a random element ($Y^N(t)$ measurable for every $t$); $Y^N=(\alpha^N,X^N,\nu^N,\eta^N)$ is rcll and satisfies (S.1), (S.2), $Q^N\ge0$ and $I^N\ge0$ at all times. **Admissible** (Definition 3): in addition $K^N$ is adapted to $\mathcal G^N_t=\sigma\big((\tilde Y^N(s))_{s\le t},\{\epsilon^N_i\}_{i\le E^N_\Sigma(t)},\{d^N_i\}_{i\le D^N_\Sigma(t)}\big)$.
--
--   **Fluid scaling.** $\bar H^N=H^N/N$ for every process; $(\bar X^N,\bar\nu^N,\bar\eta^N)$ is a path in $\mathbb X$.
--
--   **Assumptions 1–5** (pp. 16–17): convergence of the scaled arrivals (1) and initial conditions (3), control of $\bar K^N$ by (K.2) or by inequality (55) (2), boundedness or lower semicontinuity of the hazards near the right edge of their supports (4), and (5): Assumptions 1–3 together with continuity of $E$, $\eta^0_j$ not charging points, and C-tightness of $\bar K^N$ or (55).
--
--   These definitions are the hypotheses of the fluid limit theorem (Theorem 1) and of the prelimit Lemmas 1, 6, 7 and 8.
--
--   **Formalization Note** The derivative indicators of $D^N,S^N,R^N$ and of the marked point processes (p. 10–11) are resolved into explicit counts: customer $i$ departs at $k^N_{j,i}+v^N_{j,i}$ with mark $\varphi(v^N_{j,i},k^N_{j,i}+v^N_{j,i})$, potential customer $i$ potentially reneges at $e^N_{j,i}+r^N_{j,i}$, and customer $i$ reneges at $s=e^N_{j,i}+r^N_{j,i}\le t$ when $s\le k^N_{j,i}$ (its age at $s$ is zero). Times are in $[-\infty,\infty]$; $r=\infty$ keeps a potential customer forever, $k=\infty$ means never served. A Dirac mass at a point outside $[0,H)$ is replaced by $0$; this never happens on the event where the service and patience times have their laws. Definition 1 says $Y^N$ "satisfies (5)–(26)"; only the defining relations are imposed here, and the identities (18)–(26) (in particular Lemma 1) are left as consequences. Definition 2's mixture over initial states is automatic because the initial state is a random element of the same probability space; the policy is taken on $\mathbb S^N=\mathbb Y^N$, which covers every Polish subspace. Idling is allowed. Pathwise conditions stated "for all" by the paper are imposed almost surely. In Assumption 4, "bounded or lower semicontinuous on $(L,H)$" is read on $(L,H)\cap[0,H)$, where the hazard is defined. The head-of-the-line order is the HL condition stated in words on pp. 8–9 ("when $k$ customers simultaneously enter service, they are the 1st through $k$th HL class $j$ customers"), not (10) alone: (10) as printed only compares two customers who both enter service, so it allows a policy to skip a waiting customer for good (who later abandons) and serve younger ones, which contradicts the consequence the paper draws from (10) on p. 11 (customers with potential waiting time below $\chi^N_j(t)$ are in queue) and the reneging equation (40) of the fluid limit.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, pp. 5–13, 16–19 (PDF 6–14, 17–20), §2.1–2.6 (3)–(19), Definitions 1–3, §4 (fluid scaling), Assumptions 1–5

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_FluidModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

variable {J : ℕ}

/-- The data of the sequence of `N`-server queues, `N ∈ ℕ = {1, 2, …}`, on one probability space
(§2, pp. 5–9). Customer indices are integers, as in the paper.
* `E N ω t j` — the arrival process `E^N_j(t)` (§2.1.1);
* `alpha0 N ω j` — `α^N_{0,j}` (§2.1.1);
* `v j i ω` — service times `v_{j,i}`, `i ∈ ℤ` (§2.1.2; the same for every `N`);
* `r j i ω` — patience times `r_{j,i} ∈ [0, ∞]`, `i ∈ ℕ` (only `i ≥ 1` is used; same for every `N`);
* `Vu N j i ω`, `Ru N j i ω` — the uniforms `V^N_{j,i}`, `R^N_{j,i}`, `i ∈ ℤ₋` (only `i ≤ 0` is used);
* `eps N i ω`, `dd N i ω` — the uniforms `ϵ^N_i`, `d^N_i`, `i ∈ ℕ` (only `i ≥ 1` is used);
* the initial state `y^N_0` (§2.2, §2.3): `x0 = X^N(0)`, `b0 = ⟨1, ν^N(0)⟩`, `m0 = ⟨1, η^N(0)⟩`,
  ages `a0 N ω j i = a^N_{j,i}(0)` for `i ∈ (−x0, −q0]` and potential waiting times
  `w0 N ω j i = w^N_{j,i}(0)` for `i ∈ (−m0, 0]` (other indices unused);
* `kE N ω j i ∈ (0, ∞]` — the entry-into-service time `k^N_{j,i}` of a customer `i > −q^N_{0,j}`
  (`∞` if the customer never enters service); this is the control. -/
structure QueueSeq (J : ℕ) (Ω : Type*) where
  E : ℕ+ → Ω → ℝ≥0 → Fin J → ℕ
  alpha0 : ℕ+ → Ω → Fin J → ℝ≥0
  v : Fin J → ℤ → Ω → ℝ
  r : Fin J → ℤ → Ω → ℝ≥0∞
  Vu : ℕ+ → Fin J → ℤ → Ω → ℝ
  Ru : ℕ+ → Fin J → ℤ → Ω → ℝ
  eps : ℕ+ → ℤ → Ω → ℝ
  dd : ℕ+ → ℤ → Ω → ℝ
  x0 : ℕ+ → Ω → Fin J → ℕ
  b0 : ℕ+ → Ω → Fin J → ℕ
  m0 : ℕ+ → Ω → Fin J → ℕ
  a0 : ℕ+ → Ω → Fin J → ℤ → ℝ≥0
  w0 : ℕ+ → Ω → Fin J → ℤ → ℝ≥0
  kE : ℕ+ → Ω → Fin J → ℤ → ℝ≥0∞

namespace QueueSeq

variable {Ω : Type*} (L : ClassLaws J) (Q : QueueSeq J Ω) (N : ℕ+) (ω : Ω)

/-- `q^N_{0,j} = x^N_{0,j} − b^N_{0,j}` (p. 7). -/
def q0 (j : Fin J) : ℕ := Q.x0 N ω j - Q.b0 N ω j

/-- The residual-time map `inf {t > 0 : G_y(t) > u} ∈ [0, ∞]` (`∞` on the empty set). -/
noncomputable def resid (g : ℝ → ℝ≥0) (y u : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 < t ∧ u < condCdf g y t), ENNReal.ofReal t

/-- Arrival times: `e^N_{j,i} = inf {t ≥ 0 : E^N_j(t) ≥ i}` for `i ≥ 1` (§2.1.1, `∞` if never), and
`e^N_{j,i} = −w^N_{j,i}(0)` for `i ≤ 0` (§2.3.1). -/
noncomputable def arr (j : Fin J) (i : ℤ) : EReal :=
  if i ≤ 0 then -((Q.w0 N ω j i : ℝ) : EReal)
  else (((⨅ (t : ℝ≥0) (_ : i.toNat ≤ Q.E N ω t j), (t : ℝ≥0∞)) : ℝ≥0∞) : EReal)

/-- Patience times `r^N_{j,i}` (§2.3.1): `r_{j,i}` for `i ≥ 1`, and for a time-zero potential
customer `i ≤ 0`, `inf {t > 0 : G^r_{j, w^N_{j,i}(0)}(t) > R^N_{j,i}} + w^N_{j,i}(0)`. -/
noncomputable def pat (j : Fin J) (i : ℤ) : EReal :=
  if i ≤ 0 then
    ((resid (L.gr j) (Q.w0 N ω j i) (Q.Ru N j i ω) : ℝ≥0∞) : EReal) + ((Q.w0 N ω j i : ℝ) : EReal)
  else ((Q.r j i ω : ℝ≥0∞) : EReal)

/-- Service times `v^N_{j,i}` (§2.3.2): for a customer in service at time zero (`i ≤ −q^N_{0,j}`),
`inf {t > 0 : G^s_{j, a^N_{j,i}(0)}(t) > V^N_{j,i}} + a^N_{j,i}(0)`; otherwise `v_{j,i}`. -/
noncomputable def serv (j : Fin J) (i : ℤ) : EReal :=
  if i ≤ -(Q.q0 N ω j : ℤ) then
    ((resid (L.gs j) (Q.a0 N ω j i) (Q.Vu N j i ω) : ℝ≥0∞) : EReal) + ((Q.a0 N ω j i : ℝ) : EReal)
  else ((Q.v j i ω : ℝ) : EReal)

/-- Entry-into-service times `k^N_{j,i}` (§2.4.1): `−a^N_{j,i}(0)` for a customer in service at
time zero, and the control `kE` otherwise (`∞` = never enters service). -/
noncomputable def entry (j : Fin J) (i : ℤ) : EReal :=
  if i ≤ -(Q.q0 N ω j : ℤ) then -((Q.a0 N ω j i : ℝ) : EReal) else ((Q.kE N ω j i : ℝ≥0∞) : EReal)

/-- Potential waiting time `w^N_{j,i}(t) = min([t − e^N_{j,i}]^+, r^N_{j,i})` (p. 7). -/
noncomputable def wait (j : Fin J) (i : ℤ) (t : ℝ≥0) : EReal :=
  min (max (((t : ℝ) : EReal) - Q.arr N ω j i) 0) (Q.pat L N ω j i)

/-- Age in service `a^N_{j,i}(t) = min([t − k^N_{j,i}]^+, v^N_{j,i})` (11). -/
noncomputable def age (j : Fin J) (i : ℤ) (t : ℝ≥0) : EReal :=
  min (max (((t : ℝ) : EReal) - Q.entry N ω j i) 0) (Q.serv L N ω j i)

end QueueSeq

open Classical in
/-- The unit Dirac mass `δ_z ∈ M[0, H)` at a point `z` (given in `EReal`); the zero measure if `z`
is not a finite point of `[0, H)` (never the case for the atoms of (7), (12), (14) on the event
where the patience and service times have their laws). -/
noncomputable def atomAt (H : ℝ≥0∞) (z : EReal) : FiniteMeasure (Iv H) :=
  if h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H then
    ⟨Measure.dirac (⟨z.toReal.toNNReal, h.2⟩ : Iv H), inferInstance⟩
  else 0

namespace QueueSeq

variable {Ω : Type*} (L : ClassLaws J) (Q : QueueSeq J Ω) (N : ℕ+) (ω : Ω)

open Classical in
/-- The potential queue measure (7): `η^N_j(t) = ∑_{i=−⟨1,η^N_{0,j}⟩+1}^{E^N_j(t)}
δ_{w^N_{j,i}(t)} 1{0 ≤ t − e^N_{j,i} < r^N_{j,i}}`. -/
noncomputable def eta (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hr j)) :=
  ∑ i ∈ Finset.Ioc (-(Q.m0 N ω j : ℤ)) (Q.E N ω t j : ℤ),
    if 0 ≤ ((t : ℝ) : EReal) - Q.arr N ω j i ∧ ((t : ℝ) : EReal) - Q.arr N ω j i < Q.pat L N ω j i
    then atomAt (L.Hr j) (Q.wait L N ω j i t) else 0

open Classical in
/-- The age-in-service measure (12): `ν^N_j(t) = ∑_{i=−x^N_{0,j}+1}^{E^N_j(t)}
δ_{a^N_{j,i}(t)} 1{0 ≤ t − k^N_{j,i} < v^N_{j,i}}`. -/
noncomputable def nu (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hs j)) :=
  ∑ i ∈ Finset.Ioc (-(Q.x0 N ω j : ℤ)) (Q.E N ω t j : ℤ),
    if 0 ≤ ((t : ℝ) : EReal) - Q.entry N ω j i ∧ ((t : ℝ) : EReal) - Q.entry N ω j i < Q.serv L N ω j i
    then atomAt (L.Hs j) (Q.age L N ω j i t) else 0

open Classical in
/-- The measure (14): `ν̃^N_j(t)`, as (12) with the strict condition `0 < t − k^N_{j,i}`. -/
noncomputable def nuT (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hs j)) :=
  ∑ i ∈ Finset.Ioc (-(Q.x0 N ω j : ℤ)) (Q.E N ω t j : ℤ),
    if 0 < ((t : ℝ) : EReal) - Q.entry N ω j i ∧ ((t : ℝ) : EReal) - Q.entry N ω j i < Q.serv L N ω j i
    then atomAt (L.Hs j) (Q.age L N ω j i t) else 0

/-- (13) `B^N_j(t) = ⟨1, ν^N_j(t)⟩`. -/
noncomputable def B (t : ℝ≥0) (j : Fin J) : ℝ := mass1 (Q.nu L N ω t j)

open Classical in
/-- The entry-into-service process (p. 9): `K^N_j(t) = ∑_{i=−q^N_{0,j}+1}^{E^N_j(t)} 1{k^N_{j,i} ≤ t}`. -/
noncomputable def K (t : ℝ≥0) (j : Fin J) : ℕ :=
  ((Finset.Ioc (-(Q.q0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
    (fun i => Q.entry N ω j i ≤ ((t : ℝ) : EReal))).card

open Classical in
/-- The departure process `D^N_j(t)` (p. 10), with the derivative indicator resolved: customer `i`
departs at `k^N_{j,i} + v^N_{j,i}`, counted when this is `≤ t`. -/
noncomputable def D (t : ℝ≥0) (j : Fin J) : ℕ :=
  ((Finset.Ioc (-(Q.x0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
    (fun i => Q.entry N ω j i + Q.serv L N ω j i ≤ ((t : ℝ) : EReal))).card

open Classical in
/-- The potential reneging process `S^N_j(t)` (p. 10): potential customer `i` potentially reneges at
`e^N_{j,i} + r^N_{j,i}`, counted when this is `≤ t` (never if `r^N_{j,i} = ∞`). -/
noncomputable def S (t : ℝ≥0) (j : Fin J) : ℕ :=
  ((Finset.Ioc (-(Q.m0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
    (fun i => Q.arr N ω j i + Q.pat L N ω j i ≤ ((t : ℝ) : EReal))).card

open Classical in
/-- The reneging process `R^N_j(t)` (p. 10): customer `i > −q^N_{0,j}` reneges at
`s = e^N_{j,i} + r^N_{j,i} ≤ t` if its age in service at `s` is zero, i.e. `s ≤ k^N_{j,i}`. -/
noncomputable def R (t : ℝ≥0) (j : Fin J) : ℕ :=
  ((Finset.Ioc (-(Q.q0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
    (fun i => Q.arr N ω j i + Q.pat L N ω j i ≤ ((t : ℝ) : EReal) ∧
      Q.arr N ω j i + Q.pat L N ω j i ≤ Q.entry N ω j i)).card

/-- (17) `X^N_j(t) = X^N_j(0) + E^N_j(t) − D^N_j(t) − R^N_j(t)`. -/
noncomputable def X (t : ℝ≥0) (j : Fin J) : ℝ :=
  (Q.x0 N ω j : ℝ) + Q.E N ω t j - Q.D L N ω t j - Q.R L N ω t j

/-- (15) `Q^N_j(t) = X^N_j(t) − B^N_j(t)`. -/
noncomputable def Qlen (t : ℝ≥0) (j : Fin J) : ℝ := Q.X L N ω t j - Q.B L N ω t j

/-- (16) `I^N(t) = N − ∑_j B^N_j(t)`. -/
noncomputable def I (t : ℝ≥0) : ℝ := (N : ℝ) - ∑ j, Q.B L N ω t j

/-- `E^N_Σ(t) = ∑_j E^N_j(t)`. -/
def ESum (t : ℝ≥0) : ℕ := ∑ j, Q.E N ω t j
/-- `D^N_Σ(t) = ∑_j D^N_j(t)`. -/
noncomputable def DSum (t : ℝ≥0) : ℕ := ∑ j, Q.D L N ω t j

/-- (3) `α^N_j(t) = α^N_{0,j} + t` for `t < e^N_{j,1}`, and
`t − sup {s < t : E^N_j(t) − E^N_j(s) > 0}` for `t ≥ e^N_{j,1}`. -/
noncomputable def alpha (t : ℝ≥0) (j : Fin J) : ℝ≥0 :=
  if ((t : ℝ) : EReal) < Q.arr N ω j 1 then Q.alpha0 N ω j + t
  else t - sSup {s : ℝ≥0 | s < t ∧ Q.E N ω s j < Q.E N ω t j}

/-- The state space of `Y^N = (α^N, X^N, ν^N, η^N)` (4). -/
abbrev Ysp (L : ClassLaws J) : Type :=
  (Fin J → ℝ≥0) × (Fin J → ℝ) × (∀ j, FiniteMeasure (Iv (L.Hs j))) ×
    (∀ j, FiniteMeasure (Iv (L.Hr j)))

/-- The state process `Y^N(t) = (α^N(t), X^N(t), ν^N(t), η^N(t))`. -/
noncomputable def Y (t : ℝ≥0) : Ysp L :=
  (fun j => Q.alpha N ω t j, fun j => Q.X L N ω t j, fun j => Q.nu L N ω t j,
    fun j => Q.eta L N ω t j)

/-- `Ỹ^N(0) = Y^N(0)` and `Ỹ^N(t) = (α^N(t), X^N(t), ν̃^N(t), η^N(t))` for `t > 0` (p. 13). -/
noncomputable def Ytil (t : ℝ≥0) : Ysp L :=
  if t = 0 then Q.Y L N ω 0
  else (fun j => Q.alpha N ω t j, fun j => Q.X L N ω t j, fun j => Q.nuT L N ω t j,
    fun j => Q.eta L N ω t j)

/-- The departure-from-service marked point process (p. 11), with the derivative indicator
resolved: `𝒟^N_j(φ, t) = ∑ φ(v^N_{j,i}, k^N_{j,i} + v^N_{j,i})` over the customers
`i ∈ (−x^N_{0,j}, E^N_j(t)]` with `k^N_{j,i} + v^N_{j,i} ≤ t` (at the departure time `s` the age is
`a^N_{j,i}(s) = v^N_{j,i}`). `φ` is given on `ℝ × ℝ` and used on `[0, H^s_j) × ℝ₊`. -/
noncomputable def Dmark (φ : ℝ → ℝ → ℝ) (t : ℝ≥0) (j : Fin J) : ℝ :=
  ∑ i ∈ (Finset.Ioc (-(Q.x0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
      (fun i => Q.entry N ω j i + Q.serv L N ω j i ≤ ((t : ℝ) : EReal)),
    φ (Q.serv L N ω j i).toReal (Q.entry N ω j i + Q.serv L N ω j i).toReal

/-- The potential reneging marked point process (p. 11), with the derivative indicator resolved:
`𝒮^N_j(ψ, t) = ∑ ψ(r^N_{j,i}, e^N_{j,i} + r^N_{j,i})` over `i ∈ (−⟨1, η^N_{0,j}⟩, E^N_j(t)]` with
`e^N_{j,i} + r^N_{j,i} ≤ t`. -/
noncomputable def Smark (ψ : ℝ → ℝ → ℝ) (t : ℝ≥0) (j : Fin J) : ℝ :=
  ∑ i ∈ (Finset.Ioc (-(Q.m0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
      (fun i => Q.arr N ω j i + Q.pat L N ω j i ≤ ((t : ℝ) : EReal)),
    ψ (Q.pat L N ω j i).toReal (Q.arr N ω j i + Q.pat L N ω j i).toReal

/-- The compensator `𝒜^N_{s,j}(φ, t) = ∫_0^t ⟨φ(·, u) h^s_j(·), ν^N_j(u)⟩ du` (p. 18). -/
noncomputable def Acomp_s (φ : ℝ → ℝ → ℝ) (t : ℝ≥0) (j : Fin J) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, pair (fun x => φ x u * (L.hs j x).toReal) (Q.nu L N ω u.toNNReal j)

/-- The compensator `𝒜^N_{r,j}(ψ, t) = ∫_0^t ⟨ψ(·, u) h^r_j(·), η^N_j(u)⟩ du` (p. 18). -/
noncomputable def Acomp_r (ψ : ℝ → ℝ → ℝ) (t : ℝ≥0) (j : Fin J) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, pair (fun x => ψ x u * (L.hr j x).toReal) (Q.eta L N ω u.toNNReal j)

/-! ### Fluid scaling (p. 16) -/

/-- `Ē^N_j(t) = E^N_j(t)/N`. -/
noncomputable def Ebar (t : ℝ≥0) (j : Fin J) : ℝ := (Q.E N ω t j : ℝ) / N
/-- `X̄^N_j(t) = X^N_j(t)/N`. -/
noncomputable def Xbar (t : ℝ≥0) (j : Fin J) : ℝ := Q.X L N ω t j / N
/-- `K̄^N_j(t) = K^N_j(t)/N`. -/
noncomputable def Kbar (t : ℝ≥0) (j : Fin J) : ℝ := (Q.K N ω t j : ℝ) / N
/-- `ν̄^N_j(t) = ν^N_j(t)/N`. -/
noncomputable def nubar (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hs j)) :=
  (1 / (N : ℝ≥0)) • Q.nu L N ω t j
/-- `η̄^N_j(t) = η^N_j(t)/N`. -/
noncomputable def etabar (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hr j)) :=
  (1 / (N : ℝ≥0)) • Q.eta L N ω t j

/-- The fluid-scaled state `(X̄^N(t), ν̄^N(t), η̄^N(t)) ∈ 𝕏`. -/
noncomputable def fluidTriple (t : ℝ≥0) : Xsp L :=
  (fun j => Q.Xbar L N ω t j, fun j => Q.nubar L N ω t j, fun j => Q.etabar L N ω t j)

end QueueSeq


/-! ### Test-function classes (§1.1.5, p. 4) -/

/-- `f ∈ C¹_c([0, H))` with derivative `f'` (p. 4): `f` is continuous on `[0, H)`, has derivative
`f'(x)` at every `x ∈ [0, H)` (one-sided at `0`), `f'` is continuous on `[0, H)`, and `f` and `f'`
vanish on `(m, H)` for some `m < H` (compact support inside `[0, H)`). Values off `[0, H)` are
irrelevant. -/
def IsC1c (H : ℝ≥0∞) (f f' : ℝ → ℝ) : Prop :=
  ContinuousOn f {x | 0 ≤ x ∧ ENNReal.ofReal x < H} ∧
  (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x < H → HasDerivWithinAt f (f' x) (Set.Ici 0) x) ∧
  ContinuousOn f' {x | 0 ≤ x ∧ ENNReal.ofReal x < H} ∧
  ∃ m : ℝ, 0 ≤ m ∧ ENNReal.ofReal m < H ∧
    ∀ x : ℝ, m < x → ENNReal.ofReal x < H → f x = 0 ∧ f' x = 0

/-- The domain `[0, H) × ℝ₊` of the marks, inside `ℝ × ℝ`. -/
def markDom (H : ℝ≥0∞) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ ENNReal.ofReal p.1 < H ∧ 0 ≤ p.2}

/-- `‖φ‖_∞ = sup {|φ(x, t)| : (x, t) ∈ [0, H) × ℝ₊}` (p. 4), for `φ` bounded on that set. -/
noncomputable def supNormOn (H : ℝ≥0∞) (φ : ℝ → ℝ → ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => |φ p.1 p.2|) '' markDom H)

/-! ### Standing probabilistic assumptions of §2.1–2.2 and HL control policies (§2.5–2.6) -/

/-- `Z` is a **Markov process** with respect to its own natural filtration: each `Z t` is measurable
and `P(Z(t+s) ∈ A | σ(Z(u), u ≤ t)) = P(Z(t+s) ∈ A | σ(Z(t)))` a.s., for all `s, t ≥ 0` and Borel `A`. -/
def IsMarkovProc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ≥0 → Ω → ℝ≥0) : Prop :=
  (∀ t, Measurable (Z t)) ∧
  ∀ (s t : ℝ≥0) (A : Set ℝ≥0), MeasurableSet A →
    condExp (⨆ u ≤ t, MeasurableSpace.comap (Z u) inferInstance) P
        (((Z (t + s)) ⁻¹' A).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      condExp (MeasurableSpace.comap (Z t) inferInstance) P
        (((Z (t + s)) ⁻¹' A).indicator (fun _ => (1 : ℝ)))

/-- The index set of the stochastic primitive inputs of the `N`-th queue (p. 6). -/
inductive PrimIdx (J : ℕ)
  | V (j : Fin J)
  | R (j : Fin J)
  | v (j : Fin J)
  | r (j : Fin J)
  | eps
  | d
  | E

/-- The law of a uniform `(0, 1)` random variable. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Ioo 0 1)

namespace QueueSeq

variable {Ω : Type*} [MeasurableSpace Ω] (L : ClassLaws J) (P : Measure Ω) (Q : QueueSeq J Ω)
  (N : ℕ+)

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by each primitive input sequence of the `N`-th queue. -/
def primSigma : PrimIdx J → MeasurableSpace Ω
  | .V j => MeasurableSpace.comap (fun ω (i : {i : ℤ // i ≤ 0}) => Q.Vu N j i ω) inferInstance
  | .R j => MeasurableSpace.comap (fun ω (i : {i : ℤ // i ≤ 0}) => Q.Ru N j i ω) inferInstance
  | .v j => MeasurableSpace.comap (fun ω (i : ℤ) => Q.v j i ω) inferInstance
  | .r j => MeasurableSpace.comap (fun ω (i : {i : ℤ // 0 < i}) => Q.r j i ω) inferInstance
  | .eps => MeasurableSpace.comap (fun ω (i : {i : ℤ // 0 < i}) => Q.eps N i ω) inferInstance
  | .d => MeasurableSpace.comap (fun ω (i : {i : ℤ // 0 < i}) => Q.dd N i ω) inferInstance
  | .E => MeasurableSpace.comap (fun ω => Q.E N ω) inferInstance

/-- The initial state `Y^N(0)` as one random element. -/
def init (ω : Ω) : (Fin J → ℝ≥0) × (Fin J → ℕ) × (Fin J → ℕ) × (Fin J → ℕ) ×
    (Fin J → ℤ → ℝ≥0) × (Fin J → ℤ → ℝ≥0) :=
  (Q.alpha0 N ω, Q.x0 N ω, Q.b0 N ω, Q.m0 N ω, Q.a0 N ω, Q.w0 N ω)

/-- **Standing assumptions on the primitive inputs and the initial condition** of the `N`-th queue
(§2.1, pp. 5–6; Definition 1 and `𝔖^N`, p. 12):
1. each `E^N_j` is a counting process (nondecreasing, right continuous, `ℕ`-valued, `E^N_j(0) = 0`)
   with `P(e^N_{j,1} < ∞) = 1`, the coordinates of `E^N` are mutually independent, and each
   `α^N_j` is Markov with respect to its own natural filtration;
2. `{v_{j,i}}_{i∈ℤ}` is i.i.d. with distribution function `G^s_j`, `{r_{j,i}}_{i∈ℕ}` is i.i.d. with
   distribution function `G^r_j` on `[0, ∞]`; `{V^N_{j,i}}`, `{R^N_{j,i}}` (`i ∈ ℤ₋`), `{ϵ^N_i}`,
   `{d^N_i}` (`i ∈ ℕ`) are i.i.d. uniform `(0, 1)`;
3. these sequences are mutually independent of one another and of `E^N`;
4. the initial state `Y^N(0)` is a random element independent of the primitive inputs with
   `max_j E[X^N_j(0) + ⟨1, η^N_j(0)⟩] < ∞`. -/
def Primitives : Prop :=
  -- 1. arrivals
  (∀ᵐ ω ∂P, ∀ j, Monotone (fun t => Q.E N ω t j) ∧ IsCadlag (fun t => Q.E N ω t j) ∧
    Q.E N ω 0 j = 0) ∧
  (∀ j, ∀ᵐ ω ∂P, ∃ t, 1 ≤ Q.E N ω t j) ∧
  (∀ t j, Measurable (fun ω => Q.E N ω t j)) ∧
  iIndepFun (fun (j : Fin J) (ω : Ω) (t : ℝ≥0) => Q.E N ω t j) P ∧
  (∀ j, IsMarkovProc P (fun t ω => Q.alpha N ω t j)) ∧
  -- 2. laws
  (∀ j, (∀ i, Measurable (Q.v j i)) ∧ iIndepFun (fun i : ℤ => Q.v j i) P ∧
    ∀ i (x : ℝ), 0 ≤ x → P {ω | Q.v j i ω ≤ x} = ENNReal.ofReal (L.Gs j x)) ∧
  (∀ j, (∀ i, Measurable (Q.r j i)) ∧ iIndepFun (fun i : {i : ℤ // 0 < i} => Q.r j i) P ∧
    ∀ i : ℤ, 0 < i → ∀ x : ℝ, 0 ≤ x →
      P {ω | Q.r j i ω ≤ ENNReal.ofReal x} = ENNReal.ofReal (L.Gr j x)) ∧
  (∀ j, iIndepFun (fun i : {i : ℤ // i ≤ 0} => Q.Vu N j i) P ∧
    ∀ i : ℤ, i ≤ 0 → Measurable (Q.Vu N j i) ∧ P.map (Q.Vu N j i) = unif01) ∧
  (∀ j, iIndepFun (fun i : {i : ℤ // i ≤ 0} => Q.Ru N j i) P ∧
    ∀ i : ℤ, i ≤ 0 → Measurable (Q.Ru N j i) ∧ P.map (Q.Ru N j i) = unif01) ∧
  (iIndepFun (fun i : {i : ℤ // 0 < i} => Q.eps N i) P ∧
    ∀ i : ℤ, 0 < i → Measurable (Q.eps N i) ∧ P.map (Q.eps N i) = unif01) ∧
  (iIndepFun (fun i : {i : ℤ // 0 < i} => Q.dd N i) P ∧
    ∀ i : ℤ, 0 < i → Measurable (Q.dd N i) ∧ P.map (Q.dd N i) = unif01) ∧
  -- 3. mutual independence
  iIndep (Q.primSigma N) P ∧
  -- 4. initial condition
  Measurable (Q.init N) ∧
  Indep (MeasurableSpace.comap (Q.init N) inferInstance) (⨆ p, Q.primSigma N p) P ∧
  (∀ j, ∫⁻ ω, ((Q.x0 N ω j : ℝ≥0∞) + (Q.m0 N ω j : ℝ≥0∞)) ∂P < ⊤)

/-- The pathwise constraints of an **HL control policy** (§2.2–2.4; Definition 1, p. 12) on a
sample path `ω`:
* the initial state lies in `𝕐^N`: (S.1) `b ≤ x ≤ b + ⟨1, η⟩`, (S.2) `∑_j b_j ≤ N`, the orderings
  (6) and (8), with waits `< H^r_j` and ages `< H^s_j`;
* customers waiting at time zero or arriving later enter service at times in `(0, ∞]`;
* (9) `e^N_{j,i} ≤ k^N_{j,i} < e^N_{j,i} + r^N_{j,i}` whenever `k^N_{j,i} < ∞`;
* the HL (head-of-the-line) condition (pp. 8–9): if customer `l` enters service, every earlier
  customer `i < l` (`i > −x^N_{0,j}`) has entered service no later, or has abandoned no later:
  `k^N_{j,l} < ∞ → k^N_{j,i} ≤ k^N_{j,l} ∨ e^N_{j,i} + r^N_{j,i} ≤ k^N_{j,l}`. This implies (10)
  (`k^N_{j,i} ≤ k^N_{j,l}` when both are finite, by (9)) and is what p. 9 means by "when `k`
  customers simultaneously enter service, they are the 1st through `k`th HL class `j` customers";
  (10) as printed does not exclude skipping a waiting customer who abandons later, which p. 11
  ("(10) implies that … each potential customer … with potential waiting time strictly less than
  `χ^N_j(t)` is in queue") rules out;
* `Y^N` is rcll in `𝕐` and satisfies (S.1), (S.2), (15) and (16) at all times.
The identities (18)–(26) of the paper are consequences of these definitions, not constraints. -/
def HLPath (ω : Ω) : Prop :=
  (∀ j, Q.b0 N ω j ≤ Q.x0 N ω j ∧ Q.x0 N ω j ≤ Q.b0 N ω j + Q.m0 N ω j) ∧
  (∑ j, Q.b0 N ω j ≤ (N : ℕ)) ∧
  (∀ j (i : ℤ), -(Q.m0 N ω j : ℤ) < i → i ≤ 0 →
    ((Q.w0 N ω j i : ℝ≥0∞) < L.Hr j ∧ (i < 0 → Q.w0 N ω j (i + 1) ≤ Q.w0 N ω j i))) ∧
  (∀ j (i : ℤ), -(Q.x0 N ω j : ℤ) < i → i ≤ -(Q.q0 N ω j : ℤ) →
    ((Q.a0 N ω j i : ℝ≥0∞) < L.Hs j ∧
      (i < -(Q.q0 N ω j : ℤ) → Q.a0 N ω j (i + 1) ≤ Q.a0 N ω j i))) ∧
  (∀ j (i : ℤ), -(Q.q0 N ω j : ℤ) < i → 0 < Q.kE N ω j i) ∧
  (∀ j (i : ℤ), -(Q.q0 N ω j : ℤ) < i → Q.entry N ω j i < ⊤ →
    Q.arr N ω j i ≤ Q.entry N ω j i ∧ Q.entry N ω j i < Q.arr N ω j i + Q.pat L N ω j i) ∧
  (∀ j (i l : ℤ), -(Q.x0 N ω j : ℤ) < i → i < l → Q.entry N ω j l < ⊤ →
    Q.entry N ω j i ≤ Q.entry N ω j l ∨
      Q.arr N ω j i + Q.pat L N ω j i ≤ Q.entry N ω j l) ∧
  IsCadlag (Q.Y L N ω) ∧
  (∀ t j, Q.B L N ω t j ≤ Q.X L N ω t j ∧
    Q.X L N ω t j ≤ Q.B L N ω t j + mass1 (Q.eta L N ω t j)) ∧
  (∀ t, ∑ j, Q.B L N ω t j ≤ (N : ℝ)) ∧
  (∀ t j, 0 ≤ Q.Qlen L N ω t j) ∧
  (∀ t, 0 ≤ Q.I L N ω t)

/-- An **HL control policy** for the `N`-th queue (Definitions 1–2, pp. 12–13): the standing
assumptions on the primitive inputs and the initial condition, the state `Y^N` is a stochastic
process (each `Y^N(t)` is a random element of `𝕐`; Definition 2 asks for `ℙ(Y^N ∈ B)` for every
measurable `B ⊂ D(𝕊^N)`), and the HL constraints almost surely. -/
def IsHLPolicy : Prop :=
  Q.Primitives L P N ∧ (∀ t, Measurable (fun ω => Q.Y L N ω t)) ∧ ∀ᵐ ω ∂P, Q.HLPath L N ω

set_option warn.classDefReducibility false in
/-- The filtration `𝒢^N_t = σ((Ỹ^N(s), 0 ≤ s ≤ t), {ϵ^N_i}_{i=1}^{E^N_Σ(t)}, {d^N_i}_{i=1}^{D^N_Σ(t)})`
(p. 13); the random-length families are encoded with their lengths and padded by `0`. -/
noncomputable def calG (t : ℝ≥0) : MeasurableSpace Ω :=
  (⨆ s ≤ t, MeasurableSpace.comap (fun ω => Q.Ytil L N ω s) inferInstance) ⊔
  MeasurableSpace.comap (fun ω => (Q.ESum N ω t,
    fun i : {i : ℤ // 0 < i} => if (i : ℤ) ≤ (Q.ESum N ω t : ℤ) then Q.eps N i ω else 0))
    inferInstance ⊔
  MeasurableSpace.comap (fun ω => (Q.DSum L N ω t,
    fun i : {i : ℤ // 0 < i} => if (i : ℤ) ≤ (Q.DSum L N ω t : ℤ) then Q.dd N i ω else 0))
    inferInstance

/-- An **admissible HL control policy** (Definition 3, p. 13): an HL control policy whose
entry-into-service process `K^N` is `{𝒢^N_t}`-adapted. -/
def IsAdmissibleHL : Prop :=
  Q.IsHLPolicy L P N ∧ ∀ t, Measurable[Q.calG L N t] (fun ω => Q.K N ω t)

end QueueSeq

/-! ### Assumptions 1–5 (pp. 16–17) -/

section Assumptions

variable {Ω : Type*} [MeasurableSpace Ω] (L : ClassLaws J) (P : Measure Ω) (Q : QueueSeq J Ω)

/-- **Assumption 1.** `E` is a random element of `D↑(ℝ^J₊)` such that for each `j`:
`Ē^N_j → E_j` in `D(ℝ₊)` almost surely, and `E[Ē^N_j(t)] → E[E_j(t)] < ∞` for all `t ≥ 0`. -/
def Assumption1 (E : Ω → ℝ≥0 → Fin J → ℝ) : Prop :=
  (∀ ω, IsDUp (E ω)) ∧ (∀ t j, Measurable (fun ω => E ω t j)) ∧
  ∀ j, (∀ᵐ ω ∂P, J1Tendsto dR (fun n t => Q.Ebar n.succPNat ω t j) (fun t => E ω t j)) ∧
    ∀ t, Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Q.Ebar n.succPNat ω t j) ∂P) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (E ω t j) ∂P)) ∧
      ∫⁻ ω, ENNReal.ofReal (E ω t j) ∂P < ⊤

/-- Inequality (55): for all `N` and `0 ≤ s < t`,
`max_j K^N_j(t) − K^N_j(s) ≤ E^N_Σ(t) + D^N_Σ(t) − E^N_Σ(s) − D^N_Σ(s)` (almost surely). -/
def Ineq55 : Prop :=
  ∀ N : ℕ+, ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t → ∀ j,
    (Q.K N ω t j : ℝ) - Q.K N ω s j ≤
      (Q.ESum N ω t : ℝ) + Q.DSum L N ω t - Q.ESum N ω s - Q.DSum L N ω s

/-- **Assumption 2.** Either `{K̄^N_j}_N` satisfies (K.2) of Kurtz' criteria for each `j`, or (55)
holds. -/
def Assumption2 : Prop :=
  (∀ j, KurtzK2 P (fun n ω t => Q.Kbar n.succPNat ω t j)) ∨ Ineq55 L P Q

/-- Assumption 2 with its first branch read as relative compactness (the reading under which
Lemma 8 and Theorem 2 are posed; see the Formalization Note of Lemma 8): either `{K̄^N_j}_N` is
relatively compact in `D(ℝ₊)` for each `j`, or (55) holds. -/
def Assumption2RC : Prop :=
  (∀ j, RelCompactInDist dR P (fun n ω t => Q.Kbar n.succPNat ω t j)) ∨ Ineq55 L P Q

/-- **Assumption 3.** `(X^0, ν^0, η^0)` is a random element of `𝕏` such that for each `j`:
`X̄^N_j(0) → X^0_j` a.s.; `E[X̄^N_j(0)] → E[X^0_j] < ∞`; `ν̄^N_j(0) → ν^0_j` and
`η̄^N_j(0) → η^0_j` weakly a.s.; `E[⟨1, η̄^N_j(0)⟩] → E[⟨1, η^0_j⟩] < ∞`. -/
def Assumption3 (Z0 : Ω → Xsp L) : Prop :=
  (∀ ω j, 0 ≤ (Z0 ω).1 j) ∧ Measurable Z0 ∧
  ∀ j,
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Q.Xbar L n.succPNat ω 0 j) atTop (𝓝 ((Z0 ω).1 j))) ∧
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Q.Xbar L n.succPNat ω 0 j) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal ((Z0 ω).1 j) ∂P)) ∧
    ∫⁻ ω, ENNReal.ofReal ((Z0 ω).1 j) ∂P < ⊤ ∧
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Q.nubar L n.succPNat ω 0 j) atTop (𝓝 ((Z0 ω).2.1 j))) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Q.etabar L n.succPNat ω 0 j) atTop (𝓝 ((Z0 ω).2.2 j))) ∧
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (mass1 (Q.etabar L n.succPNat ω 0 j)) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (mass1 ((Z0 ω).2.2 j)) ∂P)) ∧
    ∫⁻ ω, ENNReal.ofReal (mass1 ((Z0 ω).2.2 j)) ∂P < ⊤

/-- "`h` is either bounded or lower semicontinuous on `(ℓ, H)`" for a hazard `h` (finite on `[0, H)`),
read on `(ℓ, H) ∩ [0, H)`, the part of `(ℓ, H)` where `h` is defined. -/
def BddOrLSC (h : ℝ → ℝ≥0∞) (ℓ : ℝ) (H : ℝ≥0∞) : Prop :=
  let S := {x : ℝ | ℓ < x ∧ 0 ≤ x ∧ ENNReal.ofReal x < H}
  (∃ C : ℝ, ∀ x ∈ S, h x ≤ ENNReal.ofReal C) ∨ LowerSemicontinuousOn h S

/-- **Assumption 4.** For each `j` there are `L^s_j < H^s_j` and `L^r_j < H^r_j` such that `h^s_j`
(resp. `h^r_j`) is either bounded or lower semicontinuous on `(L^s_j, H^s_j)` (resp. `(L^r_j, H^r_j)`). -/
def Assumption4 : Prop :=
  ∀ j, (∃ ℓ : ℝ, (ℓ < 0 ∨ ENNReal.ofReal ℓ < L.Hs j) ∧ BddOrLSC (L.hs j) ℓ (L.Hs j)) ∧
    (∃ ℓ : ℝ, (ℓ < 0 ∨ ENNReal.ofReal ℓ < L.Hr j) ∧ BddOrLSC (L.hr j) ℓ (L.Hr j))

/-- **Assumption 5.** Assumptions 1, 2 and 3 hold, `E_j` is continuous a.s. for each `j`, `η^0_j`
does not charge points a.s. for each `j`, and either `{K̄^N}_N` is C-tight or (55) holds. -/
def Assumption5 (E : Ω → ℝ≥0 → Fin J → ℝ) (Z0 : Ω → Xsp L) : Prop :=
  Assumption1 P Q E ∧ Assumption2 L P Q ∧ Assumption3 L P Q Z0 ∧
  (∀ j, ∀ᵐ ω ∂P, Continuous (fun t => E ω t j)) ∧
  (∀ j, ∀ᵐ ω ∂P, NoCharge ((Z0 ω).2.2 j)) ∧
  (CTight (fun a b : Fin J → ℝ => dist a b) P (fun n ω t => Q.Kbar n.succPNat ω t) ∨
    Ineq55 L P Q)

end Assumptions

end PuhaWardFluid.Limit


