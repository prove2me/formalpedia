-- Prove2me | Definitions.Def_CarlssonPartition_Equitable_Setting
-- name    : CarlssonPartition_Equitable_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:16:35.526713+00:00
-- url     : https://prove2.me/theorems/22a65ba1-5c7a-441e-aab4-5c165a67c24c
-- title:
--   §3, pp. 6–10 and p. ec4 — region, depot, density and fleet; workload factor, Theorem 3's leading-order delivery time, subregion data λ_i, f_i, partitions, heavy traffic
-- statement:
--   This file sets up the continuous-approximation model of last-mile delivery of Carlsson, Liu, Salari and Yu (§3).
--
--   **Primitives.** An *instance* consists of a service region $\mathscr R\subseteq\mathbb R^2$, a depot $x_0$, a demand density $f:\mathbb R^2\to\mathbb R$, a number $m\in\mathbb N$ of identical vehicles with speed $v$ and capacity $q\in\mathbb N$, a mean on-site service time $\bar s$, and the constant $\beta$ of the Beardwood–Halton–Hammersley theorem. The arrival rate $\lambda$ of orders is not part of the instance: it is the parameter that is driven to heavy traffic.
--
--   **Standing assumptions** (p. 6), bundled in the predicate $\mathrm{Standing}$:
--   1. $\mathscr R$ is compact and convex, and $x_0\in\mathscr R$;
--   2. $f\ge 0$ on $\mathscr R$, $f$ is Lipschitz on $\mathscr R$, and $\iint_{\mathscr R} f(x)\,dx=1$;
--   3. $m\ge 1$, $v>0$, $q\ge 1$, $\bar s\ge 0$ and $\beta>0$.
--
--   **Workload factor** (p. 7). For $k$ vehicles serving a region $S$ with density $g$ at arrival rate $\lambda$,
--   $$W_k(\lambda;S,g)=\frac{\lambda\bar s}{k}+\frac{2\lambda\iint_S\|x-x_0\|\,g(x)\,dx}{kvq}.$$
--   For the whole fleet this is $\rho+2\lambda\iint_{\mathscr R}\|x-x_0\|f(x)\,dx/mvq$ with $\rho=\lambda\bar s/m$.
--
--   **Leading-order delivery time** (the right-hand side of Theorem 3 of Bertsimas and van Ryzin, p. 8):
--   $$L_k(\lambda;S,g)=\frac{\beta^2\lambda\,(1-\tfrac1q)^2\left[\iint_S\sqrt{g(x)}\,dx\right]^2}{2k^2v^2\,\bigl(1-W_k(\lambda;S,g)\bigr)^2}.$$
--
--   **Subregion data** (p. ec4). For a subregion $S=\mathscr R_i$: $\mathbb P(x\in S)=\iint_S f(x)\,dx$, the arrival rate $\lambda_i=\lambda\iint_S f(x)\,dx$, and the conditional density $f_i(x)=f(x)/\iint_S f(y)\,dy$.
--
--   **Partitions.** $\{\mathscr R_1,\dots,\mathscr R_m\}$ is a partition of $\mathscr R$ when the pieces are measurable up to null sets, pairwise overlap only in null sets, and their union is $\mathscr R$.
--
--   **Heavy traffic** (p. 7). The heavy-traffic limit for $(k,S,g)$ is the filter on arrival rates $\lambda$ along which $W_k(\lambda;S,g)\to 1$ from below.
--
--   These objects are the vocabulary of every statement of the mission: the subregion's leading term is $L_1(\lambda_i;\mathscr R_i,f_i)$, which is Theorem 3 applied to one vehicle in $\mathscr R_i$, and the fleet's is $L_m(\lambda;\mathscr R,f)$.
--
--   **Formalization Note.** The plane is `EuclideanSpace ℝ (Fin 2)` with the Euclidean norm. Integrals are Bochner set integrals for Lebesgue measure. The heavy-traffic filter is `Filter.comap (fun λ => W_k(λ;S,g)) (𝓝[<] 1)`: only $\lambda$ varies, and the workload factor approaches 1 from below, as it takes values in $(0,1)$ (p. 7). "Partition" is read up to null sets because the paper's districts are convex pieces sharing boundary segments. The Lipschitz condition is a standing model assumption of the paper (p. 6), kept although no statement of this mission uses it beyond continuity. The delivery times themselves are not defined: the stochastic routing model is not formalized, and Theorem 3 enters the theorems as a hypothesis.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), pp. 6–10 (§3, Theorem 3, p. 8), p. ec4 (proof of Theorem 5)

import Mathlib

noncomputable section

namespace CarlssonPartition.Equitable

/-- The Euclidean plane `ℝ²` in which the service region lies (p. 6). -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The data of the model of §3, p. 6: the service region `R`, the depot `x0`, the demand density
`f`, the number of vehicles `m`, their speed `v` and capacity `q`, the mean on-site service time
`sbar` (s̄) and the BHH constant `beta` (β) of Theorem 1. The arrival rate λ is not a field: it is
the parameter along which heavy traffic is taken. -/
structure Instance where
  R : Set Plane
  x0 : Plane
  f : Plane → ℝ
  m : ℕ
  v : ℝ
  q : ℕ
  sbar : ℝ
  beta : ℝ

/-- The standing assumptions of §3, p. 6: `R` is compact and convex and contains the depot; `f` is
a Lipschitz probability density on `R`; at least one vehicle, positive speed, capacity in `ℕ₊`,
nonnegative mean service time, positive BHH constant. -/
def Instance.Standing (I : Instance) : Prop :=
  IsCompact I.R ∧ Convex ℝ I.R ∧ I.x0 ∈ I.R ∧
  (∀ x ∈ I.R, 0 ≤ I.f x) ∧
  (∃ K : NNReal, LipschitzOnWith K I.f I.R) ∧
  (∫ x in I.R, I.f x) = 1 ∧
  1 ≤ I.m ∧ 0 < I.v ∧ 1 ≤ I.q ∧ 0 ≤ I.sbar ∧ 0 < I.beta

/-- The workload factor `λ s̄ / k + 2 λ ∬_S ‖x - x0‖ g(x) dx / (k v q)` of `k` vehicles serving the
region `S` with demand density `g` at arrival rate `λ` (p. 7, with `ρ = λ s̄ / k`). -/
def Instance.workload (I : Instance) (k : ℕ) (lam : ℝ) (S : Set Plane) (g : Plane → ℝ) : ℝ :=
  lam * I.sbar / (k : ℝ) +
    2 * lam * (∫ x in S, ‖x - I.x0‖ * g x) / ((k : ℝ) * I.v * (I.q : ℝ))

/-- The right-hand side of Theorem 3 (Bertsimas and van Ryzin 1993b), p. 8, for `k` vehicles serving
the region `S` with demand density `g` at arrival rate `λ`:
`β² λ (1 - 1/q)² [∬_S √g]² / (2 k² v² (1 - workload)²)`. -/
def Instance.bvrLeading (I : Instance) (k : ℕ) (lam : ℝ) (S : Set Plane) (g : Plane → ℝ) : ℝ :=
  I.beta ^ 2 * lam * (1 - 1 / (I.q : ℝ)) ^ 2 * (∫ x in S, Real.sqrt (g x)) ^ 2 /
    (2 * (k : ℝ) ^ 2 * I.v ^ 2 * (1 - I.workload k lam S g) ^ 2)

/-- `P(x ∈ S) = ∬_S f(x) dx`. -/
def Instance.pr (I : Instance) (S : Set Plane) : ℝ :=
  ∫ x in S, I.f x

/-- The arrival rate `λ_i = λ ∬_{R_i} f(x) dx` to the subregion `S = R_i` (p. ec4). -/
def Instance.lamSub (I : Instance) (lam : ℝ) (S : Set Plane) : ℝ :=
  lam * I.pr S

/-- The conditional demand density `f_i(x) = f(x) / ∬_{R_i} f(y) dy` of the subregion `S = R_i`
(p. ec4). -/
def Instance.fSub (I : Instance) (S : Set Plane) (x : Plane) : ℝ :=
  I.f x / I.pr S

/-- `{R_1, …, R_m}` is a partition of `R`, read up to Lebesgue-null sets: null-measurable pieces,
pairwise almost-everywhere disjoint, whose union is `R`. -/
def Instance.IsPartition (I : Instance) (Rs : Fin I.m → Set Plane) : Prop :=
  (∀ i, MeasureTheory.NullMeasurableSet (Rs i) MeasureTheory.volume) ∧
  Pairwise (fun i j => MeasureTheory.AEDisjoint MeasureTheory.volume (Rs i) (Rs j)) ∧
  (⋃ i, Rs i) = I.R

/-- Heavy traffic for `k` vehicles serving `S` with density `g`: the filter on arrival rates `λ`
along which the workload factor tends to `1` from below (p. 7). -/
def Instance.heavy (I : Instance) (k : ℕ) (S : Set Plane) (g : Plane → ℝ) : Filter ℝ :=
  Filter.comap (fun lam => I.workload k lam S g) (nhdsWithin 1 (Set.Iio 1))

end CarlssonPartition.Equitable


