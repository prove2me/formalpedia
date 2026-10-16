-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Setting
-- name    : CarlssonPartition_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:48.762345+00:00
-- url     : https://prove2.me/theorems/4e9d6745-3526-4128-bd87-e67841c7eb1f
-- title:
--   §3–§4 — spatial demand, workload, leading delivery time, district data, partition and μ₁, μ₂
-- statement:
--   Fix a compact convex service region $R\subseteq\mathbb R^2$ with depot $x_0$, nonnegative normalized Lipschitz demand density $f$, $m\ge 1$ vehicles of speed $v>0$ and capacity $q\ge1$, mean service time $\bar s\ge0$, and positive geometric constant $\beta$. The standing predicate records these conditions, including $\int_R f=1$. A partition has null measurable districts, pairwise disjoint up to area zero, whose union is $R$.
--
--   For a region $S$, density $g$, vehicle count $k$, and arrival rate $a$, the workload factor and the Theorem 3 leading delivery time are
--   $$
--   W(k,a,S,g)=\frac{a\bar s}{k}+\frac{2a}{kvq}\int_S\lVert x-x_0\rVert g(x)\,dx,\qquad
--   L(k,a,S,g)=\frac{\beta^2a(1-1/q)^2[\int_S\sqrt{g(x)}\,dx]^2}{2k^2v^2(1-W(k,a,S,g))^2}.
--   $$
--   For a district $S$, the demand share, district arrival rate, and conditional density are $p(S)=\int_Sf$, $a_S=ap(S)$, and $f_S=f/p(S)$. The partition measures are
--   $$
--   \mu_1(S)=\int_S\sqrt f,\qquad
--   \mu_2(S)=\int_S(\bar s vq+2\lVert x-x_0\rVert)f(x)\,dx.
--   $$
--   The corrected error scale is $\eta=\varepsilon/\min\{\mu_1(R)/m,(vq/a)(1-a\mu_2(R)/(mvq))\}$.
--
--   These definitions support comparison of the full-region and single-vehicle district leading terms.
--
--   **Formalization Note** The source prints a maximum in $\eta$; the minimum is required by its proof. The conditional density is used only when $p(S)>0$. The stochastic routing process is outside this definition file.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3 pp. 6–8 (PDF 7–9), proof of Theorem 5 p. ec4 (PDF 41), §4 pp. 14–15 (PDF 15–16), Proposition 3 p. 21 (PDF 22)

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

noncomputable section

namespace CarlssonPartition.Approx

structure Instance where
  R : Set CarlssonPartition.Equitable.Plane
  x0 : CarlssonPartition.Equitable.Plane
  f : CarlssonPartition.Equitable.Plane → ℝ
  m : ℕ
  v : ℝ
  q : ℕ
  sbar : ℝ
  beta : ℝ

def Instance.Standing (I : Instance) : Prop :=
  IsCompact I.R ∧ Convex ℝ I.R ∧ I.x0 ∈ I.R ∧
  (∀ x ∈ I.R, 0 ≤ I.f x) ∧
  (∃ K : NNReal, LipschitzOnWith K I.f I.R) ∧
  (∫ x in I.R, I.f x) = 1 ∧
  1 ≤ I.m ∧ 0 < I.v ∧ 1 ≤ I.q ∧ 0 ≤ I.sbar ∧ 0 < I.beta

def Instance.workload (I : Instance) (k : ℕ) (lam : ℝ)
    (S : Set CarlssonPartition.Equitable.Plane) (g : CarlssonPartition.Equitable.Plane → ℝ) : ℝ :=
  lam * I.sbar / (k : ℝ) +
    2 * lam * (∫ x in S, ‖x - I.x0‖ * g x) /
      ((k : ℝ) * I.v * (I.q : ℝ))

def Instance.bvrLeading (I : Instance) (k : ℕ) (lam : ℝ)
    (S : Set CarlssonPartition.Equitable.Plane) (g : CarlssonPartition.Equitable.Plane → ℝ) : ℝ :=
  I.beta ^ 2 * lam * (1 - 1 / (I.q : ℝ)) ^ 2 *
    (∫ x in S, Real.sqrt (g x)) ^ 2 /
      (2 * (k : ℝ) ^ 2 * I.v ^ 2 * (1 - I.workload k lam S g) ^ 2)

def Instance.pr (I : Instance) (S : Set CarlssonPartition.Equitable.Plane) : ℝ :=
  ∫ x in S, I.f x

def Instance.lamSub (I : Instance) (lam : ℝ) (S : Set CarlssonPartition.Equitable.Plane) : ℝ :=
  lam * I.pr S

def Instance.fSub (I : Instance) (S : Set CarlssonPartition.Equitable.Plane) (x : CarlssonPartition.Equitable.Plane) : ℝ :=
  I.f x / I.pr S

def Instance.IsPartition (I : Instance) (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) : Prop :=
  (∀ i, MeasureTheory.NullMeasurableSet (Rs i) MeasureTheory.volume) ∧
  (∀ i j, i ≠ j → MeasureTheory.AEDisjoint MeasureTheory.volume (Rs i) (Rs j)) ∧
  (⋃ i, Rs i) = I.R

def Instance.mu1 (I : Instance) (S : Set CarlssonPartition.Equitable.Plane) : ℝ :=
  ∫ x in S, Real.sqrt (I.f x)

def Instance.mu2 (I : Instance) (S : Set CarlssonPartition.Equitable.Plane) : ℝ :=
  ∫ x in S, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x

def Instance.eta (I : Instance) (lam ε : ℝ) : ℝ :=
  (min ((1 / (I.m : ℝ)) * I.mu1 I.R)
    (I.v * (I.q : ℝ) / lam *
      (1 - lam * I.mu2 I.R / ((I.m : ℝ) * I.v * (I.q : ℝ)))))⁻¹ * ε

end CarlssonPartition.Approx


