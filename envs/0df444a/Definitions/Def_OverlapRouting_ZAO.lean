-- Prove2me | Definitions.Def_OverlapRouting_ZAO
-- name    : OverlapRouting_ZAO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:55.485209+00:00
-- url     : https://prove2.me/theorems/0b97af93-4f19-4cec-a396-00da3ca5347e
-- title:
--   $Z^{AO(\alpha)}$, $Z^*$, $\mathbb E[R_j]$, $r_{avg}$, α-optimal labellings, $c_i$, $L_j$, $L'_j$
-- statement:
--   Fix $N'$ customers per primary route, capacity $Q$, a demand law $D$ and a depot $x_0$. For the instance with $M$ vehicles and customer locations $x_1,\dots,x_N$ ($N=N'M$):
--
--   1. A **labelling** is a bijection between labels and customers. It is **α-optimal** if the closed tour through the customers in label order has length at most $\alpha L^*$.
--   2. $Z^{AO(\alpha)}$ is the expected daily AO cost (Algorithm 1 on the labelled customers) over i.i.d. demands $D_i\sim D$.
--   3. $Z^*$ is the expected optimal split-delivery VRP distance $\mathbb E[\mathrm{VRP}^*(\mathbf D)]$.
--   4. $\mathbb E[R_j]$ is the expected trip count $\mathbb E[r_j]$ of vehicle $j$, and $r_{avg}=\frac1M\sum_{j=1}^M\mathbb E[R_j]$.
--   5. $c_i=\|x_0-x_i\|_2$; $\sum_{i\in\mathcal N_j}c_i$ is taken over the labelled customers of $\mathcal N_j$.
--   6. $L_j$ is the length of the open path through $\mathcal N_j$ in label order, and $L'_j$ that through $\mathcal E_j$ ($L'_M=L_M$).
--
--   These are the quantities compared in Lemmas 1–7, Proposition 1 and Theorem 1.
--
--   **Formalization Note** Expectations are finite sums over demand vectors. The demand of the customer with label $k$ is $d_{\ell(k)}$, so $Z^{AO(\alpha)}$ is literally the expectation over customer demands. Locations and demands are extended by $0$ beyond label $N-1$; those values are never read.
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, §4, pp.11–14 (Z*, L*, α-optimal labelling, Lⱼ, L′ⱼ, Z^{AO(α)}, Rⱼ, r_avg); Table 1, p.6

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO

namespace OverlapRouting

/-! The cost quantities of §4 of Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022), pp.11–17,
for the instance with `M` vehicles and `N = N′M` customers. -/

/-- The demand vector `d` of `n` customers read as a function on labels `ℕ`, `0` beyond `n`. -/
def extendDemand {u n : ℕ} (d : Fin n → Fin (u + 1)) : ℕ → ℕ :=
  fun i => if h : i < n then ((d ⟨i, h⟩ : Fin (u + 1)) : ℕ) else 0

/-- The location vector `y` of `n` customers read as a function on labels `ℕ`, `0` beyond `n`
(those labels are never read). -/
noncomputable def extendPoints {n : ℕ} (y : Fin n → Point) : ℕ → Point :=
  fun i => if h : i < n then y ⟨i, h⟩ else 0

/-- `Z^{AO(α)}`, the expected travel cost of the adjacent overlapping strategy (p.13) for customer
locations `x` (customer `c` at `x c`) and the labelling `ℓ`: the customer with label `k` is
`ℓ k`. The expectation is over the i.i.d. daily demands `Dᵢ ∼ D`, served by Algorithm 1 with
capacity `Q`, `M` vehicles and `N′` customers per primary route.

**Formalization Note.** The labelling is a permutation; `α` enters only through the hypothesis
that `ℓ` is `α`-optimal (`IsAlphaOptimal`). The expectation is the finite sum over demand
vectors. -/
noncomputable def ZAO (N' Q : ℕ) (D : DemandLaw) (x₀ : Point) (M : ℕ)
    (x : Fin (N' * M) → Point) (ℓ : Equiv.Perm (Fin (N' * M))) : ℝ :=
  D.expect (N' * M) fun d => costAO N' Q M x₀ (extendPoints (x ∘ ℓ)) (extendDemand (d ∘ ℓ))

/-- `Z*`, "the travel cost of reoptimization" (pp.11–12; Table 1, p.6): the expectation over the
i.i.d. daily demands of the optimal split-delivery VRP distance `vrpOpt` for `N` customers at
`x`, depot `x₀` and capacity `Q`. -/
noncomputable def Zstar (Q : ℕ) (D : DemandLaw) (x₀ : Point) {N : ℕ} (x : Fin N → Point) : ℝ :=
  D.expect N fun d => vrpOpt x₀ x Q fun i => (((d i : Fin (D.u + 1)) : ℕ) : ℝ)

/-- `E[Rⱼ]`, the expected number of trips of vehicle `j` under the AO strategy (p.13), with `Rⱼ`
the trip count `rⱼ` of display (3), p.14, under the random demands of the instance with `M`
vehicles. It does not depend on the locations. -/
noncomputable def expTrips (N' Q : ℕ) (D : DemandLaw) (M j : ℕ) : ℝ :=
  D.expect (N' * M) fun d => (trips N' Q (extendDemand d) j : ℝ)

/-- `r_avg = ∑_{j=1}^{M} E[Rⱼ]/M` (p.14; Table 1, p.6). -/
noncomputable def rAvg (N' Q : ℕ) (D : DemandLaw) (M : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 M, expTrips N' Q D M j) / M

/-- The labelling `ℓ` is **α-optimal** (§4.1, p.13): "customers `1 → 2 → … N → 1` form an
α-optimal TSP tour, i.e., the tour's length is at most `α` times the distance of the optimal TSP
through all customers". -/
def IsAlphaOptimal (α : ℝ) {n : ℕ} (x : Fin n → Point) (ℓ : Equiv.Perm (Fin n)) : Prop :=
  closedTourLength (x ∘ ℓ) ≤ α * tspOpt x

/-- `∑_{i ∈ 𝒩ⱼ} cᵢ` with `cᵢ = ‖x₀ − xᵢ‖₂` (p.5) for the labelled locations `pt`. -/
noncomputable def groupDepotDist (N' : ℕ) (x₀ : Point) (pt : ℕ → Point) (j : ℕ) : ℝ :=
  ∑ i ∈ primaryRoute N' j, dist x₀ (pt i)

/-- `Lⱼ`, "the distance of travelling through `𝒩ⱼ`" (p.13): the open path through the labels of
`𝒩ⱼ` in label order, `∑_{(j−1)N′ ≤ i < jN′ − 1} ‖pt i − pt (i+1)‖`. -/
noncomputable def primaryPathLength (N' : ℕ) (pt : ℕ → Point) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico ((j - 1) * N') (j * N' - 1), dist (pt i) (pt (i + 1))

/-- `L′ⱼ`, "the distance of travelling through `ℰⱼ`" (p.13): the open path through the labels of
`ℰⱼ = 𝒩ⱼ ∪ 𝒩ⱼ₊₁` in label order for `j < M`, and `L′_M = L_M` since `ℰ_M = 𝒩_M` (p.10). -/
noncomputable def extendedPathLength (N' M : ℕ) (pt : ℕ → Point) (j : ℕ) : ℝ :=
  if j < M then ∑ i ∈ Finset.Ico ((j - 1) * N') ((j + 1) * N' - 1), dist (pt i) (pt (i + 1))
  else primaryPathLength N' pt j

end OverlapRouting


