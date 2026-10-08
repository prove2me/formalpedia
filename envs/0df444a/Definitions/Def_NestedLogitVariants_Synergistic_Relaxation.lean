-- Prove2me | Definitions.Def_NestedLogitVariants_Synergistic_Relaxation
-- name    : NestedLogitVariants_Synergistic_Relaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:25:51.804569+00:00
-- url     : https://prove2.me/theorems/ddb1f0e7-cc89-477d-9c06-1c3350f1166d
-- title:
--   (7), (8), p. 20–21 — the tighter problem (7), the objective of (8), Lemma 6's shape and the sums R_ik′, q_ik′
-- statement:
--   Let $z_i = (z_{i1}, \dots, z_{in}) \in [0,1]^n$ be a vector of fractional offer levels in nest $i$. The objective of the maximization problem (8) at the point $x$ is
--
--   $$F_i(z_i, x) = \Big(\sum_{j \in N} v_{ij} z_{ij}\Big)^{\gamma_i} \left[\frac{\sum_{j \in N} r_{ij} v_{ij} z_{ij}}{\sum_{j \in N} v_{ij} z_{ij}} - x\right],$$
--
--   written, as on the page, without a no-purchase weight $v_{i0}$ (the nests of §4 are fully captured). A pair $(x, y)$ is feasible for problem (7) when
--
--   $$v_0 x \ge \sum_{i \in M} y_i, \qquad y_i \ge F_i(z_i, x) \quad \text{for all } z_i \in [0,1]^n,\ i \in M,$$
--
--   which is the constraint $y_i \ge \max_{z_i \in [0,1]^n} F_i(z_i, x)$ of (7). A vector $z_i$ has the shape of Lemma 6 at product $k$ when $z_{i1} = \dots = z_{i,k-1} = 1$, $z_{ik} \in [0,1]$ and $z_{i,k+1} = \dots = z_{in} = 0$. Finally, as in Appendix A.1 (p. 41),
--
--   $$R_{ik'} = \sum_{j=1}^{k'} r_{ij} v_{ij}, \qquad q_{ik'} = \sum_{j=1}^{k'} v_{ij},$$
--
--   the sums over the nested-by-revenue assortment $N_{ik'}$.
--
--   Problem (7) restricts (3) by allowing fractional assortments; it is the device through which the paper proves the performance guarantee of the nested-by-revenue assortments.
--
--   **Formalization Note** Products are indexed from $0$ (`Fin n`); the product $k$ of the shape is a `Fin n`. At $z_i = 0$ the objective is $0^{\gamma_i}(0/0 - x) = 0$ (real power, $0/0 = 0$), its limit value. The maximum in (7) is encoded as "for every $z_i$ in the box", so no supremum is taken.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 20–21, displays (7) and (8), Lemma 6; Appendix A.1, p. 41 (R_ik′, q_ik′)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Model
import Definitions.Def_NestedLogitVariants_LP_UpperBound

namespace NestedLogitVariants.Synergistic

variable {ι : Type*} {n : ℕ}

/-- The objective of the maximization problem (8) (p. 21) for nest `i` at the point `x`:
`(∑_{j ∈ N} v_{ij} z_{ij})^{γ_i} [∑_{j ∈ N} r_{ij} v_{ij} z_{ij} / ∑_{j ∈ N} v_{ij} z_{ij} − x]`,
as printed, without `v_{i0}` (the nests of §4 are fully captured). At `z = 0` its value is
`0 ^ γ_i * (0 / 0 − x) = 0` (`Real.rpow`, `0 / 0 = 0`). -/
noncomputable def F8 (I : Instance ι n) (i : ι) (z : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ j, I.v i j * z j) ^ I.γ i * ((∑ j, I.r i j * I.v i j * z j) / (∑ j, I.v i j * z j) - x)

/-- `(x, y)` is feasible for problem (7) (p. 20): `v_0 x ≥ ∑_i y_i` and, for every nest `i`,
`y_i ≥ F8 I i z x` for every `z ∈ [0, 1]^n`, which is the constraint
`y_i ≥ max_{z_i ∈ [0,1]^n} {…}` written without a supremum. -/
def LP7Feasible [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧ ∀ i, ∀ z ∈ NestedLogitVariants.LP.box n, F8 I i z x ≤ y i

/-- The shape of Lemma 6 (p. 21): `z_1 = ⋯ = z_{k−1} = 1`, `z_k ∈ [0, 1]`,
`z_{k+1} = ⋯ = z_n = 0`, for the product `k` (here a `Fin n`, products indexed from `0`). -/
def IsFracPrefix (z : Fin n → ℝ) (k : Fin n) : Prop :=
  (∀ j, j < k → z j = 1) ∧ z k ∈ Set.Icc 0 1 ∧ ∀ j, k < j → z j = 0

/-- `R_{ik'} = ∑_{j=1}^{k'} r_{ij} v_{ij}` (Appendix A.1, p. 41): the revenue-weighted sum over the
first `k'` products of nest `i`, i.e. over `N_{ik'}`. -/
def Rsum (I : Instance ι n) (i : ι) (k' : ℕ) : ℝ := ∑ j ∈ nbr n k', I.r i j * I.v i j

/-- `q_{ik'} = ∑_{j=1}^{k'} v_{ij}` (Appendix A.1, p. 41): the total weight of the first `k'` products
of nest `i`, i.e. of `N_{ik'}`. -/
def qsum (I : Instance ι n) (i : ι) (k' : ℕ) : ℝ := ∑ j ∈ nbr n k', I.v i j

end NestedLogitVariants.Synergistic


