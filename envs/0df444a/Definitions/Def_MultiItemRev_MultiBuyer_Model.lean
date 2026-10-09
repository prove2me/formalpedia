-- Prove2me | Definitions.Def_MultiItemRev_MultiBuyer_Model
-- name    : MultiItemRev_MultiBuyer_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:24.596574+00:00
-- url     : https://prove2.me/theorems/4894ddd1-166d-4b27-a7e2-c940d6ada14e
-- title:
--   §A.7, pp. 46–48 — n buyers: mechanisms (qʲ, sʲ) with Σⱼ qʲᵢ ≤ 1, IC-DS, IR-DS, NPT, R(µ;X), Rev^DS, two independent goods, y^(1)
-- statement:
--   One seller sells $k$ goods to $n$ buyers. A **valuation profile** is $x = (x^j_i)_{j=1,\dots,n;\,i=1,\dots,k} \in \mathbb R^{kn}_+$, where $x^j_i \ge 0$ is the value of buyer $j$ for good $i$; $x^j = (x^j_i)_i \in \mathbb R^k_+$ is buyer $j$'s valuation vector. A random profile $X$ enters only through its joint law $F$ on $\mathbb R^{kn}_+$; the buyers may be arbitrarily correlated.
--
--   1. A (direct) **mechanism** $\mu = (q^j, s^j)_{j=1,\dots,n}$ consists, for each buyer $j$, of an allocation function $q^j : \mathbb R^{kn}_+ \to [0,1]^k$ and a payment function $s^j : \mathbb R^{kn}_+ \to \mathbb R$, subject to the **feasibility** condition $\sum_{j=1}^n q^j_i(x) \le 1$ for every good $i$ and every $x$.
--   2. Buyer $j$'s payoff is $b^j(x) = q^j(x)\cdot x^j - s^j(x)$; the seller's revenue is $S(x) = \sum_{j=1}^n s^j(x)$.
--   3. **IC-DS** (dominant-strategy incentive compatibility): for every $j$, every $x \in \mathbb R^{kn}_+$ and every report $\tilde x^j \in \mathbb R^k_+$,
--   $$b^j(x) \ge q^j(\tilde x^j, x^{-j})\cdot x^j - s^j(\tilde x^j, x^{-j}),$$
--   where $(\tilde x^j, x^{-j})$ is the profile $x$ with buyer $j$'s vector replaced by $\tilde x^j$. **IR-DS**: $b^j(x) \ge 0$ for every $j$ and $x$. **NPT** (no positive transfer): $s^j(x) \ge 0$ for every $j$ and $x$.
--   4. The seller's **expected revenue** is $R(\mu; X) = \mathbb E[S(X)] \in [-\infty, +\infty]$, and
--   $$\mathrm{Rev}^{DS}(X) = \sup\{R(\mu; X) : \mu \text{ feasible, IC-DS and IR-DS, with measurable payments}\} \in [0,\infty].$$
--   5. For one good, $Y = (Y^j)_{j} \in \mathbb R^n_+$ is the vector of the buyers' values; for two goods with value vectors $Y$ and $Z$, the profile is $X = (Y, Z)$, and "the two goods are independent" means that the law of $(Y,Z)$ is the product of the laws of $Y$ and $Z$.
--   6. $a^{(1)} = \max_j a^j$ is the maximal coordinate of $a \in \mathbb R^n$, and $X\mathbf 1_{X\in A}$ is the profile that equals $X$ on the event $X \in A$ and $0$ otherwise.
--   7. For a two-good mechanism $(q,s)$ and a fixed vector $z \in \mathbb R^n_+$ of values for the second good, the **marginal mechanism** for the first good is $\hat q^j(y) = q^j_1(y,z)$, $\hat s^j(y) = s^j(y,z) - q^j_2(y,z)\,z^j$.
--
--   These are the objects of Theorem 33 and of the steps of its proof.
--
--   **Formalization Note** A profile is `x : Fin n → ι → ℝ≥0` (`x j i` $= x^j_i$), and a random profile is its law `μ`. The report $(\tilde x^j, x^{-j})$ is `Function.update x j x'`. $R(\mu;X)$ is computed in `EReal` as $\int S^+ - \int S^-$ (never the Bochner integral, which is $0$ for non-integrable $S$); `RevDS` clips each value at $0$ with `toENNReal`, which does not change the supremum since the zero mechanism is admissible. Payments are required measurable, as in the paper's footnote 12. One good is `ι = Unit`, two goods are `ι = Fin 2` (good 1 is index `0`, good 2 is index `1`); `twoGoodsN μY μZ` is the image of the product law `μY ⊗ μZ`. `maxCoord` is `Finset.univ.sup`, which is $0$ when $n = 0$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 46–48, Appendix A.7 (model, IC-DS, IR-DS, R(µ;X), Rev^DS, Remark (b) NPT); p. 49, footnote 45 (y^(1)); pp. 49–50, proof of Theorems 33 and 34 (marginal mechanism)

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-!
# Selling `k` goods to `n` buyers (Hart–Nisan, Appendix A.7, pp. 46–48)

A valuation profile is `x : Fin n → ι → ℝ≥0`, with `x j i = x^j_i` the value of buyer `j` for good `i`.
A random profile `X` enters only through its law `μ : Measure (Fin n → ι → ℝ≥0)`.
-/

/-- A (direct) mechanism `µ = (q^j, s^j)_{j=1,…,n}` (p. 46): for each buyer `j` an allocation
`q^j : ℝ^{kn}_+ → [0,1]^k` (here `q x j i`) and a payment `s^j : ℝ^{kn}_+ → ℝ` (here `s x j`). -/
structure MechanismN (n : ℕ) (ι : Type*) where
  q : (Fin n → ι → ℝ≥0) → Fin n → ι → ℝ
  s : (Fin n → ι → ℝ≥0) → Fin n → ℝ

/-- The payoff of buyer `j`, `b^j(x) = q^j(x) · x^j - s^j(x)` (p. 46). -/
def payoffN {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι) (x : Fin n → ι → ℝ≥0)
    (j : Fin n) : ℝ :=
  ∑ i, M.q x j i * (x j i : ℝ) - M.s x j

/-- `q^j(x) ∈ [0,1]^k` for every buyer, and `∑_j q^j_i(x) ≤ 1` for every good `i` (p. 46). -/
def IsFeasibleN {n : ℕ} {ι : Type*} (M : MechanismN n ι) : Prop :=
  (∀ x j i, 0 ≤ M.q x j i ∧ M.q x j i ≤ 1) ∧ ∀ x i, ∑ j, M.q x j i ≤ 1

/-- IC-DS (p. 47): no buyer `j` gains by reporting `x̃^j` instead of `x^j`, whatever the reports
`x^{-j}` of the others; `(x̃^j, x^{-j})` is `Function.update x j x̃`. -/
def IsICDS {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι) : Prop :=
  ∀ (x : Fin n → ι → ℝ≥0) (j : Fin n) (x' : ι → ℝ≥0),
    ∑ i, M.q (Function.update x j x') j i * (x j i : ℝ) - M.s (Function.update x j x') j ≤
      payoffN M x j

/-- IR-DS (p. 47): `b^j(x) ≥ 0` for every buyer `j` and every profile `x`. -/
def IsIRDS {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι) : Prop :=
  ∀ x j, 0 ≤ payoffN M x j

/-- No positive transfer (p. 48): `s^j(x) ≥ 0` for every `j` and `x`. -/
def IsNPTN {n : ℕ} {ι : Type*} (M : MechanismN n ι) : Prop :=
  ∀ x j, 0 ≤ M.s x j

/-- Feasible, IC-DS and IR-DS mechanisms with measurable payments (footnote 12). -/
def IsAdmissibleDS {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι) : Prop :=
  IsFeasibleN M ∧ IsICDS M ∧ IsIRDS M ∧ ∀ j, Measurable (fun x => M.s x j)

/-- The seller's revenue `S(x) = ∑_j s^j(x)` (p. 46). -/
def sellerRevenue {n : ℕ} {ι : Type*} (M : MechanismN n ι) (x : Fin n → ι → ℝ≥0) : ℝ :=
  ∑ j, M.s x j

/-- The expected revenue `R(µ; X) = E[S(X)]` (p. 47), in `EReal`. -/
noncomputable def expRevenueN {n : ℕ} {ι : Type*} (μ : Measure (Fin n → ι → ℝ≥0))
    (M : MechanismN n ι) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal)

/-- `Rev^{DS}(X)` (p. 47): the supremum of `R(µ; X)` over IC-DS and IR-DS mechanisms. -/
noncomputable def RevDS {n : ℕ} {ι : Type*} [Fintype ι] (μ : Measure (Fin n → ι → ℝ≥0)) : ℝ≥0∞ :=
  ⨆ (M : MechanismN n ι) (_ : IsAdmissibleDS M), (expRevenueN μ M).toENNReal

/-- The law of `X · 1_{X ∈ A}` when `X` has law `μ`. -/
noncomputable def lawOnN {n : ℕ} {ι : Type*} (μ : Measure (Fin n → ι → ℝ≥0))
    (A : Set (Fin n → ι → ℝ≥0)) : Measure (Fin n → ι → ℝ≥0) :=
  μ.map (A.indicator id)

/-- The law of one good's value vector `Y ∈ ℝ^n_+`, viewed as a one-good profile. -/
noncomputable def oneGoodN {n : ℕ} (μY : Measure (Fin n → ℝ≥0)) : Measure (Fin n → Unit → ℝ≥0) :=
  μY.map (fun y j _ => y j)

/-- The law of the two-good profile `X = (Y, Z)` when the value vectors `Y` (law `μY`) and `Z`
(law `μZ`) of the two goods are independent; good 1 is index `0`, good 2 is index `1`. -/
noncomputable def twoGoodsN {n : ℕ} (μY μZ : Measure (Fin n → ℝ≥0)) :
    Measure (Fin n → Fin 2 → ℝ≥0) :=
  (μY.prod μZ).map (fun p j => ![p.1 j, p.2 j])

/-- `a^{(1)} = max_j a^j` (footnote 45); `0` when `n = 0`. -/
noncomputable def maxCoord {n : ℕ} (a : Fin n → ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup a

/-- The marginal mechanism `(q̂, ŝ) = (q̂_z, ŝ_z)` for the first good (p. 49), built from a
two-good mechanism `M` and the second-good values `z`:
`q̂^j(y) = q^j_1(y, z)` and `ŝ^j(y) = s^j(y, z) - q^j_2(y, z) z^j`. -/
def marginalMech {n : ℕ} (M : MechanismN n (Fin 2)) (z : Fin n → ℝ≥0) : MechanismN n Unit where
  q y j _ := M.q (fun l => ![y l (), z l]) j 0
  s y j := M.s (fun l => ![y l (), z l]) j - M.q (fun l => ![y l (), z l]) j 1 * (z j : ℝ)

end MultiItemRev.MultiBuyer


