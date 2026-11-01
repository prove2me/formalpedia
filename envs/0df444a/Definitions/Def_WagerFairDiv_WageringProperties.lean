-- Prove2me | Definitions.Def_WagerFairDiv_WageringProperties
-- name    : WagerFairDiv_WageringProperties
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:00.250776+00:00
-- url     : https://prove2.me/theorems/e94b4a66-fc04-4d43-88db-b69c0a685970
-- title:
--   Individual rationality, budget balance, incentive compatibility, profitable side bets and side-bet Pareto optimality (Definitions 5–9)
-- statement:
--   Let $\mathcal B$ be a mechanism on report profiles $\hat{\mathbf p}\in\Delta_m^n$ and positive wagers $\mathbf w$, with $W=\sum_i w_i$; $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)$ is the number of type-$j$ securities of agent $i$.
--
--   1. **Individually rational** (Definition 5, p.3): for every agent $i$ with beliefs $\mathbf p_i$ there is a report $\hat{\mathbf p}_i$ such that for all $\hat{\mathbf p}_{-i}$ and $\mathbf w$, $\sum_{j=1}^m p_{i,j}\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)\ge w_i$.
--   2. **Weakly / strictly budget balanced** (Definition 6, p.3): for all $\hat{\mathbf p}$, $\mathbf w$ and $j$, $\sum_{i=1}^n\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)\le W$, resp. $=W$.
--   3. **Budget balanced on reported support** (not in the paper; the correction of Theorem 3): for all $\hat{\mathbf p}$, $\mathbf w$ and every $j$ with $\hat p_{k,j}>0$ for some agent $k$, $\sum_{i}\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W$.
--   4. **Weakly / strictly incentive compatible** (Definition 7, p.3): for every agent $i$ with beliefs $\mathbf p_i$, all $\hat{\mathbf p}$ and $\mathbf w$,
--   $$\sum_{j=1}^m p_{i,j}\mathcal B_{i,j}((\mathbf p_i,\hat{\mathbf p}_{-i}),\mathbf w)\ \ge\ \sum_{j=1}^m p_{i,j}\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w),$$
--   strictly whenever $\mathbf p_i\ne\hat{\mathbf p}_i$ for strict IC.
--   5. **Profitable side bet** (Definition 8, p.4): given reports $\hat{\mathbf p}$ and security allocations $b_{i,j}$, a matrix $\Delta\mathbf b$ with (1) $\sum_i\Delta b_{i,j}=0$ for every $j$; (2) $\min_j(b_{i,j}+\Delta b_{i,j})\ge0$ for every $i$; (3) $\sum_j\hat p_{i,j}\Delta b_{i,j}\ge0$ for every $i$, strictly for at least one $i$.
--   6. **Side-bet Pareto optimal** (Definition 9, p.4): for all $\hat{\mathbf p}$ and $\mathbf w$, $\mathcal B(\hat{\mathbf p},\mathbf w)$ admits no profitable side bet.
--
--   These are the wagering properties that Theorems 1–3 match with fair-division properties.
--
--   **Formalization Note** In individual rationality the report $\hat{\mathbf p}_i$ is chosen before $\hat{\mathbf p}_{-i}$ and $\mathbf w$; quantifying over full profiles with agent $i$'s entry overwritten (`Function.update`) is the same as quantifying over $\hat{\mathbf p}_{-i}$. Condition (2) of a side bet is stated entrywise. Strict IC is weak IC plus strictness on every misreport. The predicate `BBOnSupport` is introduced for the corrected Theorem 3: strict budget balance implies it.
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Definition 5 (individually rational), p.3; Definition 6 (weakly / strictly budget balanced), p.3; Definition 7 (weakly / strictly incentive compatible), p.3; Definition 8 (profitable side bet), p.4; Definition 9 (side-bet Pareto optimal), p.4; BBOnSupport: correction of Theorem 3, p.5 (proof A.3, p.14). PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model

namespace WagerFairDiv

variable {n m : ℕ}

/-- **Individual rationality** (Definition 5, p.3): for any agent `i` with beliefs `pᵢ` there is
a report `p̂ᵢ` such that for all `p̂₋ᵢ` and `w`, `Σⱼ pᵢ,ⱼ Bᵢ,ⱼ(p̂, w) ≥ wᵢ`.

**Formalization Note.** The report `r = p̂ᵢ` is chosen before the other reports and the wagers,
so it depends on `i` and `pᵢ` only; the quantifier over `p̂₋ᵢ` is a quantifier over full
profiles `p̂`, with `i`'s entry overwritten by `Function.update`. -/
def IndivRational (B : Mech n m) : Prop :=
  ∀ (i : Fin n) (pi : stdSimplex ℝ (Fin m)), ∃ r : stdSimplex ℝ (Fin m),
    ∀ (p : Profile n m) (w : PosVec n), w.1 i ≤ val pi.1 (B (Function.update p i r) w i)

/-- **Weak budget balance** (Definition 6, p.3): for all `p̂`, `w` and every outcome `j`,
`Σᵢ Bᵢ,ⱼ(p̂, w) ≤ W`. -/
def WeaklyBB (B : Mech n m) : Prop :=
  ∀ (p : Profile n m) (w : PosVec n) (j : Fin m), ∑ i, B p w i j ≤ w.total

/-- **Strict budget balance** (Definition 6, p.3): for all `p̂`, `w` and every outcome `j`,
`Σᵢ Bᵢ,ⱼ(p̂, w) = W`. -/
def StrictlyBB (B : Mech n m) : Prop :=
  ∀ (p : Profile n m) (w : PosVec n) (j : Fin m), ∑ i, B p w i j = w.total

/-- **Budget balance on reported support** (not in the paper; used to correct Theorem 3, p.5):
for all `p̂`, `w` and every outcome `j` to which **some** agent reports positive probability,
`Σᵢ Bᵢ,ⱼ(p̂, w) = W`. Strict budget balance (Definition 6) implies it; it says nothing about
outcomes every agent reports impossible.

**Formalization Note.** The printed Theorem 3 requires strict budget balance; that "only if" is
false (a Pareto optimal allocation mechanism may waste a good nobody values). This predicate is
the minimal correction under which the equivalence of Theorem 3 holds. -/
def BBOnSupport (B : Mech n m) : Prop :=
  ∀ (p : Profile n m) (w : PosVec n) (j : Fin m), (∃ i, 0 < (p i).1 j) →
    ∑ i, B p w i j = w.total

/-- **Weak incentive compatibility** of a wagering mechanism (Definition 7, p.3): for every agent
`i` with beliefs `pᵢ`, all reports `p̂` and wagers `w`,
`Σⱼ pᵢ,ⱼ Bᵢ,ⱼ((pᵢ, p̂₋ᵢ), w) ≥ Σⱼ pᵢ,ⱼ Bᵢ,ⱼ(p̂, w)`.

**Formalization Note.** `(pᵢ, p̂₋ᵢ)` is `Function.update p̂ i pᵢ`. -/
def WagerWeakIC (B : Mech n m) : Prop :=
  ∀ (i : Fin n) (pi : stdSimplex ℝ (Fin m)) (p : Profile n m) (w : PosVec n),
    val pi.1 (B p w i) ≤ val pi.1 (B (Function.update p i pi) w i)

/-- **Strict incentive compatibility** of a wagering mechanism (Definition 7, p.3): the inequality
of weak incentive compatibility holds, and it is strict whenever `pᵢ ≠ p̂ᵢ`.

**Formalization Note.** Encoded as weak IC together with strictness on every misreport, as for
allocation mechanisms. -/
def WagerStrictIC (B : Mech n m) : Prop :=
  WagerWeakIC B ∧
    ∀ (i : Fin n) (pi : stdSimplex ℝ (Fin m)) (p : Profile n m) (w : PosVec n), pi ≠ p i →
      val pi.1 (B p w i) < val pi.1 (B (Function.update p i pi) w i)

/-- A **profitable side bet** (Definition 8, p.4): given reports `p̂` and security allocations
`bᵢ,ⱼ`, the change `Δb` is a profitable side bet if
1. `Σᵢ Δbᵢ,ⱼ = 0` for every `j`;
2. `minⱼ (bᵢ,ⱼ + Δbᵢ,ⱼ) ≥ 0` for every `i`;
3. `Σⱼ p̂ᵢ,ⱼ Δbᵢ,ⱼ ≥ 0` for every `i`, with strict inequality for at least one `i`.

**Formalization Note.** Condition 2 is stated entrywise, `0 ≤ bᵢ,ⱼ + Δbᵢ,ⱼ` for all `i, j`
(the same for `m ≥ 1`; the minimum over an empty set of outcomes is undefined in the paper). -/
def ProfitableSideBet (p : Profile n m) (b db : Fin n → Fin m → ℝ) : Prop :=
  (∀ j, ∑ i, db i j = 0) ∧ (∀ i j, 0 ≤ b i j + db i j) ∧
    (∀ i, 0 ≤ val (p i).1 (db i)) ∧ ∃ i, 0 < val (p i).1 (db i)

/-- **Side-bet Pareto optimality** (Definition 9, p.4): for all reports `p̂` and wagers `w`, the
allocation `B(p̂, w)` does not permit a profitable side bet. -/
def SideBetPO (B : Mech n m) : Prop :=
  ∀ (p : Profile n m) (w : PosVec n), ¬ ∃ db, ProfitableSideBet p (B p w) db

end WagerFairDiv


