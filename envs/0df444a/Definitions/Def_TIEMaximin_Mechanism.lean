-- Prove2me | Definitions.Def_TIEMaximin_Mechanism
-- name    : TIEMaximin_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:44.519603+00:00
-- url     : https://prove2.me/theorems/1374d81f-da1e-43c4-9911-180695cca8b4
-- title:
--   Randomized mechanisms, truthfulness-in-expectation, ex-ante envy-freeness
-- statement:
--   A **randomized mechanism** $\mathcal M$ maps every reported valuation profile to a lottery over allocations. It is **truthful in expectation** if for every agent $i$, true valuation $v_i$, report $v_i'$ and reports $v_{-i}$ of the others,
--
--   $$\mathbb E_{A\sim\mathcal M(v_i,v_{-i})}[v_i(A_i)]\ge\mathbb E_{A\sim\mathcal M(v_i',v_{-i})}[v_i(A_i)],$$
--
--   and **ex-ante envy-free** if $\mathbb E_{A\sim\mathcal M(v)}[v_i(A_i)]\ge\mathbb E_{A\sim\mathcal M(v)}[v_i(A_j)]$ for every profile $v$ and all agents $i,j$. The **uniform-recipient mechanism** of the boundary cases gives all goods to one agent chosen uniformly at random, independently of the reports.
--
--   **Formalization Note** All quantifiers range over nonnegative valuations (`Nonneg`), including misreports that change the agent's order of the goods; a mechanism's output on other inputs is unconstrained.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definitions 2.2, 2.6, pp.7–8; §2, p.8

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Shares

namespace TIEMaximin

/-- **Randomized mechanisms** (§2, p.7): a map from reported valuation profiles to lotteries over
allocations, `M : V_add^n → Δ(𝒜)`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §2, p.7.

**Formalization Note.** The domain is all real matrices; every property below only constrains
the mechanism on nonnegative profiles (`Nonneg`), so its output on other inputs is irrelevant. -/
abbrev Mech (n m : ℕ) : Type := (Fin n → Fin m → ℝ) → PMF (Alloc n m)

/-- **Truthfulness-in-expectation** (Definition 2.2, p.7): for every agent `i`, every true
valuation `v_i`, every report `v'_i` and every profile `v_{−i}` of the others (all nonnegative),
`E_{A∼M(v_i, v_{−i})}[v_i(A_i)] ≥ E_{A∼M(v'_i, v_{−i})}[v_i(A_i)]`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 2.2, p.7.

**Formalization Note.** The true profile is `v` (agent `i`'s true valuation `v i`, the others'
reports `v j`); the misreport `w` replaces row `i` (`Function.update v i w`). `w` ranges over all
nonnegative valuations, including those that change agent `i`'s order of the goods. -/
def IsTIE {n m : ℕ} (M : Mech n m) : Prop :=
  ∀ v : Fin n → Fin m → ℝ, Nonneg v → ∀ (i : Fin n) (w : Fin m → ℝ), (∀ g, 0 ≤ w g) →
    expect (M (Function.update v i w)) (valOf (v i) i) ≤ expect (M v) (valOf (v i) i)

/-- **Ex-ante envy-freeness** (Definition 2.6, p.8): for every (nonnegative) profile `v` and all
agents `i, j`, `E_{A∼M(v)}[v_i(A_i)] ≥ E_{A∼M(v)}[v_i(A_j)]`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 2.6, p.8. -/
def IsExAnteEF {n m : ℕ} (M : Mech n m) : Prop :=
  ∀ v : Fin n → Fin m → ℝ, Nonneg v → ∀ i j : Fin n,
    expect (M v) (valOf (v i) j) ≤ expect (M v) (valOf (v i) i)

/-- **The uniform-recipient mechanism** of the boundary cases (§2, p.8): independently of the
reports, all goods go to one agent chosen uniformly at random.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §2, p.8: "giving all goods to an
agent chosen uniformly at random, independently of the reports".

**Formalization Note.** `NeZero n` (i.e. `0 < n`) is needed for a uniform distribution on the
agents. For `n = 1` it gives the sole agent all goods, and for `m = 0` it is the empty allocation. -/
noncomputable def uniformRecipient (n m : ℕ) [NeZero n] : Mech n m :=
  fun _ => (PMF.uniformOfFintype (Fin n)).map (fun i => fun _ : Fin m => i)

end TIEMaximin


