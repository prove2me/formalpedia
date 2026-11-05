-- Prove2me | Definitions.Def_BlindNRMLS_hardProblem
-- name    : BlindNRMLS_hardProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:14.899722+00:00
-- url     : https://prove2.me/theorems/d965996c-bff6-4eb5-8e44-13f034b6396e
-- title:
--   §4.2, EC.9.1–EC.9.3, pp.19–20, ec40–41, ec49–50 — the hard instances $I_\mu$, families and cover times
-- statement:
--   With $b_i=B_i/T$, the **hard problem** has consumption matrix $A=2[\,0_{d\times1}\ \ \mathrm{diag}(b)\ \ 0_{d\times(n-d-1)}]$ and prices $p_{j,k}=1$ for $j=1$ and $0$ otherwise. Its **instances** $I_\mu$, for $\mu_1,\mu_2\in[-\frac12,\frac12]^K$, have independent Bernoulli demands with means
--   $$
--   q_{j,k;\mu}=\begin{cases}\frac12+\mu_{1,k},& j=1,\\ \frac12-\mu_{2,k},&\text{else if } j=(k-1)\%(d+1)+1,\\ \frac12+\mu_{2,k},&\text{else if } j=k\%(d+1)+1,\\ \frac12,&\text{else if } j\in[2,d+1],\\ 0,&\text{else.}\end{cases}
--   $$
--   The **families** are $\mathcal A_l=\{k:k\%(d+1)=l\%(d+1)\}$ for $l\in[d+1]$.
--
--   On a history, the **frozen action** $z_t$ is the action of the last selling period up to $t$. The **cover times** are $\tau_0=1$ and $\tau_{j+1}=\min\{t\le T:$ all arms are chosen in $[\tau_j:t]\}$, with $\tau=\infty$ if there is no such $t$. $S(a,T)$ counts the switches of the frozen actions inside $[a:T]$.
--
--   These objects carry the lower bound. Lemma EC.3 uses the $\mu$ with $\mu_{1,k}=\eta/(d+1)$ for $k\%(d+1)=1$, $-\eta/(d+1)$ for $k\%(d+1)=0$, $0$ otherwise, and $\mu_{2,k}=\eta$.
--
--   **Formalization Note** Arms and products are $0$-based: source $k$ is `k.val + 1`, source $j$ is `j.val + 1`. For $d=1,K=4$ the entry for product 2 is $\frac12+\mu_{2,k}$ for source arms $1,3$ and $\frac12-\mu_{2,k}$ for arms $2,4$. `bernoulliLaw` clamps its argument to $[0,1]$ to be a total function; the clamp is inert for $\mu$ in the stated ranges. The frozen action is the stop action when not even the first period sells, a case the source does not discuss. Cover times are $0$-based, valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, §4.2, pp.19–20; p.ec40; (EC.40), p.ec41; Lemma EC.3, p.ec42; §EC.9.3, pp.ec49–50

import Mathlib
import Definitions.Def_BlindNRMLS_switchRegret

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

variable {d n K : ℕ}

/-- The hard problem of Theorem 4's proof, pp.19 and ec40, with `b_i = B_i/T`:
`A = 2 [0_{d×1} diag(b) 0_{d×(n-(d+1))}]`, and `p_{j,k} = 1` if `j = 1` and `0` otherwise.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5.

**Formalization Note.** `j : Fin n` is `0`-based: page product `j` is `j.val + 1`, page resource `i`
is `i.val + 1`. All `K` price vectors coincide here. -/
noncomputable def hardProblem (T : ℕ) (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (n K : ℕ) :
    Problem d n K where
  T := T
  B i := b i * T
  p _ j := if j.val = 0 then 1 else 0
  A i j := if j.val = i.val + 1 then 2 * b i else 0
  B_nonneg i := mul_nonneg (hb i) (Nat.cast_nonneg T)
  p_nonneg _ j := by split_ifs <;> norm_num
  A_nonneg i j := by
    split_ifs
    · exact mul_nonneg (by norm_num) (hb i)
    · exact le_rfl

/-- Clamping to `[0,1]`, so that `bernoulliLaw` is a probability measure for every real argument.
It is the identity on `[0,1]`; statements restrict `μ` so that only `[0,1]` occurs. -/
noncomputable def unitClamp (q : ℝ) : ℝ := max 0 (min q 1)

/-- `Ber(q)` as a law on `ℝ`, for `q ∈ [0,1]`. -/
noncomputable def bernoulliLaw (q : ℝ) : Measure ℝ :=
  ENNReal.ofReal (unitClamp q) • Measure.dirac 1 + ENNReal.ofReal (1 - unitClamp q) • Measure.dirac 0

lemma bernoulliLaw_isProb (q : ℝ) : IsProbabilityMeasure (bernoulliLaw q) := by
  refine ⟨?_⟩
  have h0 : 0 ≤ unitClamp q := le_max_left _ _
  have h1 : unitClamp q ≤ 1 := max_le zero_le_one (min_le_right _ _)
  simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma bernoulliLaw_supp (q : ℝ) : bernoulliLaw q (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hm : MeasurableSet (Set.Icc (0 : ℝ) 1)ᶜ := measurableSet_Icc.compl
  simp [bernoulliLaw, Measure.add_apply, Measure.smul_apply, hm]

/-- The mean-demand matrix `q_{j,k;µ}` of p.20:
`1/2 + µ_{1,k}` if `j = 1`; else `1/2 - µ_{2,k}` if `j = (k-1)%(d+1)+1`; else `1/2 + µ_{2,k}` if
`j = k%(d+1)+1`; else `1/2` if `j ∈ [2,d+1]`; else `0`.

**Formalization Note.** Page `k` is `k.val + 1` and page `j` is `j.val + 1`, so
`j = (k-1)%(d+1)+1` reads `j.val = k.val % (d+1)`, and `j = k%(d+1)+1` reads
`j.val = (k.val+1) % (d+1)`. -/
noncomputable def qMu (d : ℕ) (μ₁ μ₂ : Fin K → ℝ) (k : Fin K) (j : Fin n) : ℝ :=
  if j.val = 0 then 1 / 2 + μ₁ k
  else if j.val = k.val % (d + 1) then 1 / 2 - μ₂ k
  else if j.val = (k.val + 1) % (d + 1) then 1 / 2 + μ₂ k
  else if j.val ≤ d then 1 / 2
  else 0

/-- The Bernoulli instance `I_µ` of p.20: independent `Ber(q_{j,k;µ})` demands. -/
noncomputable def hardLaw (d : ℕ) (μ₁ μ₂ : Fin K → ℝ) : DemandLaw n K where
  law k j := bernoulliLaw (qMu d μ₁ μ₂ k j)
  prob _ _ := bernoulliLaw_isProb _
  supp _ _ := bernoulliLaw_supp _

/-- The first coordinate of the `µ` of Lemma EC.3, p.ec42: `η/(d+1)` if `k%(d+1) = 1`, `-η/(d+1)` if
`k%(d+1) = 0`, and `0` otherwise (page `k` is `k.val + 1`). The second coordinate is `η` for
all `k`. -/
noncomputable def ec3Mu (d : ℕ) (η : ℝ) (k : Fin K) : ℝ :=
  if (k.val + 1) % (d + 1) = 1 then η / ((d : ℝ) + 1)
  else if (k.val + 1) % (d + 1) = 0 then -η / ((d : ℝ) + 1)
  else 0

open Classical in
/-- The family `A_l = {k : k%(d+1) = l%(d+1)}` of (EC.40), p.ec41, for `l.val + 1 ∈ [d+1]` (the
page's `A_{d+1} = {k : k%(d+1) = 0}`). -/
noncomputable def family (d : ℕ) (l : Fin (d + 1)) : Finset (Fin K) :=
  Finset.univ.filter fun k => (k.val + 1) % (d + 1) = (l.val + 1) % (d + 1)

open Classical in
/-- The number of periods in the selling horizon that post `k`, i.e. `∑_t 1(z_t = k)` while "the
algorithm has not stopped" (proof of Lemma EC.7, p.ec52). -/
noncomputable def soldCount (P : Problem d n K) {m : ℕ} (h : History n K m) (k : Fin K) : ℕ :=
  (Finset.univ.filter fun t : Fin m => Sells P h t ∧ (h t).1 = some k).card

open Classical in
/-- The action `z_t` frozen at the end of the selling horizon: "policy `ϕ` keeps choosing the action
chosen in round `τ_stop` for all `t ∈ [τ_stop + 1 : T]`" (p.ec50).

**Formalization Note.** `none` if not even the first period sells, the case `τ_stop = 0` that the
page does not discuss. -/
noncomputable def frozen (P : Problem d n K) {m : ℕ} (h : History n K m) (t : Fin m) : Action K :=
  let S := Finset.univ.filter fun u : Fin m => u ≤ t ∧ Sells P h u
  if hS : S.Nonempty then (h (S.max' hS)).1 else none

open Classical in
/-- `∑_t 1(z_t = k)` with the frozen actions. -/
noncomputable def frozenCount (P : Problem d n K) {m : ℕ} (h : History n K m) (k : Fin K) : ℕ :=
  (Finset.univ.filter fun t : Fin m => frozen P h t = some k).card

/-- All arms occur among the frozen actions of the rounds in `[a, b]`. -/
def CoveredOn (P : Problem d n K) {m : ℕ} (h : History n K m) (a b : ℕ) : Prop :=
  ∀ k : Fin K, ∃ u : Fin m, a ≤ u.val ∧ u.val ≤ b ∧ frozen P h u = some k

/-- The cover times of p.ec49: `τ_0` is the first round, and `τ_{j+1}` is the least round `b` such
that all arms were chosen in `[τ_j : b]`, and `∞` if there is none.

**Formalization Note.** Rounds are `0`-based, so page time `τ_j` is `coverTime … j + 1`. `sInf ∅ = ⊤`
in `ℕ∞` gives the `∞` case, including when `τ_j = ∞`. -/
noncomputable def coverTime (P : Problem d n K) {m : ℕ} (h : History n K m) : ℕ → ℕ∞
  | 0 => 0
  | j + 1 =>
    sInf ((fun b : ℕ => (b : ℕ∞)) ''
      {b | coverTime P h j ≤ b ∧ b < m ∧ CoveredOn P h (coverTime P h j).toNat b})

open Classical in
/-- `S(a, T)`: the number of switches of the frozen actions among rounds at least `a`. A switch
between rounds `a - 1` and `a` does not count (p.ec50). -/
noncomputable def switchesFrom (P : Problem d n K) {m : ℕ} (h : History n K m) (a : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin m =>
    a ≤ t.val ∧ ∃ ht : t.val + 1 < m, frozen P h t ≠ frozen P h ⟨t.val + 1, ht⟩).card

end BlindNRMLS


