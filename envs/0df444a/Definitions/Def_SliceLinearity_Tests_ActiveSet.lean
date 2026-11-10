-- Prove2me | Definitions.Def_SliceLinearity_Tests_ActiveSet
-- name    : SliceLinearity_Tests_ActiveSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:38:38.750367+00:00
-- url     : https://prove2.me/theorems/a4ea3f0c-c75d-471b-8558-6ba5d7b51807
-- title:
--   Product samplers $\lambda^{\otimes n}$, pairwise-independent bits, the active-set test and the symmetric active-set test $\lambda_{p,k}$
-- statement:
--   A **column law** is a distribution $\lambda$ on $\mathbb F_2^k$. The sampler $\lambda^{\otimes n}$ draws the query tuple $(z_1,\dots,z_k)\in(\mathbb F_2^n)^k$ by choosing its $n$ columns $(z_{1,i},\dots,z_{k,i})$ independently from $\lambda$. The bits of $\lambda$ are **pairwise independent** if any two coordinates of $v\sim\lambda$ are independent.
--
--   **Active-set test** (§5.1). Set $p_*=\min\{p,1-p\}$, $m=\lceil1/p_*\rceil$, $\theta=2mp_*-2$ and $c=\mathbb 1\{p>1/2\}$.
--   1. Sample $x\sim\mu_p$.
--   2. Independently for each $i\in[n]$, choose a uniform pair $A_i\subseteq[m]$ with probability $1-\theta$, or a uniform triple with probability $\theta$.
--   3. Sample $(y_{1,i},\dots,y_{m,i})$ uniformly subject to $y_{j,i}=c$ for $j\notin A_i$ and $\sum_jy_{j,i}=x_i$.
--
--   The queries are $x,y_1,\dots,y_m$, and the columns are i.i.d. More generally, active sets of size $a\in\{2,3,4\}$ are chosen with probability $\pi_a$, uniformly among sets of that size; $I_j=\{i: j\in A_i\}$.
--
--   **Symmetric active-set test** (§6.2.1). This is the same test with $c=0$ and size probabilities $\pi_2,\pi_3,\pi_4$. $\lambda_{p,k}$ ($k=m+1$) is its column law with the values found in the proof of Lemma 6.14:
--   $$\pi_2=\tfrac{3-3mp+m(m-1)p^2}{1-p},\qquad \pi_3=\tfrac{2(mp-1)(1-(m-2)p)}{1-p},\qquad \pi_4=\tfrac{(m-3)p(mp-1)}{1-p}.$$
--   For $m=2$, $p=1/2$ these give $\pi_2=1$, so $A_i=[2]$ and $\lambda_{1/2,3}$ is uniform on the even-weight vectors of $\mathbb F_2^3$: the BLR test.
--
--   **Formalization Note** Query $0$ is $x$ and query $j+1$ is $y_{j+1}$. The column law is $\mathrm{Ber}(p)(x_i)\cdot\sum_A\Pr[A]\cdot\mathbb 1[\text{constraints}]/2^{|A|-1}$, since $2^{|A|-1}$ vectors meet the constraints. `symActiveLaw p m π₂ π₃ π₄` takes arbitrary size probabilities, which Lemma 6.14 uses to state uniqueness.
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §5.1 pp. 29–31 (PDF 31–33): the active-set test; §6.2 p. 42 (PDF 44); §6.2.1 pp. 47–48 (PDF 49–50): the symmetric active-set test, Lemma 6.14 (proof)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis

set_option autoImplicit false

namespace SliceLinearity.Tests

/-! # Column laws, product samplers and the (symmetric) active-set test

Aydin, Larsen, Mittal, Richelson, Roy, *Low Soundness Linearity Testing on Subsets of the Hypercube*,
STOC 2027 submission (manuscript sha256 457be236…), §5.1 pp. 29–31 (PDF 31–33), §6.2 p. 42 (PDF 44),
§6.2.1 pp. 47–48 (PDF 49–50, Lemma 6.14).

A *column law* is a distribution `λ` on `F₂^k`; the product sampler `λ^{⊗n}` draws the `n` columns
`(z₁ᵢ, …, z_kᵢ)` independently from `λ`. The query tuple `(z₁, …, z_k)` is a function
`Fin k → Cube n`; its `i`th column is `fun j => z j i`.

The active-set test with `m` auxiliary queries queries `x, y₁, …, y_m`; as a tuple, query `0` is `x`
and query `j.succ` is `y_{j+1}`. -/

/-- The product sampler `λ^{⊗n}`: the weight of `(z₁, …, z_k)` is `∏ᵢ λ(z₁ᵢ, …, z_kᵢ)`. -/
noncomputable def tensorPow {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) (n : ℕ) (z : Fin k → Cube n) : ℝ :=
  ∏ i : Fin n, lam (fun j => z j i)

/-- `Pr_{v∼λ}[v_j = a]`. -/
noncomputable def bitProb {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) (j : Fin k) (a : ZMod 2) : ℝ :=
  ∑ v, if v j = a then lam v else 0

/-- The bits under `λ` are pairwise independent: any two distinct bits are independent. -/
def PairwiseIndepBits {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) : Prop :=
  ∀ j j' : Fin k, j ≠ j' → ∀ a b : ZMod 2,
    (∑ v, if v j = a ∧ v j' = b then lam v else 0) = bitProb lam j a * bitProb lam j' b

/-- The probability of an active set `A ⊆ [m]` when its size `a ∈ {2, 3, 4}` has probability
`π a` and `A` is uniform among the sets of that size. -/
noncomputable def activeSetProb (m : ℕ) (π : ℕ → ℝ) (A : Finset (Fin m)) : ℝ :=
  if 2 ≤ A.card ∧ A.card ≤ 4 then π A.card / (m.choose A.card : ℝ) else 0

/-- The law of one column `(xᵢ, y₁ᵢ, …, y_mᵢ)` of an active-set test: `xᵢ ∼ Ber(p)`; an active set
`Aᵢ` with law `activeSetProb m π`; then `(y₁ᵢ, …, y_mᵢ)` uniform subject to `y_jᵢ = c` for `j ∉ Aᵢ`
and `∑_j y_jᵢ = xᵢ` (there are `2^{|Aᵢ|−1}` such vectors). -/
noncomputable def activeColumnLaw (p : ℝ) (m : ℕ) (c : ZMod 2) (π : ℕ → ℝ)
    (v : Fin (m + 1) → ZMod 2) : ℝ :=
  bitBer p (v 0) * ∑ A : Finset (Fin m), activeSetProb m π A *
    (if (∀ j : Fin m, j ∉ A → v j.succ = c) ∧ ∑ j : Fin m, v j.succ = v 0
      then 1 / (2 : ℝ) ^ (A.card - 1) else 0)

/-- `p* = min{p, 1 − p}`. -/
noncomputable def pStar (p : ℝ) : ℝ := min p (1 - p)

/-- `m = ⌈1/p*⌉`, the number of auxiliary queries of the active-set test. -/
noncomputable def activeM (p : ℝ) : ℕ := ⌈1 / pStar p⌉₊

/-- `θ = 2 m p* − 2`, the probability of an active triple. -/
noncomputable def activeTheta (p : ℝ) : ℝ := 2 * (activeM p : ℝ) * pStar p - 2

/-- `c = 1{p > 1/2}`, the value of inactive bits. -/
noncomputable def activeC (p : ℝ) : ZMod 2 := if 1 / 2 < p then 1 else 0

/-- Size probabilities `π₂, π₃, π₄` as a function of the size. -/
def sizeProbs (π2 π3 π4 : ℝ) (a : ℕ) : ℝ :=
  if a = 2 then π2 else if a = 3 then π3 else if a = 4 then π4 else 0

/-- The column law of the **active-set test** of §5.1 (`m + 1` queries, `m = ⌈1/p*⌉`): a uniform
pair with probability `1 − θ`, a uniform triple with probability `θ`, inactive bits `c`. -/
noncomputable def activeSetTestLaw (p : ℝ) : (Fin (activeM p + 1) → ZMod 2) → ℝ :=
  activeColumnLaw p (activeM p) (activeC p) (sizeProbs (1 - activeTheta p) (activeTheta p) 0)

/-- The joint law of the active sets `A = (A₁, …, A_n)`, independent across coordinates. -/
noncomputable def activeSetsJoint (m : ℕ) (π : ℕ → ℝ) {n : ℕ} (A : Fin n → Finset (Fin m)) : ℝ :=
  ∏ i, activeSetProb m π (A i)

/-- `I_j = {i : j ∈ Aᵢ}`, the coordinates at which the `j`th auxiliary query is active. -/
def coordSet {m n : ℕ} (A : Fin n → Finset (Fin m)) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => j ∈ A i

/-- The column law of the **symmetric active-set test** of §6.2.1 with size probabilities
`π₂, π₃, π₄` (`c = 0`: inactive bits are zero). -/
noncomputable def symActiveLaw (p : ℝ) (m : ℕ) (π2 π3 π4 : ℝ) : (Fin (m + 1) → ZMod 2) → ℝ :=
  activeColumnLaw p m 0 (sizeProbs π2 π3 π4)

/-- `π₂ = (3 − 3mp + m(m−1)p²)/(1 − p)` (proof of Lemma 6.14, p. 48). -/
noncomputable def piTwo (p : ℝ) (m : ℕ) : ℝ :=
  (3 - 3 * (m : ℝ) * p + (m : ℝ) * ((m : ℝ) - 1) * p ^ 2) / (1 - p)

/-- `π₃ = 2(mp − 1)(1 − (m−2)p)/(1 − p)` (proof of Lemma 6.14, p. 48). -/
noncomputable def piThree (p : ℝ) (m : ℕ) : ℝ :=
  2 * ((m : ℝ) * p - 1) * (1 - ((m : ℝ) - 2) * p) / (1 - p)

/-- `π₄ = (m − 3)p(mp − 1)/(1 − p)` (proof of Lemma 6.14, p. 48). -/
noncomputable def piFour (p : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) - 3) * p * ((m : ℝ) * p - 1) / (1 - p)

/-- `λ_{p,k}` (`k = m + 1`): the column law of the symmetric active-set test with the size
probabilities of Lemma 6.14. For `m = 2`, `p = 1/2` these are `π₂ = 1`, `π₃ = π₄ = 0`, and
`λ_{1/2,3}` is uniform on the even-weight vectors of `F₂³` (the BLR test). -/
noncomputable def lambdaPK (p : ℝ) (m : ℕ) : (Fin (m + 1) → ZMod 2) → ℝ :=
  symActiveLaw p m (piTwo p m) (piThree p m) (piFour p m)

end SliceLinearity.Tests


