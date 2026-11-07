-- Prove2me | Definitions.Def_NCPComm_family
-- name    : NCPComm_family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:34.948629+00:00
-- url     : https://prove2.me/theorems/9960b29f-e5fb-46ef-98e2-ae94233c4f15
-- title:
--   The families $\mathcal F_0(N,K)$ and $\mathcal F_1(N,K)$ of the Noisy Collisions Problem
-- statement:
--   Fix integers $N,K$ with $3\mid N$ and $0<K<N/3$. The **canonical distributions** on $[N]$ are as follows. $D_0$ gives mass $\frac1{2K}$ to each of the $K$ heavy elements $\{1,\dots,K\}$ and $\frac1{2(N-K)}$ to each of the other $N-K$ elements. $D_1$ gives mass $\frac1{2K}$ to the same heavy elements, $\frac1{2(N/3-K)}$ to each light element in $\{K+1,\dots,N/3\}$, and $0$ to the remaining $2N/3$ elements.
--
--   For a permutation $\pi$ of $[N]$, the distribution $\pi(D)$ is given by $\pi(D)(x)=D(\pi^{-1}(x))$. The families are the permutation orbits
--   $$
--   \mathcal F_b(N,K)=\{\pi(D_b):\pi\text{ a permutation of }[N]\},\qquad b\in\{0,1\},
--   $$
--   and the **Noisy Collisions Problem** is the promise problem $\mathrm{NCP}(N,K)=(\mathcal F_0(N,K),\mathcal F_1(N,K))$.
--
--   Both families have $\|D\|_2^2=\Theta(1/K)$, and they differ only in the support size of the light part, which is what makes collisions among light elements the only signal.
--
--   **Formalization Note** The labels are 0-based. `canonicalMass` is a function with values in $[0,\infty]$, and membership in a family is equality of mass functions. `ValidParams N K` records $3\mid N$ and $0<K<N/3$; p.19 assumes $N\in6\mathbb N$ "only for convenience", and $N\in3\mathbb N$ is what Proposition 4.7 uses. `canonicalPMF` packages $D_b$ as a distribution in that range.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Definitions 4.1 and 4.2, p.19

import Mathlib

open scoped ENNReal

namespace NCPComm

/-- The mass function of the canonical distributions of §4, p.19 (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256
714c0353…). `canonicalMass false N K` is `D₀ = D₀({1,…,K})`: mass `1/(2K)` on the heavy set and
`1/(2(N-K))` on the other `N-K` elements. `canonicalMass true N K` is
`D₁ = D₁({1,…,K}, {K+1,…,N/3})`: mass `1/(2K)` on the heavy set, `1/(2(N/3-K))` on the light set
and `0` on the other `2N/3` elements.

**Formalization Note** The labels are 0-based: the heavy set is `{x | x < K}` and the light set of
`D₁` is `{x | K ≤ x < N/3}`. The natural-number subtraction and division are exact under the
standing assumptions of p.19, recorded in `ValidParams`. -/
noncomputable def canonicalMass (b : Bool) (N K : ℕ) (x : Fin N) : ℝ≥0∞ :=
  if x.val < K then ((2 * K : ℕ) : ℝ≥0∞)⁻¹
  else if b then (if x.val < N / 3 then ((2 * (N / 3 - K) : ℕ) : ℝ≥0∞)⁻¹ else 0)
  else ((2 * (N - K) : ℕ) : ℝ≥0∞)⁻¹

/-- The families `F₀(N, K)` (`b = false`) and `F₁(N, K)` (`b = true`) of Definition 4.2, p.19: all
permutations `π(D_b)` of the canonical distribution, with `π(D)(x) = D(π⁻¹(x))` (Definition 4.1,
p.19). The Noisy Collisions Problem is the promise problem `NCP(N, K) = (F₀(N, K), F₁(N, K))`.

**Formalization Note** Membership is equality of mass functions, so no distribution is constructed
here. -/
def family (b : Bool) (N K : ℕ) : Set (PMF (Fin N)) :=
  {D | ∃ π : Equiv.Perm (Fin N), ∀ x, D x = canonicalMass b N K (π.symm x)}

/-- The parameter range in which `canonicalMass` is a distribution for both `b`: `3 ∣ N` and
`0 < K < N/3` (p.19 assumes `N ∈ 6ℕ` "only for convenience"; `N ∈ 3ℕ` is what Proposition 4.7 uses
for the source parameter). -/
def ValidParams (N K : ℕ) : Prop := 3 ∣ N ∧ 0 < K ∧ 3 * K < N

instance (N K : ℕ) : Decidable (ValidParams N K) := by
  unfold ValidParams; infer_instance

theorem sum_range_three_blocks (f : ℕ → ℝ≥0∞) (K l r : ℕ) (a c d : ℝ≥0∞)
    (h1 : ∀ i < K, f i = a) (h2 : ∀ i < l, f (K + i) = c) (h3 : ∀ i < r, f (K + l + i) = d) :
    ∑ i ∈ Finset.range (K + l + r), f i = K * a + l * c + r * d := by
  rw [Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_congr rfl (fun i hi => h1 i (Finset.mem_range.1 hi)),
    Finset.sum_congr rfl (fun i hi => h2 i (Finset.mem_range.1 hi)),
    Finset.sum_congr rfl (fun i hi => h3 i (Finset.mem_range.1 hi))]
  simp

theorem canonicalMass_sum (b : Bool) (N K : ℕ) (h : ValidParams N K) :
    ∑ x, canonicalMass b N K x = 1 := by
  obtain ⟨⟨m, rfl⟩, hK, hlt⟩ := h
  have hKm : K < m := by omega
  have hdiv : 3 * m / 3 = m := by omega
  have half : ∀ c : ℕ, 0 < c → (c : ℝ≥0∞) * ((2 * c : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹ := by
    intro c hc
    have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
    have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
    push_cast
    rw [ENNReal.mul_inv (by simp) (by simp), mul_comm (2⁻¹ : ℝ≥0∞), ← mul_assoc,
      ENNReal.mul_inv_cancel hc0 hct, one_mul]
  have hsum : ∑ x : Fin (3 * m), canonicalMass b (3 * m) K x
      = ∑ i ∈ Finset.range (3 * m),
          (if i < K then ((2 * K : ℕ) : ℝ≥0∞)⁻¹
           else if b then (if i < m then ((2 * (m - K) : ℕ) : ℝ≥0∞)⁻¹ else 0)
           else ((2 * (3 * m - K) : ℕ) : ℝ≥0∞)⁻¹) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => (if i < K then ((2 * K : ℕ) : ℝ≥0∞)⁻¹
           else if b then (if i < m then ((2 * (m - K) : ℕ) : ℝ≥0∞)⁻¹ else 0)
           else ((2 * (3 * m - K) : ℕ) : ℝ≥0∞)⁻¹))]
    simp [canonicalMass, hdiv]
  rw [hsum]
  cases b with
  | false =>
    rw [show 3 * m = K + (3 * m - K) + 0 by omega,
      sum_range_three_blocks _ K (3 * m - K) 0 ((2 * K : ℕ) : ℝ≥0∞)⁻¹ (((2 * (K + (3 * m - K) + 0 - K) : ℕ) : ℝ≥0∞)⁻¹) 0
        (fun i hi => by simp [hi]) (fun i _ => by simp)
        (fun i hi => by omega)]
    have e : K + (3 * m - K) + 0 - K = 3 * m - K := by omega
    rw [e, half K hK, half _ (by omega : 0 < 3 * m - K)]
    simp [ENNReal.inv_two_add_inv_two]
  | true =>
    rw [show 3 * m = K + (m - K) + 2 * m by omega,
      sum_range_three_blocks _ K (m - K) (2 * m) ((2 * K : ℕ) : ℝ≥0∞)⁻¹ (((2 * (m - K) : ℕ) : ℝ≥0∞)⁻¹) 0
        (fun i hi => by simp [hi])
        (fun i hi => by
          have h1 : ¬ K + i < K := by omega
          have h2 : K + i < m := by omega
          simp [h1, h2])
        (fun i _ => by
          have h1 : ¬ K + (m - K) + i < K := by omega
          have h2 : ¬ K + (m - K) + i < m := by omega
          simp [h1, h2])]
    rw [half K hK, half _ (by omega : 0 < m - K)]
    simp [ENNReal.inv_two_add_inv_two]

/-- The canonical distribution `D_b` of p.19 as a `PMF`, in the valid parameter range. -/
noncomputable def canonicalPMF (b : Bool) (N K : ℕ) (h : ValidParams N K) : PMF (Fin N) :=
  PMF.ofFintype (canonicalMass b N K) (canonicalMass_sum b N K h)

end NCPComm


