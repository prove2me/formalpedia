-- Prove2me | Definitions.Def_RandOrderKnapGAP_Integral_OneResource
-- name    : RandOrderKnapGAP_Integral_OneResource
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:55.212982+00:00
-- url     : https://prove2.me/theorems/cbe481fb-d1da-478f-ab9c-835803159912
-- title:
--   One-resource constructions: conditions (B.7)–(B.11), the comparison condition (B.16) and the coefficient $\Gamma_N(C,i)$
-- statement:
--   Fix a horizon $N$: rounds $k=1,\dots,N$, $N$ items with sizes $s_j\in[0,1]$, one resource of capacity $1$. A **one-resource construction** consists of target distributions $\mu_k$ on $[0,1]$ ($k=0,\dots,N$) with strict tails $P_k(z)=\Pr_{Z\sim\mu_k}(Z>z)$; acceptance rules $\ell$ with acceptance probabilities $h_{k,\ell}(z,s)$; finite sets $\mathcal L_k(s)$ of rules eligible for size $s$ in round $k$; crossing envelopes $H_{k,\ell}(z,s)$; threshold budgets $D_k(z)$; and a set of active rounds. With
--   $$q_{k,\ell}(s)=\mathbb E_{Z\sim\mu_{k-1}}[h_{k,\ell}(Z,s)],\qquad B_{k,\ell}(z,s)=\mathbb E_{Z\sim\mu_{k-1}}\big[h_{k,\ell}(Z,s)\mathbf 1\{z-s<Z\le z\}\big]$$
--   ((B.8), (B.9)), the construction is **valid** when every $\mu_k$ is a probability distribution on $[0,1]$; (B.7) $0\le h_{k,\ell}(z,s)\le1$ and $h_{k,\ell}(z,s)=0$ whenever $z+s>1$; (B.10) $0\le B_{k,\ell}(z,s)\le H_{k,\ell}(z,s)$ for $0\le z<1$; and (B.11) $D_k(z)/k\le P_k(z)-P_{k-1}(z)$ for $0\le z<1$.
--
--   A **feasible configuration** is a set $C$ of items with $\sum_{i\in C}s_i\le1$. A **comparison assignment** gives each $i$ in an observed part $S=C\cap Q$ ($|Q|=k$) a rule $\ell_{k,C,S}(i)$; it satisfies (B.16) when the rules are eligible and $\sum_{i\in S}H_{k,\ell_{k,C,S}(i)}(z,s_i)\le D_k(z)$ for $0\le z<1$. The comparison coefficient (B.17) is
--   $$\Gamma_N(C,i)=\frac1N\sum_{k=1}^N\mathbb E\big[q_{k,\ell_{k,C,C\cap Q_k}(i)}(s_i)\ \big|\ i\in Q_k\big],$$
--   over a uniformly random order of the $N$ items, inactive rounds contributing $0$.
--
--   **Formalization Note.** Rules are natural numbers. (B.7) and (B.10) are required for eligible rules, sizes in $[0,1]$ and loads in $[0,1]$ (thresholds in $[0,1)$), with $z\mapsto h_{k,\ell}(z,s)$ measurable so that $q$ and $B$ are genuine expectations. The assignment may depend on the sizes of the instance, on $C$, $k$, $S$ and $i$, as the paper's analysis-only comparison does.
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), pp. 33–34, 36 (PDF 35–36, 38), §B.2–§B.3, (B.7)–(B.11), (B.16), (B.17)

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_RandomOrder

open scoped BigOperators
open MeasureTheory

namespace RandOrderKnapGAP.Integral

/-!
# One-resource constructions: (B.7)–(B.11), the comparison condition (B.16) and `Γ_N`

Agrawal, Khan, Pareek, *Improved Algorithms in the Random-Order Model: Knapsack, GAP, and
Beyond*, STOC 2027 submission, §B.2 (pp. 33–34) and §B.3 (p. 36).

One resource of capacity `1`; horizon `N` (rounds `k = 1, …, N`, `N` items `Fin N`, sizes in
`[0, 1]`). A construction fixes

* target distributions `μ_k` on `[0, 1]` (`k = 0, …, N`) with strict tails
  `P_k(z) = Pr_{Z∼μ_k}(Z > z)`;
* acceptance rules `ℓ ∈ ℕ` with acceptance probabilities `h_{k,ℓ}(z, s)`;
* the eligible rule sets `L_k(s)` (a finite set of rules for an item of size `s` in round `k`);
* crossing envelopes `H_{k,ℓ}(z, s)` and threshold budgets `D_k(z)`;
* which rounds are active (inactive rounds reject and contribute `0` to `Γ_N`).

`q_{k,ℓ}(s) = E_{Z∼μ_{k−1}}[h_{k,ℓ}(Z, s)]` (B.8) and
`B_{k,ℓ}(z, s) = E_{Z∼μ_{k−1}}[h_{k,ℓ}(Z, s) 1{z − s < Z ≤ z}]` (B.9).
-/

/-- The data of a one-resource construction. -/
structure OneResourceConstruction where
  /-- Target distributions `μ_k`. -/
  μ : ℕ → Measure ℝ
  /-- Acceptance probabilities `h_{k,ℓ}(z, s)` (arguments: round, rule, load, size). -/
  h : ℕ → ℕ → ℝ → ℝ → ℝ
  /-- Eligible rules `L_k(s)` for an item of size `s` in round `k`. -/
  L : ℕ → ℝ → Finset ℕ
  /-- Crossing envelopes `H_{k,ℓ}(z, s)`. -/
  H : ℕ → ℕ → ℝ → ℝ → ℝ
  /-- Threshold budgets `D_k(z)`. -/
  D : ℕ → ℝ → ℝ
  /-- Whether round `k` is active. -/
  active : ℕ → Bool

namespace OneResourceConstruction

variable (c : OneResourceConstruction)

/-- The strict tail `P_k(z) = Pr_{Z∼μ_k}(Z > z)`. -/
noncomputable def P (k : ℕ) (z : ℝ) : ℝ := (c.μ k (Set.Ioi z)).toReal

/-- (B.8): `q_{k,ℓ}(s) = E_{Z∼μ_{k−1}}[h_{k,ℓ}(Z, s)]` (rounds `k ≥ 1`). -/
noncomputable def q (k ℓ : ℕ) (s : ℝ) : ℝ := ∫ Z, c.h k ℓ Z s ∂(c.μ (k - 1))

/-- (B.9): `B_{k,ℓ}(z, s) = E_{Z∼μ_{k−1}}[h_{k,ℓ}(Z, s) 1{z − s < Z ≤ z}]` (rounds `k ≥ 1`). -/
noncomputable def Bcross (k ℓ : ℕ) (z s : ℝ) : ℝ :=
  ∫ Z, c.h k ℓ Z s * (Set.Ioc (z - s) z).indicator (fun _ => (1 : ℝ)) Z ∂(c.μ (k - 1))

/-- The conditions (B.7)–(B.11) for horizon `N`:
* every `μ_k` (`0 ≤ k ≤ N`) is a probability distribution on `[0, 1]`;
* (B.7) for every round `1 ≤ k ≤ N`, size `s ∈ [0, 1]` and eligible rule `ℓ ∈ L_k(s)`:
  `z ↦ h_{k,ℓ}(z, s)` is measurable, `0 ≤ h_{k,ℓ}(z, s) ≤ 1` for `z ∈ [0, 1]`, and
  `h_{k,ℓ}(z, s) = 0` whenever `z + s > 1`;
* (B.10) `0 ≤ H_{k,ℓ}(z, s)` and `B_{k,ℓ}(z, s) ≤ H_{k,ℓ}(z, s)` for every such `k, s, ℓ` and every
  threshold `z ∈ [0, 1)`;
* (B.11) `D_k(z)/k ≤ P_k(z) − P_{k−1}(z)` for `1 ≤ k ≤ N` and `0 ≤ z < 1`. -/
def Valid (N : ℕ) : Prop :=
  (∀ k ≤ N, IsProbabilityMeasure (c.μ k) ∧ c.μ k (Set.Icc 0 1) = 1) ∧
  (∀ k, 1 ≤ k → k ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ℓ ∈ c.L k s,
      Measurable (fun z => c.h k ℓ z s) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c.h k ℓ z s ∧ c.h k ℓ z s ≤ 1) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1, 1 < z + s → c.h k ℓ z s = 0)) ∧
  (∀ k, 1 ≤ k → k ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ℓ ∈ c.L k s, ∀ z ∈ Set.Ico (0 : ℝ) 1,
      0 ≤ c.H k ℓ z s ∧ c.Bcross k ℓ z s ≤ c.H k ℓ z s) ∧
  (∀ k, 1 ≤ k → k ≤ N → ∀ z ∈ Set.Ico (0 : ℝ) 1,
      c.D k z / (k : ℝ) ≤ c.P k z - c.P (k - 1) z)

/-- A comparison assignment `ℓ_{k,C,S}(i)`: for sizes `s` of the `N` items, a configuration `C`,
a round `k`, an observed part `S` and an item `i ∈ S`, the rule assigned to `i`. -/
abbrev Assignment (N : ℕ) : Type :=
  (Fin N → ℝ) → Finset (Fin N) → ℕ → Finset (Fin N) → Fin N → ℕ

/-- A feasible one-resource configuration: sizes in `[0, 1]` and `∑_{i ∈ C} s_i ≤ 1`. -/
def IsConfiguration {N : ℕ} (s : Fin N → ℝ) (C : Finset (Fin N)) : Prop :=
  (∀ j, s j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j ∈ C, s j ≤ 1

/-- (B.16): for every feasible configuration `C`, every round `1 ≤ k ≤ N` and every possible
observed part `S = C ∩ Q` (`Q` any set of `k` items), each `i ∈ S` gets an eligible rule
`ℓ_{k,C,S}(i) ∈ L_k(s_i)`, and `∑_{i∈S} H_{k,ℓ_{k,C,S}(i)}(z, s_i) ≤ D_k(z)` for `0 ≤ z < 1`. -/
def SatisfiesB16 (N : ℕ) (ℓ : Assignment N) : Prop :=
  ∀ (s : Fin N → ℝ) (C : Finset (Fin N)), IsConfiguration s C →
    ∀ k, 1 ≤ k → k ≤ N → ∀ Q : Finset (Fin N), Q.card = k →
      (∀ i ∈ C ∩ Q, ℓ s C k (C ∩ Q) i ∈ c.L k (s i)) ∧
      (∀ z ∈ Set.Ico (0 : ℝ) 1,
        ∑ i ∈ C ∩ Q, c.H k (ℓ s C k (C ∩ Q) i) z (s i) ≤ c.D k z)

/-- (B.17): `Γ_N(C, i) = (1/N) ∑_{k=1}^N E[q_{k,ℓ_{k,C,C∩Q_k}(i)}(s_i) | i ∈ Q_k]`, the
expectation over a uniformly random arrival order of the `N` items, with inactive rounds
contributing `0`. -/
noncomputable def Gamma (N : ℕ) (ℓ : Assignment N) (s : Fin N → ℝ) (C : Finset (Fin N))
    (i : Fin N) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N,
    (if c.active k then
      condExpPerm (fun π => c.q k (ℓ s C k (C ∩ prefixSet π k) i) (s i))
        (fun π => i ∈ prefixSet π k)
    else 0)

end OneResourceConstruction

end RandOrderKnapGAP.Integral


