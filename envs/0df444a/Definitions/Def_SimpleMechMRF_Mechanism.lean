-- Prove2me | Definitions.Def_SimpleMechMRF_Mechanism
-- name    : SimpleMechMRF_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:31.629087+00:00
-- url     : https://prove2.me/theorems/02a68041-85a7-4a47-a38f-abc59236bb45
-- title:
--   Mechanisms for a constrained-additive buyer: lotteries, IC, IR, $\mathrm{Rev}(D)$, $\mathrm{SRev}$, $\mathrm{BRev}$
-- statement:
--   Let $\mathcal I\subseteq 2^{[n]}$ be a set system of feasible bundles; it is **downward closed** if every subset of a feasible bundle is feasible. The **constrained additive** valuation is $v(t,S)=\max_{R\subseteq S,\,R\in\mathcal I}\sum_{i\in R}t_i$; it is **additive** when $\mathcal I=2^{[n]}$.
--
--   A **mechanism** $M$ assigns to each report $t'$ a lottery $\sigma(t',\cdot)$ over feasible bundles (nonnegative weights with total at most $1$; the rest allocates nothing) and a real payment $p(t')$. The probability of receiving item $i$ is $\pi_i(t')=\sum_{S\in\mathcal I,\,i\in S}\sigma(t',S)$, and a buyer of type $t$ reporting $t'$ has quasi-linear utility $u(t,t')=\sum_{S\in\mathcal I}\sigma(t',S)\,v(t,S)-p(t')$. $M$ is **incentive compatible** (IC) if $u(t,t')\le u(t,t)$ for all $t,t'\in T$, and **individually rational** (IR) if $u(t,t)\ge0$ for all $t\in T$. Its revenue is $\mathrm{Rev}(M,v,D)=\mathbb E_{t\sim D}[p(t)]$, and
--
--   $$
--   \mathrm{Rev}(D)=\sup\{\mathrm{Rev}(M,v,D): M\text{ IC and IR}\}.
--   $$
--
--   The simple mechanisms are posted prices. For item $i$, $r_i=\sup_{p}\,p\cdot\Pr[t_i\ge p]$ is the optimal revenue from selling item $i$ alone; $\mathrm{SRev}=r=\sum_i r_i$; and $\mathrm{BRev}=\sup_p\,p\cdot\Pr[\sum_i t_i\ge p]$ is the optimal revenue from one price on the grand bundle.
--
--   **Formalization Note** The suprema are true suprema: $\mathrm{Rev}(D)$ ranges over a nonempty set (the null mechanism) bounded by $\mathbb E[\sum_i t_i]$, and each posted-price revenue is at most $\mathbb E[t_i]$, resp. $\mathbb E[\sum_i t_i]$ (proved in the mission's sanity file). Randomized mechanisms are allowed. The buyer buys at value at least the price.
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Definition 1 and 'Mechanism', p.6 (PDF 7); SRev and BRev, p.7 (PDF 8); r = Σ r_i, §4.3, p.12 (PDF 13)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist

open scoped NNReal

namespace SimpleMechMRF

variable {n : ℕ}

/-- A set system `I` over the items is **downward closed**: every subset of a feasible bundle is
feasible (Definition 1, p. 6, PDF 7). -/
def DownwardClosed (I : Finset (Finset (Fin n))) : Prop :=
  ∀ S ∈ I, ∀ R : Finset (Fin n), R ⊆ S → R ∈ I

/-- The set system of the **additive** valuation, `I = 2^[n]` (Definition 1). -/
def additiveSystem (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ

/-- **Constrained additive valuation** `v(t, S) = max_{R⊆S, R∈I} Σ_{i∈R} tᵢ`
(Definition 1, p. 6, PDF 7). The maximum is taken in `ℝ≥0` (values are nonnegative); it is `0`
when no feasible `R ⊆ S` exists. -/
noncomputable def val (I : Finset (Finset (Fin n))) (t : Fin n → ℝ≥0) (S : Finset (Fin n)) :
    ℝ :=
  ((I.filter (fun R => R ⊆ S)).sup fun R => ∑ i ∈ R, t i : ℝ≥0)

/-- **A (randomized) mechanism** `M = (π, p)` for one buyer. On report `t`, `σ t S` is the
probability that the buyer receives exactly the bundle `S`, and `p t` is the payment (any real).

Cai & Oikonomou, arXiv:2106.10814v2, "Mechanism", p. 6 (PDF 7). -/
structure Mechanism (n : ℕ) where
  /-- The lottery over bundles offered at each report. -/
  σ : (Fin n → ℝ≥0) → Finset (Fin n) → ℝ
  /-- The payment `p(t)`. -/
  p : (Fin n → ℝ≥0) → ℝ

namespace Mechanism

/-- At every report the mechanism is a sub-probability lottery over the **feasible** bundles
`S ∈ I` (the remaining probability allocates nothing). Only the values `σ t S` for `S ∈ I` are
used. -/
def IsLottery (I : Finset (Finset (Fin n))) (M : Mechanism n) : Prop :=
  ∀ t, (∀ S, 0 ≤ M.σ t S) ∧ ∑ S ∈ I, M.σ t S ≤ 1

/-- `πᵢ(t)`, the probability that the buyer receives item `i` when she reports `t`. -/
noncomputable def alloc (I : Finset (Finset (Fin n))) (M : Mechanism n) (i : Fin n)
    (t : Fin n → ℝ≥0) : ℝ :=
  ∑ S ∈ I.filter (fun S => i ∈ S), M.σ t S

/-- The quasi-linear expected utility of a buyer of true type `t` who reports `t'`:
`E_{S∼σ(t')}[v(t, S)] − p(t')`. -/
noncomputable def utility (I : Finset (Finset (Fin n))) (M : Mechanism n)
    (t t' : Fin n → ℝ≥0) : ℝ :=
  ∑ S ∈ I, M.σ t' S * val I t S - M.p t'

/-- **Incentive compatibility** on the support: no type in `T` gains by reporting another type
in `T` (p. 6). -/
def IsIC (D : TypeDist n) (I : Finset (Finset (Fin n))) (M : Mechanism n) : Prop :=
  ∀ t ∈ D.supp, ∀ t' ∈ D.supp, M.utility I t t' ≤ M.utility I t t

/-- **Individual rationality** on the support: truthful utility is nonnegative (p. 6). -/
def IsIR (D : TypeDist n) (I : Finset (Finset (Fin n))) (M : Mechanism n) : Prop :=
  ∀ t ∈ D.supp, 0 ≤ M.utility I t t

/-- `Rev(M, v, D) = E_{t∼D}[p(t)]`, the expected revenue (p. 6). -/
noncomputable def rev (D : TypeDist n) (M : Mechanism n) : ℝ :=
  D.expect M.p

end Mechanism

/-- **`Rev(D)`**: the optimal expected revenue over all randomized IC and IR mechanisms for the
valuation with feasible bundles `I` (p. 6, PDF 7).

**Formalization Note.** The set is nonempty (the mechanism that allocates nothing and charges
nothing) and bounded above by `E[Σᵢ tᵢ]` (IR and `v(t, S) ≤ Σᵢ tᵢ`), so `sSup` is the true
supremum. -/
noncomputable def optRev (D : TypeDist n) (I : Finset (Finset (Fin n))) : ℝ :=
  sSup {x | ∃ M : Mechanism n, M.IsLottery I ∧ M.IsIC D I ∧ M.IsIR D I ∧ x = M.rev D}

/-- `rᵢ`, the optimal revenue from selling item `i` alone at a posted price:
`sup_{p ∈ ℝ} p · Pr_{t∼D}[tᵢ ≥ p]` (the buyer buys at value ≥ price; this is Myerson's revenue
for `Dᵢ`, p. 12, PDF 13).

**Formalization Note.** The function is bounded above by `E[tᵢ]`, so the `iSup` is the true
supremum; it is `≥ 0` (price `0`). -/
noncomputable def itemRev (D : TypeDist n) (i : Fin n) : ℝ :=
  ⨆ p : ℝ, p * D.prob {t | p ≤ (t i : ℝ)}

/-- **`SRev`** for an additive buyer: `r = Σᵢ rᵢ` (p. 7 and p. 12: "We use r = Σ_{i∈[n]} ri to
denote SRev"). -/
noncomputable def srev (D : TypeDist n) : ℝ :=
  ∑ i, itemRev D i

/-- **`BRev`**: the optimal revenue from selling the grand bundle at one posted price,
`sup_{p ∈ ℝ} p · Pr_{t∼D}[Σᵢ tᵢ ≥ p]` (p. 7, PDF 8).

**Formalization Note.** Bounded above by `E[Σᵢ tᵢ]`, so the `iSup` is the true supremum. -/
noncomputable def brev (D : TypeDist n) : ℝ :=
  ⨆ p : ℝ, p * D.prob {t | p ≤ ∑ i, (t i : ℝ)}

end SimpleMechMRF


