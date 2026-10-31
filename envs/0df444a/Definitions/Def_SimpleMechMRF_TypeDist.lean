-- Prove2me | Definitions.Def_SimpleMechMRF_TypeDist
-- name    : SimpleMechMRF_TypeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:38.805682+00:00
-- url     : https://prove2.me/theorems/734de509-7918-4e85-aeed-5ea315a91e10
-- title:
--   Finite distributions of buyer types: probabilities, marginals $f_i$, conditionals $f_i(t_i\mid t_{-i})$
-- statement:
--   A seller offers $n$ items to one buyer. The buyer's **type** is a vector $t=(t_1,\dots,t_n)$ of nonnegative reals, $t_i$ being her value for item $i$. A **type distribution** $D$ is a probability distribution of $t$ with finite support $T=\mathrm{Supp}(D)$ and mass function $f(c)=\Pr_{t\sim D}[t=c]$, positive on $T$ and summing to $1$.
--
--   The module defines, for such $D$:
--
--   1. $\Pr_{t\sim D}[t\in S]$ and $\mathbb E_{t\sim D}[g(t)]$, as finite sums over $T$;
--   2. $T_i=\mathrm{Supp}(D_i)$, the set of values of $t_i$ on $T$, and the marginal mass $f_i(c_i)=\Pr[t_i=c_i]$;
--   3. $f_{-i}(c_{-i})=\Pr[t_{-i}=c_{-i}]$ and the conditional probability $\Pr[t\in S\mid t_{-i}=c_{-i}]$;
--   4. the conditional mass $f_i(c_i\mid c_{-i})=\Pr[t=(c_i,c_{-i})]/\Pr[t_{-i}=c_{-i}]$;
--   5. the conditional probability $\Pr[t\in S\mid t_i=c_i]$ given the value of one item.
--
--   These are the paper's "Basic Notation" and are used by every statement of the mission.
--
--   **Formalization Note** Types are functions $\mathrm{Fin}\,n\to\mathbb R_{\ge 0}$. Conditional probabilities are quotients and are used only where the conditioning event has positive probability (for points of $T$).
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, §2 Basic Notation, p.6 (PDF 7)

import Mathlib

open scoped NNReal

namespace SimpleMechMRF

/-- **A buyer-type distribution with finite support.** A type of the buyer is a vector
`t : Fin n → ℝ≥0`, `t i` being the buyer's value for item `i` (items are `Fin n`). The
distribution `D` of `t` is given by its finite support `supp` (the set `T = Supp(D)` of the
paper) and its probability mass function `pmf`, which is positive on `supp` and sums to `1`
over it.

Cai & Oikonomou, *On Simple Mechanisms for Dependent Items*, arXiv:2106.10814v2, §2 "Basic
Notation", p. 6 (PDF 7): "We use D to denote the distribution of t … T = Supp(D) … we use f(c)
to denote Pr_{t∼D}[t = c]".

**Formalization Note.** Values are nonnegative reals and the support is finite (a reading of
the paper: Def 1 "interpret tᵢ as the value of item i", and every sum of the paper ranges over a
finite type space). The value of `pmf` outside `supp` plays no role: every probability and
expectation below is a sum over `supp`. -/
structure TypeDist (n : ℕ) where
  /-- The support `T = Supp(D)`. -/
  supp : Finset (Fin n → ℝ≥0)
  /-- The probability mass function `f`. -/
  pmf : (Fin n → ℝ≥0) → ℝ
  pmf_pos : ∀ t ∈ supp, 0 < pmf t
  sum_pmf : ∑ t ∈ supp, pmf t = 1

namespace TypeDist

variable {n : ℕ}

/-- `Pr_{t∼D}[t ∈ S]`. -/
noncomputable def prob (D : TypeDist n) (S : Set (Fin n → ℝ≥0)) : ℝ :=
  ∑ t ∈ D.supp, S.indicator D.pmf t

/-- `E_{t∼D}[g(t)]`. -/
noncomputable def expect (D : TypeDist n) (g : (Fin n → ℝ≥0) → ℝ) : ℝ :=
  ∑ t ∈ D.supp, D.pmf t * g t

/-- `Tᵢ = Supp(Dᵢ)`, the support of the marginal distribution of `tᵢ`. -/
noncomputable def suppMarg (D : TypeDist n) (i : Fin n) : Finset ℝ≥0 :=
  D.supp.image (fun t => t i)

/-- `fᵢ(s) = Pr_{tᵢ∼Dᵢ}[tᵢ = s]`, the marginal mass function of item `i`. -/
noncomputable def marg (D : TypeDist n) (i : Fin n) (s : ℝ≥0) : ℝ :=
  D.prob {t | t i = s}

/-- `u` agrees with `t` on every coordinate other than `i` (`u₋ᵢ = t₋ᵢ`). -/
def SameOthers (i : Fin n) (t u : Fin n → ℝ≥0) : Prop :=
  ∀ j, j ≠ i → u j = t j

/-- `f₋ᵢ(t₋ᵢ) = Pr_{u∼D}[u₋ᵢ = t₋ᵢ]`. -/
noncomputable def othersProb (D : TypeDist n) (i : Fin n) (t : Fin n → ℝ≥0) : ℝ :=
  D.prob {u | SameOthers i t u}

/-- `Pr_{u∼D}[u ∈ S | u₋ᵢ = t₋ᵢ]`, conditional probability given the other coordinates. Used
only when `t₋ᵢ` has positive probability (for `t ∈ T`). -/
noncomputable def condProb (D : TypeDist n) (i : Fin n) (t : Fin n → ℝ≥0)
    (S : Set (Fin n → ℝ≥0)) : ℝ :=
  D.prob {u | SameOthers i t u ∧ u ∈ S} / D.othersProb i t

/-- `fᵢ(tᵢ | t₋ᵢ) = Pr[t = (tᵢ, t₋ᵢ)] / Pr[t₋ᵢ]`, the conditional mass of `tᵢ` given `t₋ᵢ`. -/
noncomputable def cond (D : TypeDist n) (i : Fin n) (t : Fin n → ℝ≥0) : ℝ :=
  D.condProb i t {u | u i = t i}

/-- `Pr_{u∼D}[u ∈ S | uᵢ = s]`, conditional probability given the value of item `i`. Used only
for `s ∈ Tᵢ`, where `fᵢ(s) > 0`. -/
noncomputable def condOnItem (D : TypeDist n) (i : Fin n) (s : ℝ≥0)
    (S : Set (Fin n → ℝ≥0)) : ℝ :=
  D.prob {u | u i = s ∧ u ∈ S} / D.marg i s

end TypeDist

end SimpleMechMRF


