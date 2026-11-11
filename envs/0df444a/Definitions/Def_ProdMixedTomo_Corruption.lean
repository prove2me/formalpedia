-- Prove2me | Definitions.Def_ProdMixedTomo_Corruption
-- name    : ProdMixedTomo_Corruption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:13:47.225611+00:00
-- url     : https://prove2.me/theorems/251770f5-b030-4590-b57e-705bc2ddb35b
-- title:
--   $\epsilon$-corruption adversary and total variation between measures
-- statement:
--   **$\epsilon$-corruption** (Definition 2.1). A multiset $S$ of $N$ points is an $\epsilon$-corrupted set of samples from $p$ if $S=S_g\cup S_b\setminus S_r$ with $S_g$ a set of $N$ i.i.d. samples from $p$, $S_r\subseteq S_g$ and $|S_r|=|S_b|\le\epsilon N$. We model the corruption as an **adversary**: a map $\mathrm{Adv}$ from the clean list $S_g$ to the corrupted list such that, for every $S_g$, after some reordering $\mathrm{Adv}(S_g)$ differs from $S_g$ in at most $\epsilon N$ positions. The adversary sees all of $S_g$ but not the algorithm's randomness.
--
--   **Total variation for measures.** For probability measures $p,q$ on a measurable space,
--   $$
--   d_{\mathrm{tv}}(p,q)=\sup_{A\ \text{measurable}}|p(A)-q(A)|,
--   $$
--   which defines $\epsilon$-contamination (Definition 2.2): $N$ i.i.d. samples from some $q$ with $d_{\mathrm{tv}}(p,q)\le\epsilon$.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Definition 2.1, pp.13–14 (PDF pp.15–16); Definition 2.2, p.14 (PDF p.16)

import Mathlib

namespace ProdMixedTomo

/-!
# The `ϵ`-corruption adversary and total variation between measures

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Definition 2.1, pp.13–14
(PDF pp.15–16): "a multi-set S of n points is an ϵ-corrupted set of samples from a distribution p
if we can write S = S_g ∪ S_b \ S_r, where S_g is a set of n i.i.d. samples from p, S_r ⊆ S_g, and
|S_r| = |S_b| ≤ ϵn"; Definition 2.2, p.14 (`ϵ`-contamination: i.i.d. samples from some `q` with
`d_tv(p, q) ≤ ϵ`).

**Formalization Note.** The corruption is an *adversary*: a function `Adv` from the clean sample
`S_g` (a list of `N` points) to the corrupted list `S`, such that for every `S_g` the multiset of
`Adv S_g` differs from that of `S_g` by at most `ϵN` replacements, i.e. after some reordering
at most `ϵN` positions differ. The adversary sees all of `S_g` but not the algorithm's coins; a
randomized adversary is a mixture of these. For measures on a measurable space, total variation is
`sup_A |p(A) − q(A)|` over measurable `A`.
-/

open MeasureTheory

open Classical in
/-- `Adv` is an `ϵ`-corruption adversary on lists of `N` points (Definition 2.1). -/
def IsCorruption {X : Type*} {N : ℕ} (ϵ : ℝ) (Adv : (Fin N → X) → (Fin N → X)) : Prop :=
  ∀ S : Fin N → X, ∃ σ : Equiv.Perm (Fin N),
    ((Finset.univ.filter fun i => Adv S i ≠ S (σ i)).card : ℝ) ≤ ϵ * N

/-- Total variation distance `sup_A |p(A) − q(A)|` between two finite measures. -/
noncomputable def tvMeasure {X : Type*} [MeasurableSpace X] (p q : Measure X) : ℝ :=
  ⨆ A : {A : Set X // MeasurableSet A}, |(p A.1).toReal - (q A.1).toReal|

end ProdMixedTomo


