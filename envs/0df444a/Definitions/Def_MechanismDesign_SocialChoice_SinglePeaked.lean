-- Prove2me | Definitions.Def_MechanismDesign_SocialChoice_SinglePeaked
-- name    : MechanismDesign_SocialChoice_SinglePeaked
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:47:45.610899+00:00
-- url     : https://prove2.me/theorems/285059c2-e339-46d5-a434-95d04ef519c2
-- title:
--   Restricted domains and single-peaked preferences
-- statement:
--   This bundle fixes the vocabulary of §8.3 of Börgers' *An Introduction to the Theory of Mechanism Design*, where each agent's preference is drawn from a subset $\hat{\mathcal R}\subseteq\mathcal R$ of the linear orders over the finite set $A$ and a direct mechanism only has to perform on $\hat{\mathcal R}^N$.
--
--   For a domain $D\subseteq\mathcal R$ and a direct mechanism $f$:
--
--   1. $f$ is **dominant strategy incentive-compatible on $D^N$** if $f(R_i,R_{-i})\,R_i\,f(R_i',R_{-i})$ for every agent $i$, every $R\in D^N$ and every $R_i'\in D$;
--   2. $f$ is **dictatorial on $D^N$** if some agent $i$ satisfies $f(R)\,R_i\,a$ for every $R\in D^N$ and every $a\in A$;
--   3. **the range of $f$ on $D^N$ is $A$** if every $a\in A$ equals $f(R)$ for some $R\in D^N$.
--
--   **Single-peaked preferences.** Label the alternatives $1,\dots,K$. A linear order $R_i$ is single-peaked if there is a peak $k(i)$ such that (i) $k(i)\,R_i\,a$ for every $a\in A$, and (ii) preferences decline monotonically to the right and to the left of the peak:
--   $$\ell\ge k(i)\ \Rightarrow\ \ell\,R_i\,(\ell+1),\qquad \ell\le k(i)\ \Rightarrow\ \ell\,R_i\,(\ell-1).$$
--   The set $\hat{\mathcal R}$ of single-peaked preferences depends on the labelling, which is held fixed.
--
--   The single-peaked domain is the classical restriction on which strategy-proof, non-dictatorial mechanisms exist (Proposition 8.6).
--
--   **Formalization Note** The labelling is an equivalence `lab : A ≃ Fin K`, so labels run $0,\dots,K-1$ instead of $1,\dots,K$. The book prints the left clause as "if $\ell\le k(i)$, then $(\ell-1)\,R_i\,\ell$", which would make preferences rise away from the peak on the left and contradict clause (i); the evident intended clause $\ell\,R_i\,(\ell-1)$ is used. The mechanism remains a total function on all profiles; every notion above only looks at profiles in $D^N$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.149–150, §8.3 (single-peaked preferences and the restricted domain R̂^N)

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

/-!
# Restricted domains and single-peaked preferences (Börgers, Ch. 8, §8.3, pp.149–150)

In §8.3 the set of preferences an agent may hold is no longer all of `R` but a subset `R̂ ⊆ R`;
a direct mechanism is then only required to behave well on `R̂^N`. We represent the subset by a
predicate `D : LinPref A → Prop` and keep the mechanism a total function on all profiles: every
notion below quantifies only over profiles in `D^N`, so values off the domain are irrelevant.
-/

namespace MechanismDesign.SocialChoice

variable {ι A : Type*}

/-- Dominant strategy incentive compatibility on the restricted domain `D^N` (Definition 8.2
read on `R̂^N`, p.149): for every agent `i`, every profile `R ∈ D^N` and every `R'_i ∈ D`,
`f(R_i, R_{-i}) R_i f(R'_i, R_{-i})`. -/
def IsDSICOn [DecidableEq ι] (D : LinPref A → Prop) (f : DirectMechanism ι A) : Prop :=
  ∀ (i : ι) (R : ι → LinPref A) (Ri' : LinPref A), (∀ j, D (R j)) → D Ri' →
    (R i).rel (f R) (f (Function.update R i Ri'))

/-- Dictatorship on the restricted domain `D^N` (Definition 8.3 read on `R̂^N`): some agent `i`
such that for all profiles `R ∈ D^N`, `f(R) R_i a` for all `a ∈ A`. -/
def IsDictatorialOn (D : LinPref A → Prop) (f : DirectMechanism ι A) : Prop :=
  ∃ i : ι, ∀ R : ι → LinPref A, (∀ j, D (R j)) → ∀ a : A, (R i).rel (f R) a

/-- "The range of `f` is `A`" on the restricted domain `D^N`: every alternative is chosen at some
profile in `D^N`. -/
def HasFullRangeOn (D : LinPref A → Prop) (f : DirectMechanism ι A) : Prop :=
  ∀ a : A, ∃ R : ι → LinPref A, (∀ j, D (R j)) ∧ f R = a

/-- **Single-peaked preferences** (p.149). The alternatives are labelled by `lab : A ≃ Fin K`
(the book labels them `1, 2, …, K`; here the labels are `0, …, K − 1`). A linear order `R_i` is
single-peaked if there is a peak `k(i)` such that (i) `k(i) R_i a` for all `a ∈ A`, and
(ii) preferences decline monotonically to the right and to the left of the peak: if
`ℓ ≥ k(i)` then `ℓ R_i (ℓ + 1)`, and if `ℓ ≤ k(i)` then `ℓ R_i (ℓ − 1)`.

The page prints the left-hand clause as "if ℓ ≤ k(i), then (ℓ–1)R_iℓ", which would make
preferences *increase* away from the peak on the left and contradict clause (i); the book's own
words "decline monotonically 'to the left'" and the median-voter proof of Proposition 8.6 fix
the intended reading `ℓ R_i (ℓ − 1)`, used here. -/
def SinglePeaked {K : ℕ} (lab : A ≃ Fin K) (Ri : LinPref A) : Prop :=
  ∃ p : A, (∀ a : A, Ri.rel p a) ∧
    (∀ a b : A, lab p ≤ lab a → (lab b : ℕ) = (lab a : ℕ) + 1 → Ri.rel a b) ∧
    (∀ a b : A, lab a ≤ lab p → (lab b : ℕ) + 1 = (lab a : ℕ) → Ri.rel a b)

end MechanismDesign.SocialChoice


