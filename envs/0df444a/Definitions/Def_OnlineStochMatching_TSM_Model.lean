-- Prove2me | Definitions.Def_OnlineStochMatching_TSM_Model
-- name    : OnlineStochMatching_TSM_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:22:15.215037+00:00
-- url     : https://prove2.me/theorems/f39a048a-6581-4b43-80f9-f3f66e47c18d
-- title:
--   The i.i.d. arrival law with $e_i = 1$, the offline optimum OPT and the constant $\alpha$ (Section 2, Theorem 5)
-- statement:
--   Let $G = (A, I, E)$ be a bipartite graph with a finite set $A$ of **advertisers**, a finite set $I$ of **impression types**, and edge set $E \subseteq A \times I$. In the online stochastic matching problem with $e_i = 1$ for every type, $n = |I|$ impressions arrive one at a time, and their types $\omega(0), \dots, \omega(n-1)$ are drawn independently and uniformly from $I$. Every arrival sequence $\omega : \{0,\dots,n-1\} \to I$ therefore has probability $|I|^{-n}$, and the probability of an event $P$ is
--   $$\Pr[P] = \frac{\#\{\omega : P(\omega)\}}{|I|^{n}}.$$
--   With $I = \{0, \dots, n-1\}$ the same law describes $n$ balls thrown independently and uniformly into $n$ bins.
--
--   The **realization graph** $\hat G$ has the advertisers on one side, one node per arrival $t$ on the other, and an edge between $a$ and $t$ whenever $(a, \omega(t)) \in E$. The offline optimum $\mathrm{OPT}(\omega)$ is the size of a maximum matching of $\hat G$, that is, the largest number of arrivals that can be assigned, with hindsight, to pairwise distinct adjacent advertisers.
--
--   Finally, the definition fixes the constant
--   $$\alpha = \frac{1 - 2/e^2}{4/3 - 2/(3e)} \approx 0.67029$$
--   of Theorem 5.
--
--   These objects are shared by every probabilistic statement of the mission: the balls-in-bins facts, the bounds on ALG and OPT, and the goal theorem.
--
--   **Formalization Note** Probabilities are counting ratios over all arrival sequences `Fin n → I`, so no measurability conditions arise. A matching of $\hat G$ is encoded as a partial assignment `Fin n → Option A` that uses only edges and is injective on matched arrivals; OPT is the largest size of such an assignment, a maximum over a finite nonempty set (the empty assignment always qualifies). The number $e$ is `Real.exp 1`.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, pp. 3–4, Section 2; p. 6, Theorem 5 and the standing assumption e_i = 1 of Section 4.2

import Mathlib

namespace OnlineStochMatching.TSM

open Finset

/-- The probability of an event under the arrival law of the online stochastic matching problem
with `e_i = 1` for every impression type (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online
Stochastic Matching: Beating 1-1/e*, arXiv:0905.4100v1, §2, p. 3, and the standing assumption of
§4.2, p. 6): `n` arrivals `ω 0, …, ω (n-1)` are drawn i.i.d. uniformly from the finite set `I` of
impression types, so every arrival sequence `ω : Fin n → I` has probability `1 / |I|^n`, and

  `prob n P = #{ω : Fin n → I | P ω} / |I|^n`.

The same formula with `I = Fin n` is the law of `n` balls thrown i.i.d. uniformly into `n` bins
(§2.1, p. 4). -/
noncomputable def prob {I : Type} [Fintype I] (n : ℕ) (P : (Fin n → I) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card I : ℝ) ^ n

/-- A matching of the realization graph `Ĝ(Î)` (§2, p. 4). The graph `G = (A, I, E)` has
advertisers `A`, impression types `I` and edge set `E ⊆ A × I`; the realization graph has one
node per arrival `t`, of type `ω t`, and the edge `(a, t)` iff `(a, ω t) ∈ E`. A matching is
encoded as `M : Fin n → Option A`, where `M t = some a` means that arrival `t` is matched to
advertiser `a`: every matched pair is an edge, and no advertiser is matched twice. -/
def IsRealizationMatching {A I : Type} {n : ℕ} (E : Finset (A × I)) (ω : Fin n → I)
    (M : Fin n → Option A) : Prop :=
  (∀ t a, M t = some a → (a, ω t) ∈ E) ∧ ∀ s t a, M s = some a → M t = some a → s = t

/-- The number of arrivals that a partial assignment `M` matches. -/
def matchSize {A : Type} {n : ℕ} (M : Fin n → Option A) : ℕ :=
  (Finset.univ.filter fun t => (M t).isSome = true).card

/-- `OPT(Î)` (§2, p. 4): the size of a maximum matching of the realization graph `Ĝ(Î)` for the
arrival sequence `ω`, i.e. the largest number of arrivals that can be assigned, with hindsight,
to pairwise distinct adjacent advertisers. -/
noncomputable def OPT {A I : Type} [Fintype A] {n : ℕ} (E : Finset (A × I)) (ω : Fin n → I) :
    ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n → Option A)).filter (IsRealizationMatching E ω)).sup
    matchSize

/-- The constant `α := (1 - 2/e²) / (4/3 - 2/(3e)) ≈ 0.67029` of Theorem 5 (p. 6). -/
noncomputable def alpha : ℝ :=
  (1 - 2 / Real.exp 1 ^ 2) / (4 / 3 - 2 / (3 * Real.exp 1))

end OnlineStochMatching.TSM


