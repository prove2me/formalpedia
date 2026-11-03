-- Prove2me | Definitions.Def_RankOneBTF_frProb
-- name    : RankOneBTF_frProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:16.573839+00:00
-- url     : https://prove2.me/theorems/cefb73ff-7273-46b4-ad8b-7a5334d1dea2
-- title:
--   Fully-random and semi-random corruption models
-- statement:
--   **Fully-random model.** Fix $p\in[0,1]$ and the ground truth $\bar{\mathcal W}=\bar x\otimes\bar y\otimes\bar z$. Each entry $(i,j,k)$ is corrupted independently with probability $p$: then $g_{ijk}:=1-\bar x_i\bar y_j\bar z_k$; otherwise $g_{ijk}:=\bar x_i\bar y_j\bar z_k$. Writing $C\in\{0,1\}^{n\times m\times l}$ for the corruption pattern, $C$ has probability
--   $$
--   \mathbb P[C]=\prod_{i,j,k}p^{C_{ijk}}(1-p)^{1-C_{ijk}},
--   $$
--   and the probability of a property $E$ of the noisy tensor is $\sum_{C:\,E(\mathcal G(C))}\mathbb P[C]$; expectations are the corresponding weighted sums.
--
--   **Semi-random model.** First $\mathcal G$ is drawn from the fully-random model; then an adversary applies an arbitrary sequence of monotone transformations: an entry that is $1$ in $\bar{\mathcal W}$ and $0$ in $\mathcal G$ may be reverted to $1$, and an entry that is $0$ in $\bar{\mathcal W}$ and $1$ in $\mathcal G$ may be reverted to $0$.
--
--   **Formalization Note** The probability space is the finite set of patterns with product Bernoulli($p$) weights (`patternWeight`, `frProb`, `frExpect`), and $\mathcal G(C)$ is $\bar{\mathcal W}$ with the entries of $C$ flipped (`corrupt`). An adversary is any map $\mathcal G\mapsto\mathcal G'$ whose output agrees at every entry with $\mathcal G$ or with $\bar{\mathcal W}$ (`IsMonotoneAdversary`): a sequence of reversions changes an arbitrary, $\mathcal G$-dependent subset of the corrupted entries back to the ground truth and nothing else.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §1, p.3 (fully-random and semi-random corruption models); p.5 (independence of corruptions, proof of Proposition 1)

import Mathlib
import Definitions.Def_RankOneBTF_groundTruth

namespace RankOneBTF

/-- The probability of a **corruption pattern** `C` (`C i j k = true` iff entry `(i,j,k)` is
corrupted) under the fully-random corruption model with parameter `p`: every entry is corrupted
independently with probability `p` (arXiv:2202.07053v3, §1, p.3; independence: proof of
Proposition 1, p.5), so `P[C] = Π_{i,j,k} p^{C_ijk} (1 − p)^{1 − C_ijk}`. -/
def patternWeight {n m l : ℕ} (p : ℝ) (C : BTensor n m l) : ℝ :=
  ∏ i, ∏ j, ∏ k, if C i j k then p else 1 - p

/-- The noisy tensor obtained from the ground truth `W̄` and a corruption pattern `C`
(arXiv:2202.07053v3, p.3): a corrupted entry is `g_ijk := 1 − x̄_i ȳ_j z̄_k`, an uncorrupted one
`g_ijk := x̄_i ȳ_j z̄_k`. -/
def corrupt {n m l : ℕ} (W C : BTensor n m l) : BTensor n m l :=
  fun i j k => xor (W i j k) (C i j k)

/-- The probability, under the **fully-random corruption model** with parameter `p` and ground
truth `W̄`, that the noisy tensor `G` satisfies the property `E`
(arXiv:2202.07053v3, §1, p.3).

**Formalization Note** The probability space is the finite set of corruption patterns
`C ∈ {0,1}^{n×m×l}` with the product Bernoulli(`p`) weights `patternWeight p C`; the
probability of `E` is the explicit finite sum `Σ_{C : E(corrupt W̄ C)} patternWeight p C`. For
`p ∈ [0,1]` these weights form a probability distribution. -/
noncomputable def frProb {n m l : ℕ} (p : ℝ) (W : BTensor n m l) (E : BTensor n m l → Prop) :
    ℝ := by
  classical
  exact ∑ C : BTensor n m l, if E (corrupt W C) then patternWeight p C else 0

/-- The expectation, under the fully-random corruption model with parameter `p` and ground
truth `W̄`, of a real function `X` of the noisy tensor `G` (arXiv:2202.07053v3, §1, p.3):
`Σ_C patternWeight p C · X(corrupt W̄ C)`. -/
def frExpect {n m l : ℕ} (p : ℝ) (W : BTensor n m l) (X : BTensor n m l → ℝ) : ℝ :=
  ∑ C : BTensor n m l, patternWeight p C * X (corrupt W C)

/-- An **adversary of the semi-random corruption model** (arXiv:2202.07053v3, §1, p.3): it maps
the noisy tensor `G` to a tensor obtained "by applying an arbitrary sequence of monotone
transformations": an entry that is `1` in `W̄` and `0` in `G` may be reverted to `1`, and an
entry that is `0` in `W̄` and `1` in `G` may be reverted to `0`.

**Formalization Note** A sequence of such reversions changes an arbitrary subset of the entries
where `G` differs from `W̄` back to `W̄`, and nothing else; so the result agrees, entry by entry,
either with `G` or with `W̄`. The choice of the subset may depend on `G` arbitrarily, which is
why the adversary is any function of `G` with this property. -/
def IsMonotoneAdversary {n m l : ℕ} (W : BTensor n m l) (adv : BTensor n m l → BTensor n m l) :
    Prop :=
  ∀ G i j k, adv G i j k = G i j k ∨ adv G i j k = W i j k

end RankOneBTF


