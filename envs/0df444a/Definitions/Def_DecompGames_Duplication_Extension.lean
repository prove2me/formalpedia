-- Prove2me | Definitions.Def_DecompGames_Duplication_Extension
-- name    : DecompGames_Duplication_Extension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:17.225033+00:00
-- url     : https://prove2.me/theorems/39e6d66c-abf0-4dc9-8536-cd927b41ce88
-- title:
--   The extending map Ť and extensions of the measure vector, along a collapsing map π (Definition 3.13, p. 18, generalized)
-- statement:
--   Definition 3.13 duplicates a strategy $s^i_1$ of player $i$ into two strategies $s^i_0,s^i_1$. This module states it for a general **collapsing map**: for each player $j$, a finite strategy set $S'^j$ and a map $\pi^j:S'^j\to S^j$, with $\pi(s')=(\pi^j(s'^j))_{j\in N}$.
--
--   1. **The extending map** $\check T$. For a game (or any vector of functions) $g$ on $S$, $\check g=\check T(g)$ is the game on $S'$ with $\check g^j(s')=g^j(\pi(s'))$. Applied to a co-measure vector $\gamma$, regarded as the nonstrategic game $(\gamma^j)_{j\in N}$, it gives the extended co-measure $\check\gamma^j(s')=\gamma^j(\pi(s'))$.
--   2. **Extension of a measure vector.** $\check\mu$ is an extension of $\mu$ along $\pi$ if, for every player $j$ and every $a\in S^j$,
--   $$\sum_{b\in S'^j:\ \pi^j(b)=a}\check\mu^j(b)=\mu^j(a).$$
--
--   For a single duplication, $S'^i=S^i\cup\{s^i_0\}$, $\pi^i(s^i_0)=s^i_1$, $\pi^i$ is the identity on $S^i$ and $\pi^j$ is the identity for $j\ne i$. Then $\check g^j(s)=g^j(s)$ for $s\in S$ and $\check g^j(s^i_0,s^{-i})=g^j(s^i_1,s^{-i})$, and the fibre condition reads $\check\mu^j=\mu^j$ for $j\ne i$, $\check\mu^i(s^i_0)+\check\mu^i(s^i_1)=\mu^i(s^i_1)$ and $\check\mu^i=\mu^i$ elsewhere, which is the paper's extension of $\mu$. The extended co-measure copies: $\check\gamma^i=\gamma^i$ and $\check\gamma^j(s^i_0,s^{-(i,j)})=\check\gamma^j(s^i_1,s^{-(i,j)})=\gamma^j(s^i_1,s^{-(i,j)})$ for $j\ne i$, as in the proof of Lemma 3.14(iv), p. 40.
--
--   These objects state that duplicating strategies commutes with the $(\mu,\gamma)$-decomposition (Lemma 3.14, Theorem 3.15).
--
--   **Formalization Note** The printed extension of $\gamma$ in Definition 3.13 (ii) requires $\check\gamma^j(s^i_0,\cdot)+\check\gamma^j(s^i_1,\cdot)=\gamma^j(s^i_1,\cdot)$; with that sum Lemma 3.14(i) and Theorem 3.15 are false (two players, two strategies each, $\mu\equiv1$, $\gamma\equiv1$, $g^1=g^2=\Psi$ with $\Psi(s^1,s^2)=\Psi(t^1,t^2)=1$, $\Psi(s^1,t^2)=\Psi(t^1,s^2)=-1$, duplicating $s^1$ with $\check\mu^1=(\tfrac12,\tfrac12,1)$, $\check\gamma^2(s^1_0,\cdot)=\check\gamma^2(s^1_1,\cdot)=\tfrac12$: $\check g$ is not $\check\gamma$-potential). The module uses the copy $\check\gamma=\check T(\gamma)$, which is what Theorem 3.15 calls "the extended nonstrategic game of $\gamma$" and what the proof on p. 40 uses. One map `extend` serves for games and for co-measure vectors. Positivity of $\check\mu$ is assumed in the theorems.
-- source:
--   Abdou, Pnevmatikos, Scarsini & Venel, Decomposition of Games: Some Strategic Considerations, arXiv:1901.06048v2, p. 18, Definition 3.13; p. 19, Theorem 3.15 ("the extended nonstrategic game of γ"); p. 40, proof of Lemma 3.14(iv)

import Mathlib
import Definitions.Def_DecompGames_Duplication_Games

namespace DecompGames.Duplication

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (S' i)] [∀ i, DecidableEq (S' i)]

/-- The extending map `Ť` of Definition 3.13 (p. 18), along a collapsing map
`π = (πʲ : S'ʲ → Sʲ)_{j ∈ N}`: `ǧʲ(s') = gʲ(π(s'))` with `π(s') = (πᵏ(s'ᵏ))_{k ∈ N}`.
Duplicating `s¹ⁱ` into `s⁰ⁱ, s¹ⁱ` is the case `S'ⁱ = Sⁱ ∪ {s⁰ⁱ}`, `πⁱ(s⁰ⁱ) = s¹ⁱ`, `πⁱ = id` on
`Sⁱ`, `πʲ = id` for `j ≠ i`. Applied to a co-measure vector `γ`, read as the nonstrategic game
`(γʲ)_{j ∈ N}`, it gives the extended co-measure `γ̌ = Ť(γ)` of Theorem 3.15. -/
def extend (π : ∀ i, S' i → S i) (g : ι → (∀ i, S i) → ℝ) : ι → (∀ i, S' i) → ℝ :=
  fun j s' => g j (fun k => π k (s' k))

/-- `μ'` is an extension of `μ` along `π` (Definition 3.13, p. 18, measures): for every player `j`
and every `a ∈ Sʲ`, the `μ'ʲ`-mass of the fibre `(πʲ)⁻¹(a)` is `μʲ(a)`. For a single duplication
this is (i) `μ̌ʲ = μʲ` for `j ≠ i` and (ii) `μ̌ⁱ(s⁰ⁱ) + μ̌ⁱ(s¹ⁱ) = μⁱ(s¹ⁱ)`, `μ̌ⁱ = μⁱ` elsewhere. -/
def IsMeasureExtension (π : ∀ i, S' i → S i) (μ : ∀ i, S i → ℝ) (μ' : ∀ i, S' i → ℝ) : Prop :=
  ∀ j (a : S j), ∑ b ∈ univ.filter (fun b => π j b = a), μ' j b = μ j a

end DecompGames.Duplication


