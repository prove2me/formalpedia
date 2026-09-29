-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_Instance
-- name    : SetCoverThreshold_SetCover_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:54:10.586447+00:00
-- url     : https://prove2.me/theorems/ab4942e7-c5fb-495f-aad0-2ef8ecc55845
-- title:
--   Set-cover instances, their encoding, and approximation within $\rho(n)$
-- statement:
--   **Set cover** (p. 634): "Let S be a set of n points and 𝒞 = {S_1, S_2, …, S_s} a collection of subsets of S. Set cover is the problem of selecting as few as possible subsets from 𝒞 such that every point in S is contained in at least one of the selected subsets." An instance has points $\{0,\dots,n-1\}$ and a list of subsets $S_1,\dots,S_s$. A *cover* is a set of indices whose subsets together contain every point; the instance is *coverable* if every point lies in some $S_i$.
--
--   **Encoding.** $n$ is written in unary, then a separator, then each subset as its characteristic vector of length $n$ followed by a separator. The code length is $\Theta(ns+n)$.
--
--   **Approximation.** The paper measures an algorithm by "the ratio between the number of subsets used in the cover output by the algorithm and the number of subsets used by the optimal solution … the largest value that it can attain on an input instance is the approximation ratio of the algorithm" (p. 634). A deterministic polynomial-time algorithm $A$ *approximates set cover within $\rho(n)$* if there is $n_0$ such that on every coverable instance with $n\ge n_0$ points the value $v$ that $A$ outputs satisfies
--
--   $$\mathrm{OPT}\ \le\ v\ \le\ \rho(n)\cdot\mathrm{OPT},$$
--
--   that is, some cover has at most $v$ subsets and $v\le\rho(n)\,|C|$ for every cover $C$.
--
--   **Formalization Note** The algorithm outputs a number (in unary) rather than a cover; an algorithm that outputs a cover yields one by counting, so this hypothesis is weaker and the hardness theorem stronger. The guarantee is required only for $n\ge n_0$: for $\rho(n)=(1-\varepsilon)\ln n<1$ (small $n$) no value could satisfy it. For $\varepsilon\ge 1$ the ratio $(1-\varepsilon)\ln n$ is at most $0$ and no algorithm approximates within it.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 634, Section 1 (set cover, approximation ratio)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.SetCover

/-- A set-cover instance (Feige 1998, p. 634): the points `Fin n` and a list of subsets
`S_1, …, S_s`. -/
structure SCInstance where
  n : ℕ
  sets : List (Finset (Fin n))

namespace SCInstance

variable (I : SCInstance)

/-- A cover: a set of indices of the list whose subsets together contain every point. -/
def IsCover (C : Finset (Fin I.sets.length)) : Prop :=
  ∀ x : Fin I.n, ∃ i ∈ C, x ∈ I.sets.get i

/-- The instance has a cover: every point lies in some subset. -/
def Coverable : Prop := ∀ x : Fin I.n, ∃ S ∈ I.sets, x ∈ S

/-- String encoding over `Option Bool`: `n` in unary (`some true`, `n` times), a separator
`none`, then each subset as its characteristic bit-vector of length `n` followed by `none`. -/
def encode : List (Option Bool) :=
  List.replicate I.n (some true) ++ none ::
    I.sets.flatMap fun S => List.ofFn (fun x : Fin I.n => some (decide (x ∈ S))) ++ [none]

end SCInstance

/-- A deterministic polynomial-time algorithm approximates set cover within `ρ(n)`
(Feige 1998, p. 634), in value form: there are a polynomial-time computable
`A : List (Option Bool) → List Unit` and a threshold `n₀` such that on every coverable instance
with `n ≥ n₀` points the output length `v` satisfies: some cover has at most `v` subsets, and
`v ≤ ρ(n) · |C|` for every cover `C`. -/
def ApproximableWithin (ρ : ℕ → ℝ) : Prop :=
  ∃ A : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable A ∧
    ∃ n₀ : ℕ, ∀ I : SCInstance, n₀ ≤ I.n → I.Coverable →
      (∃ C, I.IsCover C ∧ C.card ≤ (A I.encode).length) ∧
        ∀ C, I.IsCover C → ((A I.encode).length : ℝ) ≤ ρ I.n * C.card

end SetCoverThreshold.SetCover


