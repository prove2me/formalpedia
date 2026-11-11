-- Prove2me | Definitions.Def_MetaSearch_Heyting_JoinMeet
-- name    : MetaSearch_Heyting_JoinMeet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:21:53.696201+00:00
-- url     : https://prove2.me/theorems/60ccfac4-f651-43b3-9d2f-1a42c4d45786
-- title:
--   The join S₀ ∨ S₁ and the meet S₀ ∧ S₁ of search problems (Definitions 2.6 and 2.10)
-- statement:
--   Let $S_0,S_1$ be search problems; a bit $b\in\{0,1\}$ is written as the one-bit string $b$, and $S_b$ is $S_0$ for $b=0$ and $S_1$ for $b=1$.
--
--   **Join (Definition 2.6).** $S_0\vee S_1$ has inputs $\langle x,b\rangle$; its valid outputs are the $y$ with $(x,y)\in S_b$. An input not of the form $\langle x,b\rangle$ is poorly formatted and every output is valid for it:
--   $$S_0\vee S_1=\{(\langle x,b\rangle,y):(x,y)\in S_b\}\;\cup\;\{(z,y): z\ne\langle x,b\rangle \text{ for all } x,b\}.$$
--
--   **Meet (Definition 2.10).** $S_0\wedge S_1$ has inputs $\langle x_0,x_1\rangle$; its valid outputs are the pairs $\langle y,b\rangle$ with $(x_b,y)\in S_b$. An input not of the form $\langle x_0,x_1\rangle$ accepts every output; for a well-formatted input, an output not of the form $\langle y,b\rangle$ is never valid:
--   $$S_0\wedge S_1=\{(\langle x_0,x_1\rangle,\langle y,b\rangle):(x_b,y)\in S_b\}\;\cup\;\{(z,w): z\ne\langle x_0,x_1\rangle\text{ for all }x_0,x_1\}.$$
--
--   **Formalization Note.** `pick b S₀ S₁` is $S_b$; the formatting conditions are stated with the injective pairing `pair`.
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 18-19, Definitions 2.6 and 2.10

import Mathlib
import Definitions.Def_MetaSearch_Heyting_SearchProblem

namespace MetaSearch.Heyting

/-! # The join `S₀ ∨ S₁` (Definition 2.6) and the meet `S₀ ∧ S₁` (Definition 2.10)

The bit `b ∈ {0,1}` is the one-bit string `[b]` (`false` is `0`), so `⟨x, b⟩` is
`pair x [b]`. -/

/-- The problem `S_b`: `S₀` for `b = 0` (`false`), `S₁` for `b = 1` (`true`). -/
def pick (b : Bool) (S₀ S₁ : SearchProblem) : SearchProblem := if b then S₁ else S₀

/-- **Definition 2.6.** `S₀ ∨ S₁`: the pairs `(⟨x, b⟩, y)` with `b ∈ {0,1}` and `(x, y) ∈ S_b`,
and all pairs `(z, y)` with `z` not of the form `⟨x, b⟩` (poorly formatted inputs accept every
output). -/
def join (S₀ S₁ : SearchProblem) : SearchProblem :=
  {q | (∃ x b, q.1 = pair x [b] ∧ (x, q.2) ∈ pick b S₀ S₁) ∨ ¬ ∃ x b, q.1 = pair x [b]}

/-- **Definition 2.10.** `S₀ ∧ S₁`: the pairs `(⟨x₀, x₁⟩, ⟨y, b⟩)` with `b ∈ {0,1}` and
`(x_b, y) ∈ S_b`, and all pairs `(z, w)` with `z` not of the form `⟨x₀, x₁⟩`. For a
well-formatted input, an output not of the form `⟨y, b⟩` is never valid. -/
def meet (S₀ S₁ : SearchProblem) : SearchProblem :=
  {q | (∃ x₀ x₁ y b, q.1 = pair x₀ x₁ ∧ q.2 = pair y [b] ∧
        ((if b then x₁ else x₀), y) ∈ pick b S₀ S₁) ∨
      ¬ ∃ x₀ x₁, q.1 = pair x₀ x₁}

end MetaSearch.Heyting


