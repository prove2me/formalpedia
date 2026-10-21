-- Prove2me | Definitions.Def_NatureSLT_GrowthFunction_vcDim
-- name    : NatureSLT_GrowthFunction_vcDim
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:04.676007+00:00
-- url     : https://prove2.me/theorems/bcf8a731-8a90-437b-b163-093569a2c0da
-- title:
--   Shattering and the VC dimension of a set of indicator functions
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a set $Z$. Vectors $z_1, \dots, z_h \in Z$ are **shattered** by the set if they can be separated into two classes in all $2^h$ possible ways: for every choice $\delta_1, \dots, \delta_h \in \{0, 1\}$ there is $\alpha \in \Lambda$ with $Q(z_i, \alpha) = \delta_i$ for $i = 1, \dots, h$.
--
--   The **VC dimension** of the set is the maximum number $h$ of vectors $z_1, \dots, z_h$ that can be shattered; if for every $n$ there exist $n$ vectors that are shattered, the VC dimension is infinite:
--
--   $$\operatorname{VC}(Q) = \sup\{h \in \mathbb N : \text{some } z_1, \dots, z_h \in Z \text{ are shattered}\} \in \mathbb N \cup \{\infty\}.$$
--
--   **Formalization Note** Indicator values are booleans (`true` = $1$); `Q α z` is the book's $Q(z, \alpha)$, and the vectors are indexed by `Fin h`. The VC dimension takes values in the extended naturals, where the supremum of an unbounded set is $\infty$. The empty family of vectors ($h = 0$) is shattered as soon as $\Lambda$ is nonempty; for empty $\Lambda$ nothing is shattered and the value is $0$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 80, Section 3.6

import Mathlib

namespace NatureSLT.GrowthFunction

/-- The vectors `z₁, …, z_h` are **shattered** by the indicator functions `Q(z, α)`, `α ∈ Λ`
(Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 80): they can be
separated into two classes in all `2^h` possible ways, i.e. for every assignment
`δ₁, …, δ_h ∈ {0, 1}` some `α ∈ Λ` has `Q(zᵢ, α) = δᵢ` for every `i`. Values are `Bool`
(`true` = `1`); `Q α z` is the book's `Q(z, α)`. -/
def Shatters {Z Λ : Type*} (Q : Λ → Z → Bool) {h : ℕ} (z : Fin h → Z) : Prop :=
  ∀ δ : Fin h → Bool, ∃ α : Λ, ∀ i : Fin h, Q α (z i) = δ i

/-- The **VC dimension of a set of indicator functions** (Vapnik, *The Nature of Statistical
Learning Theory*, 2nd ed., §3.6, p. 80): the maximum number `h` of vectors `z₁, …, z_h` that can
be shattered by `Q(z, α)`, `α ∈ Λ`; it is `∞` (`⊤`) if for every `n` some `n` vectors are
shattered. Valued in `ℕ∞`, where the supremum of an unbounded set of naturals is `⊤`. (For empty
`Λ` no sample, not even the empty one, is shattered and the value is `0`; the theorems of this
mission assume `Λ` nonempty.) -/
noncomputable def vcDim {Z Λ : Type*} (Q : Λ → Z → Bool) : ℕ∞ :=
  ⨆ (h : ℕ) (_ : ∃ z : Fin h → Z, Shatters Q z), (h : ℕ∞)

end NatureSLT.GrowthFunction


