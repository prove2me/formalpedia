-- Prove2me | Definitions.Def_HousingRI_IsImprovement
-- name    : HousingRI_IsImprovement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:29.286875+00:00
-- url     : https://prove2.me/theorems/daebed5e-0a27-458f-8d3b-5818d3288436
-- title:
--   Improvement for agent $i$ (corrected: no new acceptable objects other than $i$)
-- statement:
--   Let $A$ (the profile $R$) and $\tilde A$ (the profile $\tilde R$) be two preference profiles over the objects $N$, with $j\,R_k\,l$ iff $A_{kl}\le A_{kj}$, $P_k$ its strict part and $I_k$ its indifference part, and let $i\in N$. Then $\tilde R$ is an **improvement for $i$** with respect to $R$ if
--
--   1. $\tilde R_i=R_i$;
--   2. for all $j\ne i$ and all $k$ with $k\,R_j\,j$: $i\,I_j\,k\Rightarrow i\,\tilde R_j\,k$ and $i\,P_j\,k\Rightarrow i\,\tilde P_j\,k$;
--   3. for all $j\ne i$ and all $k,l\ne i$ with $k\,R_j\,j$ and $l\,R_j\,j$: $k\,R_j\,l\iff k\,\tilde R_j\,l$;
--   4. for all $j\ne i$ and all $k\ne i$: $k\,\tilde R_j\,j\Rightarrow k\,R_j\,j$.
--
--   In words: only agents other than $i$ change their preferences; object $i$ can only move up relative to acceptable objects; the order among acceptable objects other than $i$ is kept; and no object other than $i$ becomes acceptable.
--
--   **Formalization Note** Conditions (1)–(3) are those printed on p.13; condition (4) is added because with (1)–(3) alone Theorem 1 is false. For $N=\{1,2,3\}$, $i=1$, $R_1: 2\,P\,1\,P\,3$, $R_2: 1\,P\,2\,P\,3$, $R_3: 2\,P\,3\,P\,1$, and $\tilde R$ equal to $R$ except $\tilde R_2: 3\,P\,1\,P\,2$, conditions (1)–(3) hold, but the strong core allocation moves from $\{(1,2),(3)\}$ to $\{(1),(2,3)\}$ and agent 1 loses object 2. Condition (4) agrees with the page's gloss of (3) and with the proof's "$\tilde R_j$ is obtained from $R_j$ by shifting $i$ up" (p.14). Condition (1) is the ordinal equivalence of the two rows.
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §3, p.13 (definition of improvement, conditions (1)–(3)); condition (4) added, see the note.

import Mathlib
import Definitions.Def_HousingRI_SamePref

namespace HousingRI

/-- **Improvement for agent `i`** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, §3, p.13),
**corrected**: "Let R, R̃ be two preference profiles over objects N. Let i ∈ N. We say that R̃ is
an improvement for i with respect to R if
(1). R̃ᵢ = Rᵢ;
(2). for all j ≠ i and all k with k Rⱼ j, i Iⱼ k ⟹ i R̃ⱼ k and i Pⱼ k ⟹ i P̃ⱼ k; and
(3). for all j ≠ i and all k, l ≠ i with k, l Rⱼ j, k Rⱼ l ⟺ k R̃ⱼ l."
plus the added condition
(4). for all j ≠ i and all k ≠ i, k R̃ⱼ j ⟹ k Rⱼ j (no object other than `i` becomes
acceptable to an agent `j ≠ i`).

**Formalization Note.** Preferences are utility matrices (`k Rⱼ l` is `A j l ≤ A j k`; `Pⱼ` is
`<`, `Iⱼ` is `=`); `A` is `R` and `Ã` is `R̃`. Condition (1) is the ordinal equivalence
`SamePref A Ã i`, not equality of the rows. Condition (4) is a correction: with (1)–(3) alone
Theorem 1 (p.13) is false. For `N = {1,2,3}`, `i = 1`, `R₁ : 2 P 1 P 3`, `R₂ : 1 P 2 P 3`,
`R₃ : 2 P 3 P 1`, and `R̃` equal to `R` except `R̃₂ : 3 P 1 P 2`, conditions (1)–(3) hold (object 3
is unacceptable to agent 2 at `R₂`, so (3) does not constrain it), `τ(R) = {(1,2),(3)}` and
`τ(R̃) = {(1),(2,3)}`, so agent 1 gets object 2 at `R` and her own object at `R̃`, which she
likes less. The page's own gloss of (3) ("for each pair of acceptable objects different from i,
preferences remain unchanged") and the proof's "R̃ⱼ is obtained from Rⱼ by shifting i up" (p.14)
are consistent with (4). -/
def IsImprovement {N : Type*} (i : N) (A Ã : N → N → ℝ) : Prop :=
  SamePref A Ã i ∧
  (∀ j, j ≠ i → ∀ k, A j j ≤ A j k →
      (A j i = A j k → Ã j k ≤ Ã j i) ∧ (A j k < A j i → Ã j k < Ã j i)) ∧
  (∀ j, j ≠ i → ∀ k l, k ≠ i → l ≠ i → A j j ≤ A j k → A j j ≤ A j l →
      (A j l ≤ A j k ↔ Ã j l ≤ Ã j k)) ∧
  (∀ j, j ≠ i → ∀ k, k ≠ i → Ã j j ≤ Ã j k → A j j ≤ A j k)

end HousingRI


