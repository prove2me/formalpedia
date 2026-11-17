-- Prove2me | Definitions.Def_PermInvCC_Supplement_labelChanges
-- name    : PermInvCC_Supplement_labelChanges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:57:09.630738+00:00
-- url     : https://prove2.me/theorems/ac02956a-c3e8-4a78-a8e5-e785ed9a8889
-- title:
--   Number $B$ of label changes along the promised intersection counts
-- statement:
--   Let $g : \{0,1\}^n \times \{0,1\}^n \to \{-1,+1,*\}$ be a partial function. Let $D \subseteq \{0,\dots,n\}$ be the set of intersection sizes $t = |x \cap y|$ of promised inputs $(x,y)$, and let $\varphi(t)$ be the label of the promised inputs with $|x \cap y| = t$. The **number of label changes** $B$ is the number of pairs $t < t'$ of points of $D$ that are consecutive in $D$ (no point of $D$ lies strictly between them) with $\varphi(t) \ne \varphi(t')$:
--
--   $$B := \bigl|\{(t,t') : t, t' \in D,\ t < t',\ (t,t') \cap D = \emptyset,\ \varphi(t) \ne \varphi(t')\}\bigr|.$$
--
--   $B$ enters the comparable-margin bound of Theorem D.8; Lemma D.10 shows $\log(B+2) = O(Q^*(g)+1)$.
--
--   **Formalization Note** "Labels differ" is written as: some promised input with count $t$ has label $b$ and some promised input with count $t'$ has label $\neg b$. For a permutation-invariant $g$ with fixed weights every count has a single label (p.50), so this is the paper's $B$.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), §D.1, p.51 (PDF p.54); φ defined p.50 (PDF p.53)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_jointType

namespace PermInvCC

namespace Supplement

open Classical in
/-- The number `B` of **label changes** of a binary partial function `g` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, §D.1, p.51):
"the number of changes of label between consecutive points in the ordered domain of `φ`", where
`φ` is the partial label function of the intersection count `t = |x ∩ y|` (p.50).

**Formalization Note.** Binary strings are `Fin n → Fin 2`, and `|x ∩ y| = jointType x y 1 1`.
The domain of `φ` is the set `D ⊆ {0, …, n}` of intersection counts of promised inputs. `B` counts
the pairs `t < t'` of points of `D` with no point of `D` strictly between them (consecutive in
the ordered domain, skipping unpromised counts) at which promised inputs carry opposite labels.
For permutation-invariant `g` with fixed weights each `t ∈ D` has a single label (p.50), so this
is the paper's count. -/
noncomputable def labelChanges {n : ℕ} (g : PartialFn n 2) : ℕ :=
  let D : Finset ℕ := (Finset.range (n + 1)).filter fun t =>
    ∃ x y : Fin n → Fin 2, g x y ≠ none ∧ jointType x y 1 1 = t
  let lab : ℕ → Bool → Prop := fun t b =>
    ∃ x y : Fin n → Fin 2, g x y = some b ∧ jointType x y 1 1 = t
  ((D ×ˢ D).filter fun p => p.1 < p.2 ∧ (∀ u ∈ D, ¬ (p.1 < u ∧ u < p.2)) ∧
    ∃ b, lab p.1 b ∧ lab p.2 (!b)).card

end Supplement

end PermInvCC


