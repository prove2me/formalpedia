-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_RandomPartition
-- name    : RelatedSchedFPTAS796_Main_RandomPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:17.829941+00:00
-- url     : https://prove2.me/theorems/0ab5a49f-960f-44ed-af70-0c2f86e4b7de
-- title:
--   Random partitions of a multiset into $K$ parts
-- statement:
--   Let $X$ be a multiset with $N$ elements. A **random partition** $X_1\cup\dots\cup X_K$ of $X$ puts every element (occurrence) independently and uniformly into one of the $K$ parts, as in Algorithm 1, lines 2 and 8 ("Partition $J$ independently and uniformly into $J_1,\dots,J_K$"). Equivalently it is a uniformly random map $f$ from the $N$ occurrences to $\{1,\dots,K\}$ with $X_i=f^{-1}(i)$, and the probability of an event is the fraction of the $K^N$ maps on which it holds. For $Y\subseteq X$, $|Y\cap X_i|$ is the number of occurrences of $Y$ in part $i$.
--
--   This is the randomness of Lemmas 4.1–4.3.
--
--   **Formalization Note** Occurrences are `Fin N` (the integer values of the elements of $X$ play no role in Lemmas 4.1–4.3); parts are `Fin K`; the probability is `#{f | E f} / K^N`.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, §4.1 p.10 (Lemmas 4.1–4.3); Algorithm 1 p.11, lines 2 and 8

import Mathlib

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-!
# Random partitions of a multiset

Chen, Hu, Lian, Mao, Zhang, *Faster Approximation Schemes for Scheduling on Related Machines*,
STOC 2027 submission #796 (October 2026), §4.1 p.10 (Lemmas 4.1–4.3) and Algorithm 1 p.11,
lines 2 and 8 ("Partition J independently and uniformly into J_1, …, J_K").

**Formalization Note.** A multiset `X` of `N` elements is represented by its occurrences `Fin N`
(the values of the elements play no role). A random partition `X_1 ∪ ⋯ ∪ X_K` puts every occurrence
independently and uniformly into one of the `K` parts: it is a uniformly random map
`f : Fin N → Fin K`, and `X_i = f⁻¹(i)`. The probability of an event `E` is the fraction of the
`K^N` maps satisfying it.
-/

/-- The probability of the event `E` for a uniformly random partition of `N` occurrences into `K`
parts: `#{f : Fin N → Fin K | E f} / K^N`. -/
noncomputable def partitionProb (N K : ℕ) (E : (Fin N → Fin K) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / (K : ℝ) ^ N

/-- `|Y ∩ X_i|` for the partition `f` (`X_i = f⁻¹(i)`) and `Y ⊆ X`. -/
def partCount {N K : ℕ} (f : Fin N → Fin K) (Y : Finset (Fin N)) (i : Fin K) : ℕ :=
  (Y.filter (fun x => f x = i)).card

end RelatedSchedFPTAS796.Main


