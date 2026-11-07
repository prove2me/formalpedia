-- Prove2me | Definitions.Def_CertRandQROM_Event2
-- name    : CertRandQROM_Event2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:57.817896+00:00
-- url     : https://prove2.me/theorems/cc845609-700b-4cb6-b8d9-93e0d340c135
-- title:
--   Event2: every correct string has $s$ lightly queried symbols
-- statement:
--   For a code $C\subseteq\Sigma^n$, an algorithm $\mathcal A$, $\alpha\in\mathbb R$ and $s\in\mathbb N$, an oracle $h$ satisfies **Event2** if for every correct $x$ ($x\in C$ and $h(x)=0$) there is a set $I\subseteq[n]$ with $|I|=s$ such that
--
--   $$
--   \tilde w_{i,x_i}(h)<\frac{\alpha}{4n}\qquad\text{for all } i\in I .
--   $$
--
--   It is the condition of Lemma 7.4 (with $s=\lceil n/10\rceil$).
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §7.3, definition of Event2, p.43 (PDF p.45); condition of Lemma 7.4, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm
import Definitions.Def_CertRandQROM_IsCorrect

namespace CertRandQROM

/-- **Event2** (§7.3, p.43 of Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…; the
condition of Lemma 7.4, p.41): for every correct `x` (`x ∈ C` and `h(x) = 0`) there is a set
`I ⊆ [n]` of size `s` such that `w̃_{i, x_i}(h) < α/(4n)` for all `i ∈ I`. -/
def Event2 {n : ℕ} {S W O : Type} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    [Fintype O] {Q : ℕ} (C : Finset (Fin n → S)) (A : QueryAlg (Fin n × S) W O Q) (α : ℝ)
    (s : ℕ) (h : Fin n × S → Bool) : Prop :=
  ∀ x : Fin n → S, IsCorrect C h x →
    ∃ I : Finset (Fin n), I.card = s ∧ ∀ i ∈ I, totalQueryNorm A h (i, x i) < α / (4 * n)

end CertRandQROM


