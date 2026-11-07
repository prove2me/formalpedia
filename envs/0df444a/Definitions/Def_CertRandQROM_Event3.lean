-- Prove2me | Definitions.Def_CertRandQROM_Event3
-- name    : CertRandQROM_Event3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:33:07.055999+00:00
-- url     : https://prove2.me/theorems/8acf804d-0931-4a72-b883-6de14931ce7b
-- title:
--   Event3: a likely correct string with $s$ lightly queried symbols
-- statement:
--   For a code $C\subseteq\Sigma^n$, an algorithm $\mathcal A$ with outputs in $\Sigma^n\cup\{\bot\}$, $\alpha\in\mathbb R$ and $s\in\mathbb N$, a pair $(h,x)$ satisfies **Event3** if
--
--   1. there is a set $I\subseteq[n]$ with $|I|=s$ such that $\tilde w_{i,x_i}(h)<\alpha/(4n)$ for all $i\in I$;
--   2. $\Pr[X=x\mid H=h]\ge\alpha$;
--   3. $x$ is correct: $x\in C$ and $h(x)=0$.
--
--   These are the three conditions of Lemma 7.3.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §7.3, definition of Event3, pp.43–44 (PDF pp.45–46); conditions of Lemma 7.3, pp.38–39 (PDF pp.40–41)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm
import Definitions.Def_CertRandQROM_outProb
import Definitions.Def_CertRandQROM_IsCorrect

namespace CertRandQROM

/-- **Event3** (§7.3, pp.43–44 of Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…; the
three conditions of Lemma 7.3, pp.38–39) for a pair `(h, x)`:

1. there is a set `I ⊆ [n]` with `|I| = s` such that `w̃_{i, x_i}(h) < α/(4n)` for all `i ∈ I`;
2. `Pr[X = x | H = h] ≥ α`;
3. `x` is correct: `x ∈ C` and `h(x) = 0`. -/
def Event3 {n : ℕ} {S W : Type} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    {Q : ℕ} (C : Finset (Fin n → S)) (A : QueryAlg (Fin n × S) W (Option (Fin n → S)) Q)
    (α : ℝ) (s : ℕ) (h : Fin n × S → Bool) (x : Fin n → S) : Prop :=
  (∃ I : Finset (Fin n), I.card = s ∧ ∀ i ∈ I, totalQueryNorm A h (i, x i) < α / (4 * n)) ∧
    α ≤ outProb A h (some x) ∧ IsCorrect C h x

end CertRandQROM


