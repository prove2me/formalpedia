-- Prove2me | Definitions.Def_FuzzyExtractors_LowerBound_Basic
-- name    : FuzzyExtractors_LowerBound_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:30.799933+00:00
-- url     : https://prove2.me/theorems/0906ed16-dac7-47c0-a85e-59316165cfd7
-- title:
--   Min-entropy, average min-entropy, secure sketches, (𝓜, K, t)-codes, K(𝓜, t, S) and L(𝓜, t, m) (§2.1–§3.1, App. C)
-- statement:
--   Let $\mathcal M$ be a finite set with an integer-valued distance $\mathrm{dis}:\mathcal M\times\mathcal M\to\mathbb N$. Random variables are identified with their laws (probability mass functions); a randomized procedure is a map sending each input to a law on outputs. Logarithms are base 2.
--
--   1. **Min-entropy** (§2.3, p. 8). For a random variable $A$, $\mathbf H_\infty(A) = -\log\big(\max_a \Pr[A=a]\big)$.
--   2. **Average min-entropy** (§2.4, p. 9). For a joint law of $(A,B)$,
--   $$\tilde{\mathbf H}_\infty(A\mid B) = -\log\Big(\mathbb E_{b\leftarrow B}\big[\max_a \Pr[A=a\mid B=b]\big]\Big) = -\log \sum_b \max_a \Pr[A=a \wedge B=b].$$
--   3. **Secure sketch** (Definition 3, p. 11). A pair of randomized procedures $(\mathsf{SS},\mathsf{Rec})$ is an $(\mathcal M,m,\tilde m,t)$-secure sketch if (correctness) whenever $\mathrm{dis}(w,w')\le t$ and $s$ is a possible output of $\mathsf{SS}(w)$, $\mathsf{Rec}(w',s)$ returns $w$ with probability one; and (security) for every distribution $W$ on $\mathcal M$ with $\mathbf H_\infty(W)\ge m$, $\tilde{\mathbf H}_\infty(W\mid \mathsf{SS}(W))\ge \tilde m$.
--   4. **$(\mathcal M,K,t)$-code** (§2.2, p. 8). A set $C\subseteq\mathcal M$ of $K$ codewords such that for every $w\in\mathcal M$ at most one $c\in C$ satisfies $\mathrm{dis}(w,c)\le t$.
--   5. **$K(\mathcal M,t,S)$ and $K(\mathcal M,t)$** (Appendix C, p. 40). For $S\subseteq\mathcal M$, $K(\mathcal M,t,S)$ is the largest $K$ such that some $(\mathcal M,K,t)$-code lies inside $S$; $K(\mathcal M,t)=K(\mathcal M,t,\mathcal M)$.
--   6. **$L(\mathcal M,t,m)$** (Appendix C, p. 40). For $2^m=N$ a natural number with $N\le|\mathcal M|$,
--   $$L(\mathcal M,t,m) = \log\Big(\min_{S\subseteq\mathcal M,\ |S|=2^m} K(\mathcal M,t,S)\Big).$$
--   7. **The set $T$** (proof of Lemma C.1, p. 40). For a sketch $\mathsf{SS}$, a set $S$ and a sketch value $v$, $T$ is the set of $w\in S$ with $\Pr[\mathsf{SS}(w)=v]>0$.
--
--   These are the objects of the coding lower bound for secure sketches (Lemma C.1).
--
--   **Formalization Note** Laws are Mathlib `PMF`s; $\mathsf{Rec}$ is randomized, as Definition 3 allows; average min-entropy is written in the joint form above, which equals the paper's conditional expectation and avoids conditioning on null events. "Min-entropy $m$" is read as $\mathbf H_\infty(W)\ge m$; $m,\tilde m$ are real. The sketch output type is arbitrary (the paper's $\{0,1\}^*$). The metric axioms of §2.1 are not built into the definitions; the code-bound theorems assume them explicitly. $L$ takes $N=2^m$ as a natural number together with a proof that $N\le|\mathcal M|$, because the paper's minimum over sets "of size $2^m$" is only defined in that case; the printed $K(n,t,S)$ inside the minimum is read as $K(\mathcal M,t,S)$. The efficiency clause of Definition 3 is dropped (no complexity theory is formalized).
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §2.1–§2.4 (pp. 7–9), Definition 3 (p. 11), Appendix C (p. 40)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.LowerBound

open scoped ENNReal

noncomputable section

open Classical in
/-- K(𝓜, t, S) (Appendix C, p. 40): the largest `K` such that there is an (𝓜, K, t)-code all of
whose `K` points belong to `S`. The empty code qualifies, so the maximum is attained.
K(𝓜, t), the largest size of an (𝓜, K, t)-code, is `K dis t Finset.univ`. -/
def K {M : Type} (dis : M → M → ℕ) (t : ℕ) (S : Finset M) : ℕ :=
  (S.powerset.filter fun C => FuzzyExtractors.Hamming.IsCode dis C t).sup Finset.card

/-- L(𝓜, t, m) = log(min_{|S| = 2^m} K(𝓜, t, S)) (Appendix C, p. 40), for `2^m = N` a natural
number with `N ≤ |𝓜|`: the minimum ranges over all `N`-element subsets `S` of `𝓜`. -/
def L {M : Type} [Fintype M] (dis : M → M → ℕ) (t N : ℕ)
    (hN : N ≤ Fintype.card M) : ℝ :=
  Real.logb 2 ((Finset.univ.powersetCard N).inf'
    (Finset.powersetCard_nonempty.2 (by simpa using hN))
    fun S => (K dis t S : ℝ))

open Classical in
/-- The set T of points `w ∈ S` that can produce the sketch value `v`, i.e. `Pr[SS(w) = v] > 0`
(Appendix C, proof of Lemma C.1, p. 40). -/
def producers {M V : Type} (SS : M → PMF V) (S : Finset M) (v : V) : Finset M :=
  S.filter fun w => v ∈ (SS w).support

end

end FuzzyExtractors.LowerBound


