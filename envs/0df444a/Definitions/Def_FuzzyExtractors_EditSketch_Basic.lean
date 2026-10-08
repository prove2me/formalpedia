-- Prove2me | Definitions.Def_FuzzyExtractors_EditSketch_Basic
-- name    : FuzzyExtractors_EditSketch_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:30.516501+00:00
-- url     : https://prove2.me/theorems/05f8da48-e56d-4f42-b462-7ba45a13a347
-- title:
--   Average min-entropy, secure sketches, biometric embeddings, PinSketch, the edit metric and shingling (§2–§4.3, §6.3, §7.2, App. E)
-- statement:
--   This module fixes the objects of the edit-distance secure sketch of Dodis, Ostrovsky, Reyzin and Smith. All logarithms are base $2$.
--
--   1. **Entropy.** A random variable is identified with its law. The *min-entropy* of $A$ is $\mathbf H_\infty(A) = -\log \max_a \Pr[A = a]$, and the *average min-entropy* of $A$ given $B$ is
--   $$\tilde{\mathbf H}_\infty(A \mid B) = -\log \sum_b \max_a \Pr[A = a \wedge B = b],$$
--   which equals $-\log \mathbb E_{b \leftarrow B}\big[\max_a \Pr[A = a \mid B = b]\big]$.
--
--   2. **Average-case secure sketch (Definitions 3 and 4).** For a space $\mathcal M$ with an integer distance $\mathrm{dis}$, a pair of randomized procedures $(\mathsf{SS}, \mathsf{Rec})$ is an average-case $(\mathcal M, m, \tilde m, t)$-secure sketch if (correctness) $\mathsf{Rec}(w', s) = w$ with certainty whenever $\mathrm{dis}(w, w') \le t$ and $s$ is a possible output of $\mathsf{SS}(w)$, and (security) for every pair of random variables $(W, I)$ with $\tilde{\mathbf H}_\infty(W \mid I) \ge m$ we have $\tilde{\mathbf H}_\infty(W \mid \mathsf{SS}(W), I) \ge \tilde m$, the coins of $\mathsf{SS}$ being independent of $(W, I)$.
--
--   3. **Biometric embeddings (§4.3).** A map $f : \mathcal M_1 \to \mathcal M_2$ is an *average-case $(t_1, t_2, m_1, m_2)$-biometric embedding* if $\mathrm{dis}_1(w_1, w_1') \le t_1$ implies $\mathrm{dis}_2(f(w_1), f(w_1')) \le t_2$, and $\tilde{\mathbf H}_\infty(W_1 \mid I) \ge m_1$ implies $\tilde{\mathbf H}_\infty(f(W_1) \mid I) \ge m_2$. It is a *$(t_1, t_2, \lambda)$-biometric embedding with recovery information $g$* (Definition 7) if it has the same distance property, $g$ takes at most $2^\lambda$ values, and $w_1$ is uniquely determined by $(f(w_1), g(w_1))$. The sketch of Lemma 4.7 is $\mathsf{SS}'(w) = (\mathsf{SS}(f(w)), g(w))$; its recovery runs $\mathsf{Rec}(f(w'), s)$ and inverts $(y, r)$ to the unique $w$ with $(f(w), g(w)) = (y, r)$.
--
--   4. **Set difference and PinSketch (§6.3, Appendix E).** Let $K$ be a finite field of characteristic $2$ (so $K = GF(2^\mu)$ and the universe $\mathcal U = K^*$ has $n = 2^\mu - 1$ elements). A binary word is identified with its support $w \subseteq K^*$, and $\mathrm{dis}(w, w') = |w \triangle w'|$. The *syndrome* entries are the power sums $s_i(w) = \sum_{x \in w} x^i$. PinSketch outputs $\mathsf{SS}(w) = (s_1, s_3, \dots, s_{2t-1})$; $\mathsf{Rec}(w', s)$ forms $\sigma_i = s_i(w') - s_i$ and, if some $v$ with $|v| \le t$ has odd syndromes $(\sigma_1, \sigma_3, \dots, \sigma_{2t-1})$, outputs $w' \triangle v$ for such a $v$. For $M \subseteq K^*$ the *error locator* and *error evaluator* polynomials are
--   $$\sigma_M(z) = \prod_{x \in M} (1 - xz), \qquad \omega_M(z) = \sum_{x \in M} xz \prod_{y \in M,\, y \ne x} (1 - yz),$$
--   and the *syndrome polynomial* of designed distance $\delta$ is $S(z) = \sum_{\ell = 1}^{\delta - 1} s_\ell(M) z^\ell$.
--
--   5. **Edit metric and shingling (§2.1, §7).** $\mathrm{Edit}_{\mathcal F}(n)$ is the set of strings of length $n$ over a finite alphabet $\mathcal F$, with distance the smallest number of character insertions and deletions turning one string into the other. A *$c$-shingle* of $w$ is a length-$c$ consecutive substring; the *$c$-shingling* $\mathrm{SH}_c(w) \subseteq \mathcal F^c$ is the set of all of them. The recovery information $g_c(w) = (p_1, \dots, p_{\lceil n/c \rceil})$ cuts $w$ into $\lceil n/c \rceil$ blocks of length $c$ (the last two may overlap) and records, for each block, its index in $\mathrm{SH}_c(w)$ sorted lexicographically.
--
--   These objects are the vocabulary of every statement in the mission: PinSketch is the set-difference sketch, shingling with $g_c$ is the embedding of the edit metric into set difference, and Lemma 4.7 composes the two.
--
--   **Formalization Note.** Laws are `PMF`s and randomized procedures are kernels `M → PMF S`. Average min-entropy is written in the joint form above, which avoids conditioning on null events; the auxiliary variable ranges over every `ι : Type`, which contains the paper's $\{0,1\}^*$. "Min-entropy $m$" is read as $\ge m$. The paper's field $GF(2^m)$ is any finite field `K` of characteristic $2$ (the field degree is renamed $\mu$ because $m$ is the min-entropy); Appendix E's large field $\mathcal F$ is this `K`, distinct from §7's alphabet $\mathcal F$. The q-ary words of Appendix E are specialised to $q = 2$, so a word is a `Finset Kˣ`. $\omega$ is the paper's $\sigma(z) \sum_{x \in M} xz/(1 - xz)$ written without division. The edit distance is the published weighted edit distance `MasekPaterson.Shared.editDist` with cost $1$ per insertion or deletion and $2$ per replacement (a replacement equals a deletion plus an insertion), so its value is the insertion/deletion count, a natural number; `editDis` takes its floor to obtain the `ℕ` type. Intermediate strings of an edit sequence may have any length. `shingles` is defined for strings of every length (empty for length $< c$). `gc` uses 0-based block and rank indices and needs `[LinearOrder 𝓕]` (the lexicographic order of $\mathcal F^c$ is `Pi.Lex`) and `[Inhabited 𝓕]` (for an out-of-range read that does not occur when $c \le n$). In `pinRec`, if no $v$ exists, $w'$ is returned; the paper leaves this case unspecified. The PinSketch syndrome type is `Fin t → K`. Efficiency ("efficient procedures") is not formalized.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §2.1 (p. 7), §2.3–2.4 (pp. 8–9), Definitions 3–4 (p. 11), Definitions 6–7 (p. 15), §6.3 and Construction 6 (pp. 22–23), §7 intro and §7.2 (pp. 23, 25), Definition 8 and Appendix E (pp. 42–43)

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_FuzzyExtractors_Hamming_Basic

open scoped ENNReal

noncomputable section

namespace FuzzyExtractors.EditSketch

open Polynomial

/-! ### Shared model (§2.3–§3.1) -/

/-! ### Biometric embeddings (§4.3, p. 15) -/

/-- An average-case (t₁, t₂, m₁, m₂)-biometric embedding (Definition 6 and the average-case
variant on p. 15): distance at most `t₁` is mapped to distance at most `t₂`, and
H̃∞(W₁ | I) ≥ m₁ implies H̃∞(f(W₁) | I) ≥ m₂ for every auxiliary variable `I`. -/
def IsAvgBiometricEmbedding {M₁ M₂ : Type} (dis₁ : M₁ → M₁ → ℕ) (dis₂ : M₂ → M₂ → ℕ)
    (t₁ t₂ : ℕ) (m₁ m₂ : ℝ) (f : M₁ → M₂) : Prop :=
  (∀ w w', dis₁ w w' ≤ t₁ → dis₂ (f w) (f w') ≤ t₂) ∧
    ∀ (ι : Type) (WI : PMF (M₁ × ι)), m₁ ≤ FuzzyExtractors.Hamming.avgMinEntropy WI →
      m₂ ≤ FuzzyExtractors.Hamming.avgMinEntropy (WI.map (Prod.map f id))

/-- A (t₁, t₂, λ)-biometric embedding with recovery information `g` (Definition 7):
distance at most `t₁` is mapped to distance at most `t₂`, `g` takes at most `2 ^ λ` values,
and `w` is uniquely determined by `(f w, g w)`. -/
def IsEmbeddingWithRecovery {M₁ M₂ G : Type} (dis₁ : M₁ → M₁ → ℕ) (dis₂ : M₂ → M₂ → ℕ)
    (t₁ t₂ : ℕ) (lam : ℝ) (f : M₁ → M₂) (g : M₁ → G) : Prop :=
  (∀ w w', dis₁ w w' ≤ t₁ → dis₂ (f w) (f w') ≤ t₂) ∧
    (∃ T : Finset G, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ w, g w ∈ T) ∧
    Function.Injective fun w => (f w, g w)

/-- The sketch of Lemma 4.7: `SS'(w) = (SS(f(w)), g(w))`. -/
def embedSketch {M₁ M₂ G S : Type} (f : M₁ → M₂) (g : M₁ → G) (SS : M₂ → PMF S) :
    M₁ → PMF (S × G) :=
  fun w => (SS (f w)).map fun s => (s, g w)

/-- The recovery of Lemma 4.7: run `Rec(f(w'), s)` to get a point `y` of `M₂`, then invert
`(y, r)` to the `w` with `f w = y` and `g w = r` (unique when `(f, g)` is injective). If no
such `w` exists, return `w'`. -/
def embedRec {M₁ M₂ G S : Type} (f : M₁ → M₂) (g : M₁ → G) (Rec : M₂ → S → PMF M₂) :
    M₁ → S × G → PMF M₁ :=
  fun w' sr => (Rec (f w') sr.1).map fun y => by
    classical
    exact if h : ∃ w, f w = y ∧ g w = sr.2 then Classical.choose h else w'

/-! ### Set difference and PinSketch (§6.3, pp. 22–23; Appendix E, pp. 42–44) -/

/-- The set-difference distance on subsets of a universe: `dis(w, w') = |w △ w'|` (§6). -/
def symmDiffDis {U : Type} [DecidableEq U] (w w' : Finset U) : ℕ :=
  (symmDiff w w').card

/-- The power-sum syndrome `p(α^i) = Σ_{x ∈ w} x^i` of the binary word with support `w`
(Appendix E, p. 43; Construction 6, step 1), computed in the field `K`. -/
def syn {K : Type} [Field K] (i : ℕ) (w : Finset Kˣ) : K :=
  ∑ x ∈ w, (x : K) ^ i

/-- PinSketch, sketching (Construction 6): `SS(w) = (s₁, s₃, …, s_{2t−1})`, entry `j` being
the syndrome `s_{2j+1}`. -/
def pinSS {K : Type} [Field K] (t : ℕ) (w : Finset Kˣ) : PMF (Fin t → K) :=
  PMF.pure fun j => syn (2 * (j : ℕ) + 1) w

/-- PinSketch, recovery (Construction 6): compute `σ_i = s'_i − s_i` for the odd `i`; if
some `v` with `|v| ≤ t` has these odd syndromes, choose one and output `w' △ v`;
otherwise output `w'`. -/
def pinRec {K : Type} [Field K] [DecidableEq K] (t : ℕ) (w' : Finset Kˣ) (s : Fin t → K) :
    PMF (Finset Kˣ) := by
  classical
  exact if h : ∃ v : Finset Kˣ, v.card ≤ t ∧
      ∀ j : Fin t, syn (2 * (j : ℕ) + 1) v = syn (2 * (j : ℕ) + 1) w' - s j then
    PMF.pure (symmDiff w' (Classical.choose h))
  else PMF.pure w'

/-- The error-locator polynomial `σ(z) = ∏_{x ∈ M} (1 − xz)` (Appendix E, p. 43). -/
def sigma {K : Type} [Field K] (M : Finset Kˣ) : K[X] :=
  ∏ x ∈ M, (1 - C (x : K) * X)

/-- The error-evaluator polynomial of a binary word with support `M` (Appendix E, p. 43):
`ω(z) = σ(z) Σ_{x ∈ M} xz/(1 − xz)`, written without division as
`Σ_{x ∈ M} xz ∏_{y ∈ M, y ≠ x} (1 − yz)`. -/
def omega {K : Type} [Field K] [DecidableEq K] (M : Finset Kˣ) : K[X] :=
  ∑ x ∈ M, C (x : K) * X * ∏ y ∈ M.erase x, (1 - C (y : K) * X)

/-- The syndrome polynomial `S(z) = Σ_{ℓ=1}^{δ−1} p(α^ℓ) z^ℓ` (Appendix E, p. 43). -/
def synPoly {K : Type} [Field K] (δ : ℕ) (M : Finset Kˣ) : K[X] :=
  ∑ l ∈ Finset.Icc 1 (δ - 1), C (syn l M) * X ^ l

/-! ### The edit metric and shingling (§2.1, p. 7; §7, pp. 23–26) -/

/-- The space `Edit_𝓕(n)` of strings of length `n` over the alphabet `𝓕`. -/
abbrev EditSpace (𝓕 : Type) (n : ℕ) : Type := {w : List 𝓕 // w.length = n}

/-- The insertion/deletion cost function for `MasekPaterson.Shared.editDist`: an insertion
or a deletion costs 1, a replacement (including `a → a`) costs 2, the cost of a deletion
followed by an insertion. -/
def gammaIndel {𝓕 : Type} (o : MasekPaterson.Shared.EditOp 𝓕) : ℝ :=
  if o.src.isSome ∧ o.tgt.isSome then 2 else 1

/-- The edit distance of §2.1 (p. 7): the smallest number of character insertions and
deletions transforming `w` into `w'`. It is the weighted edit distance `δ(γ, w, w')` for the
cost function `gammaIndel`, whose values are natural numbers; the floor converts the type. -/
def editDis {𝓕 : Type} {n : ℕ} (w w' : EditSpace 𝓕 n) : ℕ :=
  ⌊MasekPaterson.Shared.editDist gammaIndel w.1 w'.1⌋₊

/-- The c-shingling `SH_c(w)` of a string (§7.2, p. 25): the set of all length-`c`
consecutive substrings of `w`. A word `u : Fin c → 𝓕` is a shingle of `w` iff
`u = (w_i, w_{i+1}, …, w_{i+c−1})` for some position `i`. Defined for strings of any length
(empty when the length is less than `c ≥ 1`). -/
def shingles {𝓕 : Type} [Fintype 𝓕] (c : ℕ) (w : List 𝓕) : Finset (Fin c → 𝓕) := by
  classical
  exact Finset.univ.filter fun u => ∃ i : ℕ, ∀ k : Fin c, w[i + (k : ℕ)]? = some (u k)

/-- The length-`c` substring of `w` starting at position `i` (entries past the end of `w`
read `default`; this never happens in `gc` below when `c ≤ n`). -/
def shingleAt {𝓕 : Type} [Inhabited 𝓕] (c : ℕ) (w : List 𝓕) (i : ℕ) : Fin c → 𝓕 :=
  fun k => w.getD (i + (k : ℕ)) default

/-- The recovery information `g_c(w) = (p_1, …, p_{⌈n/c⌉})` of §7.2 (p. 25), 0-based: the
string is cut into `⌈n/c⌉` blocks of length `c`, block `j` starting at position
`min (j c) (n − c)` (the last two blocks may overlap), and `p_j` is the index of block `j`
in the lexicographically sorted shingle set `SH_c(w)`, i.e. the number of shingles of `w`
lexicographically smaller than block `j`. -/
def gc {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕] (c : ℕ) {n : ℕ}
    (w : EditSpace 𝓕 n) : Fin ⌈(n : ℝ) / c⌉₊ → ℕ := by
  classical
  exact fun j => ((shingles c w.1).filter fun u =>
    toLex u < toLex (shingleAt c w.1 (min ((j : ℕ) * c) (n - c)))).card

end FuzzyExtractors.EditSketch


