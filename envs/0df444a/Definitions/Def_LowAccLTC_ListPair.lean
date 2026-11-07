-- Prove2me | Definitions.Def_LowAccLTC_ListPair
-- name    : LowAccLTC_ListPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:35.089622+00:00
-- url     : https://prove2.me/theorems/dca7866c-6dd1-413e-b5d8-0b00478ec7c4
-- title:
--   Edges of the containment complex $\mathcal C^jX$ and the list properties of Lemma 4.3
-- statement:
--   For sizes $a<b$, an edge $s\subset t$ of the containment complex $\mathcal C^jX$ between $X\langle a\rangle$ and $X\langle b\rangle$ is sampled by sampling a top face, then a uniformly random nested pair of colour sets $I\subseteq J$ with $|I|=a$, $|J|=b$. For lists $L(\cdot)$ of local codewords, a word $f$ and $\varepsilon>0$, the pair $(s,t)$ is **good** if
--
--   1. $L(s)$ and $L(t)$ are nonempty and contain at most $6/\varepsilon$ codewords;
--   2. every codeword of $L(s)$ is $(1-\varepsilon/3)$-close to $f|_s$ and every codeword of $L(t)$ is $(1-\varepsilon/3)$-close to $f|_t$;
--   3. the restriction map $\mathrm{Res}_{s,t}:L(s)\to L(t)$, $c\mapsto c|_t$, is a bijection.
--
--   These are the three properties of Lemma 4.3.
--
--   **Formalization Note** A list is a finite set of words on all top faces; restriction to $t$ is agreement on $\mathrm{star}(t)$.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.15 p.17 (PDF p.20), Lemma 4.3 p.30 (PDF p.33)

import Definitions.Def_LowAccLTC_TannerCode

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

/-- Ordered pairs `(I, J)` of colour sets with `I ⊆ J`, `|I| = a`, `|J| = b`. Sampling a top face
`t ∼ μ` and a uniform element of `nestedPairs r a b` is the law of an edge `s ⊂ t'` of the
containment complex `C^j X` between `X⟨a⟩` and `X⟨b⟩` (Definition 2.15, p.17: sample a
`3j`-face, then a uniform nested pair inside it). -/
noncomputable def nestedPairs (r a b : ℕ) : Finset (Finset (Fin r) × Finset (Fin r)) :=
  ((Finset.univ : Finset (Fin r)).powersetCard a ×ˢ (Finset.univ : Finset (Fin r)).powersetCard b).filter
    fun P => P.1 ⊆ P.2

namespace PartiteComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- The three properties of Lemma 4.3 (p.30) for an edge `s ⊂ t` of `C^j X` and lists `L`:
1. `L(s)` and `L(t)` are nonempty and contain at most `6/ε` codewords;
2. every codeword of `L(s)` (resp. `L(t)`) is `(1 - ε/3)`-close to `f|_s` (resp. `f|_t`);
3. the restriction map `Res_{s,t} : L(s) → L(t)`, `c ↦ c|_t`, is a bijection.

**Formalization Note.** A list is a finite set of words on all top faces, representing local
codewords by their values on the star (`Lemma 4.3` requires the representatives of distinct
codewords of `L(s)` to differ on `star(s)`); restriction to `t` is agreement on `star(t)`. -/
def IsGoodListPair (f : T → A) (ε : ℝ) (L : Finset V → Finset (T → A)) (s t : Finset V) : Prop :=
  (L s).Nonempty ∧ (L t).Nonempty ∧ ((L s).card : ℝ) ≤ 6 / ε ∧ ((L t).card : ℝ) ≤ 6 / ε ∧
  (∀ c ∈ L s, X.wdist (X.star s) c f ≤ 1 - ε / 3) ∧ (∀ c ∈ L t, X.wdist (X.star t) c f ≤ 1 - ε / 3) ∧
  (∀ c ∈ L s, ∃ c' ∈ L t, ∀ x ∈ X.star t, c x = c' x) ∧
  (∀ c' ∈ L t, ∃ c ∈ L s, ∀ x ∈ X.star t, c x = c' x) ∧
  (∀ c₁ ∈ L s, ∀ c₂ ∈ L s, (∀ x ∈ X.star t, c₁ x = c₂ x) → c₁ = c₂)

end PartiteComplex

end LowAccLTC


