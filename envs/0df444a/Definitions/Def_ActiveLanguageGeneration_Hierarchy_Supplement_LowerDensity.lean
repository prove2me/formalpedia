-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_LowerDensity
-- name    : ActiveLanguageGeneration_Hierarchy_Supplement_LowerDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:21:41.402147+00:00
-- url     : https://prove2.me/theorems/a41600e7-f3d3-4439-a740-416e6ca10ef4
-- title:
--   Lower density and active generation with lower density
-- statement:
--   Let $U$ carry a global ordering $\prec$ of order type $\omega$, let $K\subseteq U$ be infinite with elements $\ell_1\prec\ell_2\prec\cdots$, and let $S\subseteq U$. The **lower density** of $S$ in $K$ is
--
--   $$
--   \mu_{\mathrm{low}}(S,K)=\liminf_{n\to\infty}\frac{|S\cap\{\ell_1,\ldots,\ell_n\}|}{n}.
--   $$
--
--   For a generator $G$ and an enumeration $E=(x_t)$, let $O(E,G)=\{G(x_1,\ldots,x_t):t\ge1\}$ be the set of everything $G$ ever outputs, incorrect outputs included. For $\alpha\in[0,1]$:
--
--   1. $C$ is **actively generatable in the limit with lower density $\alpha$** if one generator $G$ has, for every $K\in C$, a single full repetition-free enumeration $E$ of $K$ on which $G$ is eventually correct (with repetition) and $\mu_{\mathrm{low}}(O(E,G),K)\ge\alpha$.
--   2. For a positive integer $k$, $C$ is **actively $k$-generatable with lower density $\alpha$** if one generator $G$ has, for every $K\in C$, a single such enumeration on which $G$ is correct at every time $t\ge k$ and $\mu_{\mathrm{low}}(O(E,G),K)\ge\alpha$.
--
--   These notions measure the breadth of active generation (Appendix D).
--
--   **Formalization Note** "$\mu_{\mathrm{low}}\ge\alpha$" is encoded as: for every $\varepsilon>0$, eventually $|S\cap\{\ell_1,\ldots,\ell_n\}|/n\ge\alpha-\varepsilon$, which is equivalent for this bounded sequence and has no default-value artefact. The listing $\ell$ is the neutral enumeration of $K$. Item 2 is the notion Theorem D.3 uses (Definition 2.2 plus item 2 of Definition D.1, one enumeration); the paper does not define it separately.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, §D.1 and Definition D.1 (with Theorem D.3), printed p.35–37 (PDF p.36–38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

open scoped Classical in
/-- §D.1, printed p.35 (PDF p.36): the lower density of `S` in the language `K` is at least
`α`, i.e. `liminf_{n→∞} |S ∩ {ℓ₁, …, ℓₙ}| / n ≥ α`, where `ℓ₁ ≺ ℓ₂ ≺ ⋯` lists `K` in the global
order. The liminf of this `[0,1]`-valued sequence is `≥ α` iff for every `ε > 0` the ratio is
eventually `≥ α − ε`; this form has no junk value. The ordered listing of `K` is its neutral
enumeration (unique on an ω-ordered universe). -/
def LowerDensityAtLeast {U : Type} [LinearOrder U] (S : Set U) (K : Language U) (α : ℝ) :
    Prop :=
  ∀ e : ℕ → U, NeutralEnumeration K e → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      α - ε ≤ (((Finset.range n).filter (fun i => e i ∈ S)).card : ℝ) / (n : ℝ)

/-- Definition D.1, printed p.35 (PDF p.36): one generator such that every target `K ∈ C` has
a single full injective enumeration on which it is eventually correct (with repetition) and the
set of all strings it ever outputs (incorrect early outputs included) has lower density at
least `α` in `K`. -/
def ActiveLimitGeneratableWithDensity {U : Type} [LinearOrder U]
    (C : LanguageCollection U) (α : ℝ) : Prop :=
  ∃ G : Generator U, ∀ K ∈ C, ∃ x : ℕ → U, IsEnumeration K x ∧
    (∃ tStar : ℕ, 0 < tStar ∧ ∀ n : ℕ, tStar ≤ n + 1 → CorrectAt .R G K x n) ∧
    LowerDensityAtLeast (Set.range (outputAt G x)) K α

/-- The notion of Theorem D.3, printed p.37 (PDF p.38): Definition 2.2 (with repetition) and
item 2 of Definition D.1 on one and the same enumeration — correct at every time `t ≥ k`, and
the set of all outputs has lower density at least `α` in the target. -/
def ActiveKGeneratableWithDensity {U : Type} [LinearOrder U]
    (C : LanguageCollection U) (k : ℕ) (α : ℝ) : Prop :=
  0 < k ∧ ∃ G : Generator U, ∀ K ∈ C, ∃ x : ℕ → U, IsEnumeration K x ∧
    (∀ n : ℕ, k ≤ n + 1 → CorrectAt .R G K x n) ∧
    LowerDensityAtLeast (Set.range (outputAt G x)) K α

end ActiveLanguageGeneration.Hierarchy.Supplement


