-- Prove2me | Definitions.Def_MulticlassDS_Compress_Dimensions
-- name    : MulticlassDS_Compress_Dimensions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:44:24.777697+00:00
-- url     : https://prove2.me/theorems/fb65dcdc-3485-48aa-835b-2d5ce3789468
-- title:
--   Definitions 4–6, pp. 5–6 — projection H|S, N-shattering, Natarajan dimension, pseudo-cube, DS dimension
-- statement:
--   Let $\mathcal X$ be a domain and $\mathcal Y$ a label set, possibly infinite, and let $\mathcal H \subseteq \mathcal Y^{\mathcal X}$ be a concept class. For a sequence $S = (x_1,\dots,x_n) \in \mathcal X^n$, the **projection** of $\mathcal H$ to $S$ is the set of words
--   $$\mathcal H|_S = \{(h(x_1),\dots,h(x_n)) : h \in \mathcal H\} \subseteq \mathcal Y^n .$$
--
--   1. **N-shattering and the Natarajan dimension** (Definition 4). $S$ is *N-shattered* by $\mathcal H$ if there are $f, g : [n] \to \mathcal Y$ with $f(i) \neq g(i)$ for every $i$ such that $\mathcal H|_S$ contains every word $w$ with $w(i) \in \{f(i), g(i)\}$ for all $i$. The **Natarajan dimension** $d_N(\mathcal H)$ is the maximum length of an N-shattered sequence, and $\infty$ if there are arbitrarily long ones.
--   2. **Pseudo-cubes** (Definition 5). A set $B \subseteq \mathcal Y^d$ is a *pseudo-cube of dimension $d$* if it is non-empty and finite and every $h \in B$ has, for every direction $i \in [d]$, an *$i$-neighbour* $g \in B$: $g(i) \neq h(i)$ and $g(j) = h(j)$ for all $j \neq i$.
--   3. **DS-shattering and the DS dimension** (Definition 6). $S \in \mathcal X^n$ is *DS-shattered* by $\mathcal H$ if $\mathcal H|_S$ contains an $n$-dimensional pseudo-cube. The **DS dimension** $d_{DS}(\mathcal H)$ is the maximum length of a DS-shattered sequence, and $\infty$ if there are arbitrarily long ones.
--
--   A Boolean cube $\prod_i\{f(i),g(i)\}$ is a pseudo-cube, so $d_N(\mathcal H) \le d_{DS}(\mathcal H)$. The DS dimension is the parameter that characterizes multiclass PAC learnability; the Natarajan dimension controls learnability only when the label set is finite.
--
--   **Formalization Note** Sequences of length $n$ are functions `Fin n → X`, so $[n]$ is $\{0,\dots,n-1\}$. Both dimensions take values in `ℕ∞` and are suprema over all lengths of shattered sequences: an unbounded family gives `⊤` (the paper's $\infty$), and the empty class gives $0$; for a non-empty class the empty sequence is shattered. Finiteness of a pseudo-cube is part of the definition, as on the page (Example 8 shows it cannot be dropped). The paper works with sequences rather than sets; a sequence with a repeated point is never shattered, so the dimensions agree with the set-based ones.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, pp. 5–6, §2.1 Notation, Definitions 4, 5, 6

import Mathlib

namespace MulticlassDS.Compress

/-- §2.1, p. 5: the projection `H|_S = {h|_S : h ∈ H} ⊆ Yⁿ` of `H` to the sequence
`S = (x₁, …, xₙ)`, with `h|_S` the word `i ↦ h(xᵢ)`. -/
def proj {X Y : Type*} {n : ℕ} (H : Set (X → Y)) (S : Fin n → X) : Set (Fin n → Y) :=
  (fun h => h ∘ S) '' H

/-- Definition 4, p. 5: `S` is N-shattered by `H` if there are `f, g : [n] → Y` with `f(i) ≠ g(i)` for
every `i` and `H|_S ⊇ {f(1), g(1)} × ⋯ × {f(n), g(n)}`. -/
def NShatters {X Y : Type*} {n : ℕ} (H : Set (X → Y)) (S : Fin n → X) : Prop :=
  ∃ f g : Fin n → Y, (∀ i, f i ≠ g i) ∧
    ∀ c : Fin n → Bool, (fun i => if c i then f i else g i) ∈ proj H S

/-- Definition 4, p. 5: the Natarajan dimension, the maximum size of an N-shattered sequence
(`⊤` if there are arbitrarily long ones). -/
noncomputable def natarajanDim {X Y : Type*} (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (n : ℕ) (S : Fin n → X) (_ : NShatters H S), (n : ℕ∞)

/-- Definition 5, p. 5: `B ⊆ Y^d` is a pseudo-cube of dimension `d` if it is non-empty, finite, and
every `h ∈ B` has an `i`-neighbour `g ∈ B` (`g(i) ≠ h(i)`, `g(j) = h(j)` for `j ≠ i`) for every `i`. -/
def IsPseudoCube {Y : Type*} {d : ℕ} (B : Set (Fin d → Y)) : Prop :=
  B.Nonempty ∧ B.Finite ∧
    ∀ h ∈ B, ∀ i : Fin d, ∃ g ∈ B, g i ≠ h i ∧ ∀ j, j ≠ i → g j = h j

/-- Definition 6, p. 6: `S ∈ Xⁿ` is DS-shattered by `H` if `H|_S` contains an `n`-dimensional
pseudo-cube. -/
def DSShatters {X Y : Type*} {n : ℕ} (H : Set (X → Y)) (S : Fin n → X) : Prop :=
  ∃ B ⊆ proj H S, IsPseudoCube B

/-- Definition 6, p. 6: the DS dimension, the maximum size of a DS-shattered sequence. -/
noncomputable def dsDim {X Y : Type*} (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (n : ℕ) (S : Fin n → X) (_ : DSShatters H S), (n : ℕ∞)

end MulticlassDS.Compress


