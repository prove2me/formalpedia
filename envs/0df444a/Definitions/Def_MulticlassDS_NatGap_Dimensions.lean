-- Prove2me | Definitions.Def_MulticlassDS_NatGap_Dimensions
-- name    : MulticlassDS_NatGap_Dimensions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:06:44.251905+00:00
-- url     : https://prove2.me/theorems/81f2d479-f6ac-4189-9aea-ce114ee40aef
-- title:
--   Definitions 4–6, pp. 5–6 — projection H|S, N-shattering, Natarajan dimension, pseudo-cube, DS dimension
-- statement:
--   Let $\mathcal X$ be a domain and $\mathcal Y$ a label set, possibly infinite, and let $\mathcal H \subseteq \mathcal Y^{\mathcal X}$ be a concept class. All notions below are defined for **sequences** $S = (x_1,\dots,x_n) \in \mathcal X^n$, with $[n] = \{1,\dots,n\}$.
--
--   1. **Projection.** For $h : \mathcal X \to \mathcal Y$, the projection $h|_S$ is the word $i \mapsto h(x_i)$ in $\mathcal Y^n$, and
--   $$\mathcal H|_S = \{h|_S : h \in \mathcal H\} \subseteq \mathcal Y^n .$$
--   2. **N-shattering and the Natarajan dimension (Definition 4).** $S$ is *N-shattered* by $\mathcal H$ if there are $f, g : [n] \to \mathcal Y$ with $f(i) \neq g(i)$ for every $i$ and
--   $$\mathcal H|_S \supseteq \{f(1), g(1)\} \times \{f(2), g(2)\} \times \cdots \times \{f(n), g(n)\}.$$
--   The Natarajan dimension $d_N(\mathcal H)$ is the maximum length of an N-shattered sequence, and $\infty$ if there are arbitrarily long ones.
--   3. **Pseudo-cube (Definition 5).** A class $B \subseteq \mathcal Y^d$ is a *pseudo-cube of dimension $d$* if it is non-empty, finite, and for every $h \in B$ and every $i \in [d]$ there is an $i$-neighbour $g \in B$ of $h$: $g(i) \neq h(i)$ and $g(j) = h(j)$ for all $j \neq i$.
--   4. **DS-shattering and the DS dimension (Definition 6).** $S \in \mathcal X^n$ is *DS-shattered* by $\mathcal H$ if $\mathcal H|_S$ contains an $n$-dimensional pseudo-cube. The DS dimension $d_{DS}(\mathcal H)$ is the maximum length of a DS-shattered sequence, and $\infty$ if there are arbitrarily long ones.
--
--   For binary labels a pseudo-cube is exactly a Boolean cube, so both dimensions reduce to the VC dimension; for larger label sets every N-shattered sequence is DS-shattered, so $d_N \le d_{DS}$, and the two can differ.
--
--   **Formalization Note** $[n]$ is `Fin n` (0-based). Both dimensions take values in $\mathbb N_\infty$ (`ℕ∞`) as suprema over all shattered sequences: the value is $\top$ exactly when shattered sequences of every length exist, and $0$ for the empty class. A choice of $f(i)$ or $g(i)$ in each coordinate is encoded by a Boolean vector $c$. The finiteness requirement of Definition 5 is kept: without it an infinite tree class would have infinite "DS dimension" (Example 8 of the paper). A sequence with a repeated point can be neither N- nor DS-shattered, so sequences and sets give the same dimensions.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, pp. 5–6, §2.1 Notation, Definitions 4, 5, 6

import Mathlib

namespace MulticlassDS.NatGap

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

end MulticlassDS.NatGap


