-- Prove2me | Definitions.Def_MooreFoelner
-- name    : MooreFoelner
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-01T22:41:11.909306+00:00
-- url     : https://prove2.me/theorems/87bb461f-e183-4c01-b1dc-fbec2b8357e9
-- title:
--   Moore §3: partial actions, weighted Følner sets and marginal sets
-- statement:
--   Notions of Moore's §3 (pp. 5–9) and p. 1, for a group $G$ acting partially on a set $S$ on the right.
--
--   **Partial actions (Definition 3.1).** p. 5: “A partial action of $G$ on a set $S$ is a partial function $\cdot : S \times G \to S$ such that: $x \cdot e = x$ for all $x \in S$; $x \cdot g = y$ if and only if $x = y \cdot g^{-1}$ for all $g \in G$ and $x, y \in S$; $x \cdot (gh) = (x \cdot g) \cdot h$ for all $g, h \in G$ and all $x \in S$ for which all computations involving $\cdot$ are defined.” `IsPartialAction act` is a partial function $S \times G \to S$, written `act x g = some y` for $x \cdot g = y$, with the first two conditions as quoted and the third read as: whenever $x \cdot g$ and $(x \cdot g) \cdot h$ are defined, $x \cdot (gh)$ is defined and equals $(x \cdot g) \cdot h$ (see the first Formalization Note).
--
--   **Weighted Følner sets (Definition 3.3).** p. 5: “A weighted $\varepsilon$-Følner set with respect to $\Gamma$ is a function $\mu$ from a finite subset of $S$ into $(0, \infty)$ which satisfies $\sum_{\gamma \in \Gamma} \sum_{s \in S} |\mu(s \cdot \gamma) - \mu(s)| < \varepsilon \sum_{s \in S} \mu(s)$ where we adopt with the conventions that $\mu(s) = 0$ if $s$ is not in the domain of $\mu$ and $\mu(s \cdot g) = 0$ if $s \cdot g$ is undefined.” Here $\mu \colon S \to \mathbf R$ is finitely supported with non-negative values (its support is the finite set where it is positive), and `IsWeightedFolner act Γ μ ε` is that inequality, where $\mu(s \cdot g)$ (`valAt`) is $0$ when $s \cdot g$ is undefined. p. 5: “The function $\mu$ induces a finitely supported measure on $S$, also denoted $\mu$, defined by $\mu(A) = \sum_{s \in A} \mu(s)$.” `mass μ A` is this $\mu(A)$. p. 5: “I will use $\mu \restriction A$ to denote $\mu \cdot 1_A$.” `restrict μ A` is $\mu \restriction A$. p. 5: “If $E \subseteq S$ and $g$ is in $G$, I will write $E \cdot g$ to denote $\{x \cdot g : x \in E\}$.” `image act E g` is $E \cdot g$.
--
--   **Word length.** p. 6: “If $g$ is in $G$, let $d_g$ be the minimum length of a word in $\Gamma$ which evaluates to $g$.” `wordLength Γ g` is $d_g$.
--
--   **Marginal sets (Definitions 3.6, 3.7).** p. 7: “If $g \in G$, $I \subseteq S$, and $E \subseteq S$, then $g$ marginalizes $E$ off $I$ if for every $x \in E$ if $x \cdot g^k \in E$ and $k > 0$, then there is an $i < k$ such that $x \cdot g^i$ is in $I$ or is undefined. If $I$ is the emptyset, then I will write $g$ marginalizes $E$.” `Marginalizes act g E I` is this condition. p. 7: “The $k$-marginal sets for the partial action of $G$ on $S$ are defined recursively as follows. The emptyset is $0$-marginal. If there is a decomposition $E = \bigcup_{i<l} E_i \subseteq S$ and for each $i < l$, there is a $g_i \in G$ and a $k$-marginal set $I_i$ such that $g_i$ marginalizes $E_i$ off $I_i$, then $E$ is $(k + 1)$-marginal. $E \subseteq S$ is marginal if it is $k$-marginal for some $k < \infty$.” `IsKMarginal` is this recursion, and `IsMarginal` means $k$-marginal for some $k$.
--
--   **$\Gamma$-connected sets (Definition 3.13).** p. 9: “A subset $A \subseteq G$ is $\Gamma$-connected if whenever $x$ and $y$ are in $A$, there are $\gamma_i$ ($i < l$) in $\Gamma$ such that, setting $x_0 = x$ and $x_{i+1} = x_i \cdot \gamma_i$, then $x_i$ is defined for each $i \le l$ and $y = x_l$.” `IsConnected act Γ A`: any two points of $A$ are joined by such a chain $x_{i+1} = x_i \cdot \gamma_i$, $\gamma_i \in \Gamma$, all defined and all in $A$ (see the second Formalization Note). p. 9: “A maximal $\Gamma$-connected subset of a given $B \subseteq G$ is said to be a $\Gamma$-connected component of $B$.” `IsConnectedComponent act Γ A B` says $A$ is a maximal $\Gamma$-connected subset of $B$. The definition is quoted for subsets $A \subseteq G$; `IsConnected` takes subsets of the set $S$ a partial action acts on, the generality in which the paper applies it.
--
--   **Følner sets and the Følner function (p. 1).** p. 1: “Recall that a finite subset $A$ of a finitely generated group $G$ is $\varepsilon$-Følner (with respect to a finite generating set $\Gamma \subseteq G$) if $\sum_{\gamma \in \Gamma} |(A \cdot \gamma) \mathbin{\triangle} A| < \varepsilon |A|$ where $\triangle$ denotes symmetric difference.” For the right action of $G$ on itself (`rightMul`; the source names this action in Lemma 3.15, p. 9, without a defining sentence), `IsFolnerSet Γ A ε` says that the finite set $A \subseteq G$ satisfies this inequality. p. 1: “The Følner function of $G$ (with respect to $\Gamma$) is defined by $\mathrm{Føl}_{G,\Gamma}(n) = \min\{|A| : A \subseteq G \text{ is } \frac{1}{n}\text{-Følner w.r.t. } \Gamma\}$ with $\mathrm{Føl}_{G,\Gamma}(n) = \infty$ if there is no $1/n$-Følner set with respect to $\Gamma$.” `folnerFunction Γ n` is $\mathrm{Føl}_{G,\Gamma}(n)$, the least $|A|$ over $1/n$-Følner sets $A$, and $\infty$ if there is none. `indicator A` is the characteristic function $1_A$, which the source uses on p. 5 without a defining sentence. The quote's “finitely generated” and “finite generating set” are not part of `IsFolnerSet`, which accepts any finite $\Gamma \subseteq G$; the statements that use it supply a finite generating set.
--
--   **Formalization Note (Definition 3.1).** Moore's third axiom reads "$x \cdot (gh) = (x \cdot g) \cdot h$ for all $g, h \in G$ and all $x \in S$ for which all computations involving $\cdot$ are defined" (p. 5), and "all computations" can be read two ways. On the reading taken here the equation asserts its left side: whenever $x \cdot g$ and $(x \cdot g) \cdot h$ are defined, $x \cdot (gh)$ is defined and equals $(x \cdot g) \cdot h$. This is the composition law of partial actions in the sense of R. Exel, *Partial actions of groups and actions of inverse semigroups*, Proc. Amer. Math. Soc. 126 (1998) 3481–3494 ([doi:10.1090/S0002-9939-98-04575-4](https://doi.org/10.1090/S0002-9939-98-04575-4)), Definition 1.2 and the remark after it (stated there for left actions), and Moore's proof of Lemma 3.5 uses it in the step on p. 6 where $s \cdot g_{i+1}$ is defined but $s \cdot g_i$ is not, which needs $(s \cdot g_{i+1}) \cdot \gamma_i^{-1}$ to be undefined as well. On the weaker reading the equation is required only where $x \cdot (gh)$ is defined as well, and Lemmas 3.5, 3.9, 3.10 and 3.12 fail, each already for a partial action of $\mathbf Z$ on $\mathbf Z$: see the p2m theorems for [Lemma 3.5](https://prove2.me/theorems/4c2eb548-bd94-47ad-8576-ccf07688e521), [Lemma 3.9](https://prove2.me/theorems/959236bc-0a39-4114-9639-dd4883fa2c31), [Lemma 3.10](https://prove2.me/theorems/297b1132-0197-4ea3-b8fe-307010df4a81) and [Lemma 3.12](https://prove2.me/theorems/aac1c973-3129-4533-8270-cbf4f34d3b45). The action of a group on itself by right multiplication satisfies the law, and so does the action of $F$ on trees (the §2 milestone on the tree action states it).
--
--   **Formalization Note (Definition 3.13).** Moore's Definition 3.13 does not say that the chain joining two points of $A$ stays in $A$; read that way, for a symmetric generating set $\Gamma$ every subset of a group acting on itself by right multiplication would be $\Gamma$-connected ([p2m theorem](https://prove2.me/theorems/1d02b3af-bd3a-4205-93ae-34d9b36e472b)), so the connectedness in Lemma 3.15 would say nothing, and the last step of the proof of Theorem 1.1 would fail: "Since $A'$ is $\Gamma$-connected, it must contain at least $\exp_n(0)$ elements" (p. 19) counts the points of a chain inside $A'$ from the identity to an element at distance at least $\exp_n(0)$. The definition here requires the chain to stay in $A$, which is the reading the proofs use.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), pp. 1–9, §3 (Definitions 3.1, 3.3, 3.6, 3.7, 3.13) and p. 1

import Mathlib

/-!
# Moore, *Fast growth in the Følner function for Thompson's group F*, §3: marginal sets

J. T. Moore, Groups Geom. Dyn. 7 (2013) 633–651, arXiv:0905.1118v7, §3 (pp. 5–10): partial
actions, weighted Følner sets, word length, marginal sets and `Γ`-connected sets, for a group `G`
acting partially on a set `S` on the right.
-/

namespace MooreFoelner

open Classical

variable {G S : Type*} [Group G]

/-- Definition 3.1: a **partial action** of `G` on `S`, as a partial function `S × G → S`
(`act x g = some y` means `x · g = y`). Composition: whenever `x · g` and `(x · g) · h` are
defined, `x · (gh)` is defined and equals `(x · g) · h`. -/
structure IsPartialAction (act : S → G → Option S) : Prop where
  one : ∀ x, act x 1 = some x
  inv : ∀ (g : G) (x y : S), act x g = some y ↔ act y g⁻¹ = some x
  mul : ∀ (g h : G) (x y z : S), act x g = some y → act y h = some z → act x (g * h) = some z

/-- `μ(x · g)`, taken to be `0` when `x · g` is undefined (Definition 3.3's convention). -/
noncomputable def valAt (act : S → G → Option S) (μ : S →₀ ℝ) (x : S) (g : G) : ℝ :=
  match act x g with
  | some y => μ y
  | none => 0

/-- `μ(A) = ∑_{s ∈ A} μ(s)` (p. 5). -/
noncomputable def mass (μ : S →₀ ℝ) (A : Set S) : ℝ :=
  ∑ s ∈ μ.support.filter (· ∈ A), μ s

/-- Definition 3.3: `μ`, a function from a finite subset of `S` into `(0, ∞)` (zero off that
subset), is a **weighted `ε`-Følner set** with respect to `Γ`:
`∑_{γ ∈ Γ} ∑_{s ∈ S} |μ(s · γ) − μ(s)| < ε ∑_{s ∈ S} μ(s)`. -/
def IsWeightedFolner (act : S → G → Option S) (Γ : Finset G) (μ : S →₀ ℝ) (ε : ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧
    ∑ γ ∈ Γ, ∑ᶠ s, |valAt act μ s γ - μ s| < ε * mass μ Set.univ

/-- `μ ↾ A = μ · 1_A` (p. 5). -/
noncomputable def restrict (μ : S →₀ ℝ) (A : Set S) : S →₀ ℝ :=
  μ.filter (· ∈ A)

/-- `E · g = {x · g : x ∈ E}` (p. 5). -/
def image (act : S → G → Option S) (E : Set S) (g : G) : Set S :=
  {y | ∃ x ∈ E, act x g = some y}

/-- `x · g^k`, for the partial action. -/
def actPow (act : S → G → Option S) (x : S) (g : G) (k : ℕ) : Option S :=
  act x (g ^ k)

/-- `d_g` (p. 6): the minimum length of a word in `Γ` which evaluates to `g`. -/
noncomputable def wordLength (Γ : Finset G) (g : G) : ℕ :=
  sInf {n | ∃ w : List G, w.length = n ∧ (∀ γ ∈ w, γ ∈ Γ) ∧ w.prod = g}

/-- Definition 3.6: `g` **marginalizes `E` off `I`**: for every `x ∈ E`, if `x · g^k ∈ E` with
`k > 0`, then some `i < k` has `x · g^i ∈ I` or `x · g^i` undefined. -/
def Marginalizes (act : S → G → Option S) (g : G) (E I : Set S) : Prop :=
  ∀ x ∈ E, ∀ k : ℕ, 0 < k → (∃ y ∈ E, actPow act x g k = some y) →
    ∃ i < k, actPow act x g i = none ∨ ∃ y ∈ I, actPow act x g i = some y

/-- Definition 3.7: the **`k`-marginal** sets. The empty set is `0`-marginal; `E ⊆ S` is
`(k + 1)`-marginal when `E = ⋃_{i < l} Eᵢ` with each `Eᵢ` marginalized off a `k`-marginal set `Iᵢ` by
some `gᵢ ∈ G`. -/
inductive IsKMarginal (act : S → G → Option S) : ℕ → Set S → Prop
  | zero : IsKMarginal act 0 ∅
  | succ {k : ℕ} {l : ℕ} (E : Fin l → Set S) (I : Fin l → Set S) (g : Fin l → G)
      (hI : ∀ i, IsKMarginal act k (I i)) (hg : ∀ i, Marginalizes act (g i) (E i) (I i)) :
      IsKMarginal act (k + 1) (⋃ i, E i)

/-- Definition 3.7: `E` is **marginal** when it is `k`-marginal for some `k`. -/
def IsMarginal (act : S → G → Option S) (E : Set S) : Prop :=
  ∃ k, IsKMarginal act k E

/-- Definition 3.13: `A` is **`Γ`-connected**: any two points of `A` are joined by a sequence
`x₀ = x, x_{i+1} = xᵢ · γᵢ` (`γᵢ ∈ Γ`), all defined, ending at `y`, and staying in `A`. -/
def IsConnected (act : S → G → Option S) (Γ : Finset G) (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∃ (l : ℕ) (p : Fin (l + 1) → S),
    p 0 = x ∧ p (Fin.last l) = y ∧ (∀ i, p i ∈ A) ∧
      ∀ i : Fin l, ∃ γ ∈ Γ, act (p i.castSucc) γ = some (p i.succ)

/-- Definition 3.13: a **`Γ`-connected component** of `B`: a maximal `Γ`-connected subset. -/
def IsConnectedComponent (act : S → G → Option S) (Γ : Finset G) (A B : Set S) : Prop :=
  A ⊆ B ∧ IsConnected act Γ A ∧ ∀ A', A ⊆ A' → A' ⊆ B → IsConnected act Γ A' → A' = A

/-- The right action of `G` on itself, `x · g = x g`, as a (total) partial action. -/
def rightMul (x g : G) : Option G := some (x * g)

/-- The characteristic function `1_A` of a finite set, as a finitely supported function. -/
noncomputable def indicator (A : Finset S) : S →₀ ℝ :=
  Finsupp.onFinset A (fun s => if s ∈ A then 1 else 0) (fun s h => by by_contra hs; simp [hs] at h)

open scoped symmDiff in
/-- p. 1: a finite `A ⊆ G` is **`ε`-Følner** with respect to `Γ`:
`∑_{γ ∈ Γ} |(A · γ) △ A| < ε |A|`, with the right translate `A · γ = {a γ : a ∈ A}`. -/
def IsFolnerSet (Γ A : Finset G) (ε : ℝ) : Prop :=
  (∑ γ ∈ Γ, ((A.image (· * γ)) ∆ A).card : ℝ) < ε * A.card

/-- p. 1: the **Følner function** of `G` with respect to `Γ`:
`Føl_{G,Γ}(n) = min {|A| : A ⊆ G is 1/n-Følner}`, and `∞` when there is no such set. -/
noncomputable def folnerFunction (Γ : Finset G) (n : ℕ) : ℕ∞ :=
  ⨅ (A : Finset G) (_ : IsFolnerSet Γ A (1 / (n : ℝ))), (A.card : ℕ∞)

end MooreFoelner


