-- Prove2me | Definitions.Def_ClassifAgg_Aggregation_Classes
-- name    : ClassifAgg_Aggregation_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:25.920171+00:00
-- url     : https://prove2.me/theorems/1aecd265-e824-4f3b-bf64-7a059a1977a4
-- title:
--   Definitions 1–4, (A1), (A2), (7), pp. 138–140 — ε-nets, complexity bound with bracketing, the margin assumption and (𝒢*, κ, ρ)-classes
-- statement:
--   The classes of sets and of distributions used by Tsybakov.
--
--   1. **Nets (Definition 1, p. 139).** A class $\mathcal N$ of sets is an $\varepsilon$-net on a class $\mathcal G$ for $d_\triangle$ if every $G\in\mathcal G$ has some $G'\in\mathcal N$ with $d_\triangle(G,G')\le\varepsilon$; it is an $\varepsilon$-net for $d_{\triangle,e}$ (at sample size $n$) if for every sample every $G\in\mathcal G$ has some $G'\in\mathcal N$, possibly depending on the sample, with $d_{\triangle,e}(G,G')\le\varepsilon$. The net need not lie inside $\mathcal G$.
--   2. **Complexity bound (Definitions 2–3, p. 139).** A class $\mathcal G$ has complexity bound $\rho>0$ with constant $A>0$ if its $\delta$-entropy with bracketing for $d_\triangle$ satisfies
--   $$\mathcal H_B(\delta,\mathcal G,d_\triangle)\le A\delta^{-\rho}\qquad\forall\,0<\delta\le1,$$
--   that is, for every such $\delta$ there are $m$ pairs of Borel sets $(G^L_j,G^U_j)$ with $d_\triangle(G^L_j,G^U_j)\le\delta$ such that every $G\in\mathcal G$ satisfies $G^L_j\subseteq G\subseteq G^U_j$ for some $j$, and $\log m\le A\delta^{-\rho}$.
--   3. **Margin assumption (A1), p. 138.** For a distribution $(P_X,\eta)$, with $\kappa\ge1$, $c_0>0$, $0<\varepsilon_0\le1$: $d(G,G^*)\ge c_0\,d_\triangle^\kappa(G,G^*)$ for every Borel $G$ with $d_\triangle(G,G^*)\le\varepsilon_0$.
--   4. **Distributions.** $P_X$ is a probability measure and $\eta$ is measurable with $0\le\eta\le1$.
--   5. **Condition (7), p. 140.** $\lim_{t\to0}\sup_{\pi\in\mathcal P}P(|\eta(X)-1/2|\le t)=0$.
--   6. **$(\mathcal G^*,\kappa,\rho)$-classes (Definition 4, p. 140).** A class $\mathcal P$ of distributions is a $(\mathcal G^*,\kappa,\rho)$-class if for every $\pi\in\mathcal P$, $G^*_\pi\in\mathcal G^*$, assumption (A1) holds with $\kappa,c_0,\varepsilon_0$, assumption (A2) holds ($\mathcal G^*$ has complexity bound $0<\rho<1$ with constant $A$ for the pseudodistance $d_\triangle$ of $\pi$'s design law), and either $\varepsilon_0=1$ or (7) holds.
--
--   These are the hypotheses of Theorems 1 and 3: (A1) controls the margin through $\kappa$, and the complexity bound controls the size of the candidate sets through $\rho$.
--
--   **Formalization Note** The complexity bound is stated without the minimal number $N_B$: "the smallest $m$ satisfies $\log m\le A\delta^{-\rho}$" is equivalent to "some $m$ does", and this avoids the junk value of an infimum over an empty set. Because $d_\triangle$ depends on $P_X$, the complexity bound and the nets for $d_\triangle$ are stated relative to the design law of each distribution in the class. The constants $A$, $c_0$, $\varepsilon_0$ of (A1)–(A2) are explicit parameters; the page fixes $c_0,\varepsilon_0$ for all classes "without loss of generality". Condition (7) is written as: for every $\varepsilon>0$ some $t>0$ has $P(|\eta(X)-1/2|\le t)\le\varepsilon$ for all $\pi\in\mathcal P$, which is equivalent since the probability is nondecreasing in $t$. Members of $\mathcal G^*$ are Borel sets (p. 135).
-- source:
--   Tsybakov (2004), Ann. Statist. 32, (A1), p. 138; Definitions 1–3, p. 139; (A2), Definition 4 and (7), p. 140

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Model

namespace ClassifAgg.Aggregation

open MeasureTheory

/-- Definition 1 (p. 139) for the pseudodistance `d_△`: `𝒩` is an `ε`-net on `𝒢` if every
`G ∈ 𝒢` has some `G' ∈ 𝒩` with `d_△(G, G') ≤ ε`. The net need not lie inside `𝒢`. -/
def IsNet {d : ℕ} (PX : Measure (E d)) (ε : ℝ) (net cls : Set (Set (E d))) : Prop :=
  ∀ G ∈ cls, ∃ G' ∈ net, dTri PX G G' ≤ ε

/-- Definition 1 (p. 139) for the empirical pseudodistance `d_{△,e}` at sample size `n`: at every
sample `s`, every `G ∈ 𝒢` has some `G' ∈ 𝒩` (which may depend on `s`) with `d_{△,e}(G, G') ≤ ε`. -/
def IsEmpNet {d : ℕ} (n : ℕ) (ε : ℝ) (net cls : Set (Set (E d))) : Prop :=
  ∀ s : Fin n → E d × Bool, ∀ G ∈ cls, ∃ G' ∈ net, dTriEmp s G G' ≤ ε

/-- Definitions 2–3 (p. 139): the class `𝒢` has complexity bound `ρ` with constant `A` for `d_△`,
i.e. `H_B(δ, 𝒢, d_△) = log N_B(δ, 𝒢, d_△) ≤ A δ^{-ρ}` for all `0 < δ ≤ 1`.

It is stated without the minimal number `N_B`: for each `δ` there are `m` brackets
`(G_j^L, G_j^U)` of Borel sets with `d_△(G_j^L, G_j^U) ≤ δ`, covering `𝒢` in the sense that every
`G ∈ 𝒢` satisfies `G_j^L ⊆ G ⊆ G_j^U` for some `j`, and `log m ≤ A δ^{-ρ}`. Since the smallest such
`m` satisfies the bound iff some `m` does, this is equivalent to Definition 3, and it avoids the
junk value of an infimum over an empty set. (For nonempty `𝒢` such `m` is at least `1`.) -/
def HasComplexityBound {d : ℕ} (PX : Measure (E d)) (cls : Set (Set (E d))) (ρ A : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ m : ℕ, ∃ Glo Gup : Fin m → Set (E d),
    (∀ j, MeasurableSet (Glo j) ∧ MeasurableSet (Gup j) ∧ dTri PX (Glo j) (Gup j) ≤ δ) ∧
    (∀ G ∈ cls, ∃ j, Glo j ⊆ G ∧ G ⊆ Gup j) ∧
    Real.log m ≤ A * δ ^ (-ρ)

/-- Assumption (A1) on the margin (p. 138), for the distribution with design law `P_X` and
regression function `η`: `d(G, G*) ≥ c₀ d_△^κ(G, G*)` for every Borel `G` with
`d_△(G, G*) ≤ ε₀`. -/
def Margin {d : ℕ} (PX : Measure (E d)) (η : E d → ℝ) (κ c0 ε0 : ℝ) : Prop :=
  ∀ G : Set (E d), MeasurableSet G → dTri PX G (bayesSet η) ≤ ε0 →
    c0 * dTri PX G (bayesSet η) ^ κ ≤ excess PX η G

/-- A joint distribution `π` of `(X, Y)`, given as the pair `(P_X, η)`: `P_X` is a probability
measure on `ℝᵈ` and `η` a measurable function with values in `[0, 1]`. -/
def IsDistr {d : ℕ} (π : Measure (E d) × (E d → ℝ)) : Prop :=
  IsProbabilityMeasure π.1 ∧ Measurable π.2 ∧ ∀ x, 0 ≤ π.2 x ∧ π.2 x ≤ 1

/-- The common core of Definition 4 (p. 140): for every `π ∈ 𝒫`, `G*_π ∈ 𝒢*`, the margin
assumption (A1) holds with `κ ≥ 1`, `c₀ > 0`, `0 < ε₀ ≤ 1`, and (A2) holds: `𝒢*` has complexity
bound `0 < ρ < 1` with constant `A > 0` for `d_△` of `π`'s design law. Members of `𝒢*` are Borel. -/
def IsClassCore {d : ℕ} (P : Set (Measure (E d) × (E d → ℝ))) (cls : Set (Set (E d)))
    (κ ρ A c0 ε0 : ℝ) : Prop :=
  1 ≤ κ ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < A ∧ 0 < c0 ∧ 0 < ε0 ∧ ε0 ≤ 1 ∧
    (∀ G ∈ cls, MeasurableSet G) ∧
    ∀ π ∈ P, IsDistr π ∧ bayesSet π.2 ∈ cls ∧ Margin π.1 π.2 κ c0 ε0 ∧
      HasComplexityBound π.1 cls ρ A

/-- Condition (7) (p. 140): `lim_{t → 0} sup_{π ∈ 𝒫} P(|η(X) − 1/2| ≤ t) = 0`. Since the
probability is nondecreasing in `t`, this says: for every `ε > 0` some `t > 0` has
`P(|η(X) − 1/2| ≤ t) ≤ ε` for all `π ∈ 𝒫`. -/
def MarginMassVanishes {d : ℕ} (P : Set (Measure (E d) × (E d → ℝ))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∀ π ∈ P, (π.1 {x | |π.2 x - 1 / 2| ≤ t}).toReal ≤ ε

/-- Definition 4 (p. 140): `𝒫` is a `(𝒢*, κ, ρ)`-class, with the constants `A, c₀, ε₀` of (A1)
and (A2) made explicit, if `IsClassCore` holds and either `ε₀ = 1` or (7) holds. -/
def IsGKRClass {d : ℕ} (P : Set (Measure (E d) × (E d → ℝ))) (cls : Set (Set (E d)))
    (κ ρ A c0 ε0 : ℝ) : Prop :=
  IsClassCore P cls κ ρ A c0 ε0 ∧ (ε0 = 1 ∨ MarginMassVanishes P)

end ClassifAgg.Aggregation


