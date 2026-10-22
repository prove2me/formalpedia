-- Prove2me | Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
-- name    : GroupoidSchreier_Interpretation_WeakAction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:03.354904+00:00
-- url     : https://prove2.me/theorems/d88c36d1-c8c7-4760-8924-577a0ea424dd
-- title:
--   Proposition 2.6, Example 2.11, Definition 3.3, pp. 7–15 — weak actions of a groupoid on a family of groups, their morphisms, and H²
-- statement:
--   Let $\mathcal G$ be a groupoid and $\mathcal K = \{K_A\}_{A\in\mathcal G}$ a family of groups indexed by the objects of $\mathcal G$. For arrows $A \xrightarrow{u} B \xrightarrow{v} C$ write $vu$ for their composite.
--
--   **Weak action** (Proposition 2.6, p. 7, taken as the definition as on p. 15). A weak action of $\mathcal G$ on $\mathcal K$ is a pair $\langle F,\sigma\rangle$ where $F$ assigns to every arrow $u : A\to B$ a group isomorphism $F(u) = {}^u(-) : K_A \to K_B$, and $\sigma$ assigns to every composable pair $A\xrightarrow{u}B\xrightarrow{v}C$ an element $\sigma_{vu}\in K_C$, such that for every 3-chain $A\xrightarrow{u}B\xrightarrow{v}C\xrightarrow{w}D$ and every $x\in K_A$:
--
--   1. ${}^{1}x = x$,
--   2. $\sigma_{11} = 1$,
--   3. $\sigma_{vu}\,{}^{vu}x = {}^v({}^u x)\,\sigma_{vu}$,
--   4. $\sigma_{wv}\,\sigma_{(wv)u} = {}^w\sigma_{vu}\,\sigma_{w(vu)}$.
--
--   Nothing more is required of $\sigma$; in particular $F$ need not be a functor, condition 3 says $F(v)\circ F(u)$ equals $F(vu)$ up to conjugation by $\sigma_{vu}$.
--
--   **Morphisms** (Example 2.11, pp. 9–10). A morphism $(F_1,\sigma^1)\to(F_2,\sigma^2)$ is a family of maps $\tau_{AB} : \mathcal G(A,B)\to K_B$ such that for all $k\in K_A$ and $A\xrightarrow{u}B\xrightarrow{v}C$:
--
--   1. (naturality) $\tau_{AB}(u)\cdot F_1(u)(k) = F_2(u)(k)\cdot\tau_{AB}(u)$,
--   2. (normalization) $\tau_{AA}(1) = 1$,
--   3. (coherence) $F_2(v)\big(\tau_{AB}(u)\big)\cdot\tau_{BC}(v)\cdot\sigma^1_{vu} = \sigma^2_{vu}\cdot\tau_{AC}(vu)$.
--
--   **Cohomology** (Definition 3.3, p. 15). The second cohomology of $\mathcal G$ with coefficients in the 2-groupoid $\mathrm{AUT}(\mathcal K)$ is the set of connected components of the category $\widetilde{\mathrm{Act}}(\mathcal G,\mathcal K)$ of weak actions:
--
--   $$H^2_{|\mathrm{AUT}(\mathcal K)|}(\mathcal G,\mathcal K) := \widetilde{\mathrm{Act}}[\mathcal G,\mathcal K].$$
--
--   Two weak actions lie in the same component when they are joined by a zigzag of morphisms. The class of $F$ is written $[F]$.
--
--   These are the 2-cocycles and the cohomology classes whose classification by groupoid extensions is the subject of the mission.
--
--   **Formalization Note** Objects of $\mathcal G$ and the groups $K_A$ live in one universe. Arrows of $\mathcal G$ compose with Mathlib's diagrammatic `≫`, so the paper's $vu$ is `u ≫ v`, and the paper's $\sigma_{vu}$ is `σ u v`. `F u` is a `MulEquiv`. Every product is written in the printed order. $H^2$ is the quotient (`Quot`) of the type of weak actions by the relation "there is a morphism"; a `Quot` identifies exactly the equivalence closure of its relation, which is the zigzag relation defining connected components. `H2.mk F` is the class $[F]$.
-- source:
--   Blanco, Bullejos & Faro, Categorical non abelian cohomology, and the Schreier theory of groupoids, arXiv:math/0410202v1, pp. 7–15, Proposition 2.6 (p. 7), Example 2.11 (pp. 9–10), Definition 3.3 (p. 15)

import Mathlib

namespace GroupoidSchreier.Interpretation

open CategoryTheory

universe u

/-- Proposition 2.6 (p. 7), used as the definition of a weak action (p. 15): a weak action
`⟨F, σ⟩` of the groupoid `G` on the family of groups `K`. `F u` is a group isomorphism
`K A ≃* K B` for `u : A ⟶ B`; `σ u v : K C` is the paper's `σ_{vu}` for `A ⟶[u] B ⟶[v] C`,
and `u ≫ v` is the paper's composite `vu`. -/
structure WeakAction (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] where
  /-- `F u = ^u(-) : K_A → K_B`, a group isomorphism -/
  F : ∀ {A B : G}, (A ⟶ B) → (K A ≃* K B)
  /-- `σ u v = σ_{vu} ∈ K_C` -/
  σ : ∀ {A B C : G}, (A ⟶ B) → (B ⟶ C) → K C
  /-- condition 1: `^1 x = x` -/
  map_id : ∀ (A : G) (x : K A), F (𝟙 A) x = x
  /-- condition 2: `σ_{11} = 1` -/
  σ_id : ∀ A : G, σ (𝟙 A) (𝟙 A) = 1
  /-- condition 3: `σ_{vu} · ^{vu}x = ^v(^u x) · σ_{vu}` -/
  conj : ∀ {A B C : G} (u : A ⟶ B) (v : B ⟶ C) (x : K A),
    σ u v * F (u ≫ v) x = F v (F u x) * σ u v
  /-- condition 4: `σ_{wv} σ_{(wv)u} = ^wσ_{vu} · σ_{w(vu)}` -/
  cocycle : ∀ {A B C D : G} (u : A ⟶ B) (v : B ⟶ C) (w : C ⟶ D),
    σ v w * σ u (v ≫ w) = F w (σ u v) * σ (u ≫ v) w

/-- Example 2.11 (pp. 9–10): a morphism `F₁ → F₂` in `Act~(G, K)`, a family of maps
`τ_{AB} : G(A, B) → K_B` satisfying naturality, normalization and coherence. -/
structure ActHom {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F₁ F₂ : WeakAction G K) where
  /-- `τ u = τ_{AB}(u) ∈ K_B` -/
  τ : ∀ {A B : G}, (A ⟶ B) → K B
  /-- naturality: `τ_{AB}(u) · F₁(u)(k) = F₂(u)(k) · τ_{AB}(u)` -/
  naturality : ∀ {A B : G} (u : A ⟶ B) (k : K A), τ u * F₁.F u k = F₂.F u k * τ u
  /-- normalization: `τ_{AA}(1) = 1` -/
  normalization : ∀ A : G, τ (𝟙 A) = 1
  /-- coherence: `F₂(v)(τ_{AB}(u)) · τ_{BC}(v) · σ¹_{vu} = σ²_{vu} · τ_{AC}(vu)` -/
  coherence : ∀ {A B C : G} (u : A ⟶ B) (v : B ⟶ C),
    F₂.F v (τ u) * τ v * F₁.σ u v = F₂.σ u v * τ (u ≫ v)

/-- Definition 3.3 (p. 15): `H²_{|AUT(K)|}(G, K) = Act~[G, K]`, the set of connected components of
the category of weak actions of `G` on `K`. `Quot` of the relation "there is a morphism" is its
equivalence closure, i.e. exactly the connected components. -/
def H2 (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] : Type u :=
  Quot (fun F₁ F₂ : WeakAction G K => Nonempty (ActHom F₁ F₂))

/-- The class `[F] ∈ H²_{|AUT(K)|}(G, K)` of a weak action `F` (its connected component). -/
def H2.mk {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) : H2 G K :=
  Quot.mk _ F

end GroupoidSchreier.Interpretation


