-- Prove2me | Definitions.Def_ScatCaps_Caps_Model
-- name    : ScatCaps_Caps_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:04:52.228744+00:00
-- url     : https://prove2.me/theorems/633e0e56-6c2e-4b8f-84e9-b556e57ff0ac
-- title:
--   §1, §4, pp. 3, 19–21 — caps, complete caps, translation caps 𝒦_G, maximal translation caps, products, doubling and the parabola in AG(r, q)
-- statement:
--   Let $K$ be a field (in this mission always the finite field $\mathbb F_q$, $q = 2^t$), and let $AG(r, K)$ be the affine space whose points are the vectors $(a_1, \dots, a_r) \in K^r$.
--
--   1. A **cap** of $AG(r, K)$ is a set $S$ of points no three of which are collinear: for any three pairwise distinct $a, b, c \in S$ there is no affine line over $K$ containing all three.
--   2. A **complete cap** is a cap which is maximal with respect to set-theoretical inclusion: for every point $P \in AG(r, K)$ with $P \notin S$, the set $S \cup \{P\}$ is not a cap.
--   3. For an additive subgroup $G$ of $K^r$, $\mathcal K_G = \{P_v \mid v \in G\}$ is the set of affine points whose coordinate vectors lie in $G$.
--   4. A **translation cap** is a cap that coincides with $\mathcal K_G$ for some additive subgroup $G$ of $K^r$.
--   5. A **maximal translation cap** of $AG(r, q)$ is a translation cap $S$ attaining the bound $q^{r/2}$, i.e.
--   $$|S|^2 = q^r .$$
--   6. For $S \subseteq AG(r, K)$ and $T \subseteq AG(\bar r, K)$, the **product** $S \times T \subseteq AG(r + \bar r, K)$ is the set of concatenations $(a_1, \dots, a_r, b_1, \dots, b_{\bar r})$ with $(a_i) \in S$, $(b_j) \in T$.
--   7. The **doubling** $S \times \{0, 1\} \subseteq AG(r + 1, K)$ of $S \subseteq AG(r, K)$ is the set of points $(a_1, \dots, a_r, c)$ with $(a_1, \dots, a_r) \in S$ and $c \in \{0, 1\}$; for $S = \mathcal K_G$ it is $\mathcal K_{G \times \{0,1\}}$.
--   8. The **parabola** of $AG(2, K)$ is $\{(x, x^2) : x \in K\}$.
--
--   These are the objects of Section 4: translation caps link scattered $\mathbb F_2$-linear sets to caps, and products and doubling turn a maximal translation cap in $AG(3, q)$ into a complete cap in $AG(n, q)$.
--
--   **Formalization Note** Points of $AG(r, K)$ are functions `Fin r → K`, and collinearity is Mathlib's affine `Collinear K` over the field $K$ itself (not over $\mathbb F_2$ or $\mathbb R$). Maximality is written in the squared form $|S|^2 = |K|^r$, which avoids the half-integer exponent $r/2$ when $r$ is odd; it is the paper's $|S| = q^{r/2}$. The product is the image of $S \times T$ under `Fin.append`, the doubling uses `Fin.snoc` (new last coordinate). Sizes are `Set.ncard`.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 3 (caps, complete caps), p. 19 Definition 4.1, p. 20 (maximal translation cap; Lemmas 4.5, 4.6), p. 21 (proof of Proposition 4.7)

import Mathlib

namespace ScatCaps.Caps

/-- A cap of `AG(r, K)`: a set of points of `K^r` no three of which are collinear (p. 3). -/
def IsCap {K : Type*} [Field K] {r : ℕ} (S : Set (Fin r → K)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
    ¬ Collinear K ({a, b, c} : Set (Fin r → K))

/-- A complete cap: a cap which is maximal with respect to inclusion, i.e. adding any point of
`AG(r, K)` outside it destroys the cap property (p. 3). -/
def IsCompleteCap {K : Type*} [Field K] {r : ℕ} (S : Set (Fin r → K)) : Prop :=
  IsCap S ∧ ∀ P : Fin r → K, P ∉ S → ¬ IsCap (insert P S)

/-- The point set `𝒦_G = {P_v | v ∈ G}` of an additive subgroup `G` of `K^r` (Definition 4.1). -/
def KG {K : Type*} [Field K] {r : ℕ} (G : AddSubgroup (Fin r → K)) : Set (Fin r → K) :=
  (G : Set (Fin r → K))

/-- A translation cap: a cap which coincides with `𝒦_G` for some additive subgroup `G` of `K^r`
(Definition 4.1). -/
def IsTranslationCap {K : Type*} [Field K] {r : ℕ} (S : Set (Fin r → K)) : Prop :=
  IsCap S ∧ ∃ G : AddSubgroup (Fin r → K), KG G = S

/-- A maximal translation cap: a translation cap of `AG(r, q)` attaining the bound `q^{r/2}`
(p. 20), written in squared form `|S|^2 = q^r`. -/
def IsMaximalTranslationCap {K : Type*} [Field K] {r : ℕ} (S : Set (Fin r → K)) : Prop :=
  IsTranslationCap S ∧ S.ncard ^ 2 = Nat.card K ^ r

/-- The product `S × T ⊆ AG(r + r', K)` of `S ⊆ AG(r, K)` and `T ⊆ AG(r', K)`: the concatenations
`(a_1, …, a_r, b_1, …, b_{r'})` (Lemma 4.5). -/
def capProd {K : Type*} [Field K] {r r' : ℕ} (S : Set (Fin r → K)) (T : Set (Fin r' → K)) :
    Set (Fin (r + r') → K) :=
  (fun p : (Fin r → K) × (Fin r' → K) => Fin.append p.1 p.2) '' (S ×ˢ T)

/-- The doubling `S × {0, 1} ⊆ AG(r + 1, K)` of `S ⊆ AG(r, K)`: the points `(a_1, …, a_r, c)`
with `(a_1, …, a_r) ∈ S` and `c ∈ {0, 1}` (Lemma 4.6). -/
def doubling {K : Type*} [Field K] {r : ℕ} (S : Set (Fin r → K)) : Set (Fin (r + 1) → K) :=
  {x | ∃ v ∈ S, ∃ c : K, (c = 0 ∨ c = 1) ∧ x = Fin.snoc (α := fun _ => K) v c}

/-- The parabola `{(x, x^2) : x ∈ K}` of `AG(2, K)` (proof of Proposition 4.7, p. 21). -/
def parabola (K : Type*) [Field K] : Set (Fin 2 → K) :=
  Set.range (fun x : K => ![x, x ^ 2])

end ScatCaps.Caps


