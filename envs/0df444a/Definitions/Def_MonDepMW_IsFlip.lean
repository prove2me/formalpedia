-- Prove2me | Definitions.Def_MonDepMW_IsFlip
-- name    : MonDepMW_IsFlip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:36.237401+00:00
-- url     : https://prove2.me/theorems/e7c0d4a5-4fd0-4d34-90fc-cc26889c9a53
-- title:
--   Flips, balls, flip-metric balls and the flip $G\oplus\sigma$
-- statement:
--   Let $\mathcal P$ be a partition of $V(G)$. A **$\mathcal P$-flip** of $G$ is a graph $H$ on $V(G)$ such that for every pair of parts $X,Y\in\mathcal P$ (possibly $X=Y$), either $xy\in E(G)\Leftrightarrow xy\in E(H)$ for all distinct $x\in X,y\in Y$, or $xy\in E(G)\Leftrightarrow xy\notin E(H)$ for all distinct $x\in X,y\in Y$. An **$S$-flip** of $G$ is a $\mathcal T_1(G,S)$-flip.
--
--   $\mathrm{Ball}^r_H[u]$ is the set of vertices at distance at most $r$ from $u$ in $H$. The flip-metric ball is
--   $$\mathrm{Ball}^r_{\mathcal P}[u]=\bigcap\{\mathrm{Ball}^r_H[u]: H\text{ is a }\mathcal P\text{-flip of }G\}.$$
--   For a symmetric relation $\sigma\subseteq\mathcal Q\times\mathcal Q$, $G\oplus\sigma$ is the $\mathcal Q$-flip complementing exactly the adjacency between the pairs of parts in $\sigma$.
--
--   **Formalization Note** Distances are `SimpleGraph.edist`, valued in $\mathbb N\cup\{\infty\}$, so vertices in different components are far apart.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, pp.12–13; §8, p.32

import Mathlib
import Definitions.Def_MonDepMW_oneType

set_option autoImplicit false

namespace MonDepMW

/-- **`𝒫`-flips.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.13: "A 𝒫-flip of G is a graph H with the same vertex set as G such that for every pair of
parts X, Y ∈ 𝒫 (possibly X = Y ) one of the following cases holds: xy ∈ E(G) ⇔ xy ∈ E(H), for all distinct x ∈ X and
y ∈ Y , or xy ∈ E(G) ⇔ xy ∉ E(H), for all distinct x ∈ X and y ∈ Y ." The parts are the classes of `a` and `b`.
An `S`-flip of `G` is `IsFlip G (oneType G S) H`: "an S-flip of G – is a 𝒯1(G, S)-flip of G". -/
def IsFlip {n : ℕ} (G : SimpleGraph (Fin n)) (P : Setoid (Fin n)) (H : SimpleGraph (Fin n)) : Prop :=
  ∀ a b : Fin n,
    (∀ x y, P.r a x → P.r b y → x ≠ y → (G.Adj x y ↔ H.Adj x y)) ∨
    (∀ x y, P.r a x → P.r b y → x ≠ y → (G.Adj x y ↔ ¬ H.Adj x y))

/-- **The ball `Ball^r_H[u]`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "The ball with center u of radius r ∈ N ∪ {0} in G is the set of all the
vertices that are at distance at most r from u in G."

**Formalization Note.** `SimpleGraph.edist` is `⊤` between vertices in different components, so they are far apart; the
real-valued `dist` would give them distance `0`. -/
def ball {n : ℕ} (H : SimpleGraph (Fin n)) (r : ℕ) (u : Fin n) : Set (Fin n) :=
  {v | H.edist u v ≤ (r : ℕ∞)}

/-- **The flip-metric ball `Ball^r_𝒫[u]`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.13: "Ball^r_𝒫[u] := ⋂{Ball^r_H[u]: H is a 𝒫-flip of G}." -/
def flipBall {n : ℕ} (G : SimpleGraph (Fin n)) (P : Setoid (Fin n)) (r : ℕ) (u : Fin n) : Set (Fin n) :=
  {v | ∀ H, IsFlip G P H → v ∈ ball H r u}

/-- **The flip `G ⊕ σ`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §8, p.32: "let G ⊕ σ be the 𝒬-flip of G such that for all X, Y ∈ 𝒬 and distinct vertices
x ∈ X, y ∈ Y we have that: xy ∈ E(G) ⇔ xy ∈ E(G ⊕ σ) if (X, Y ) ∉ σ, xy ∈ E(G) ⇔ xy ∉ E(G ⊕ σ) if (X, Y ) ∈ σ." -/
def flipBy {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Setoid (Fin n))
    (σ : Quotient Q → Quotient Q → Prop) (hσ : ∀ X Y, σ X Y → σ Y X) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (G.Adj x y ↔ ¬ σ (Quotient.mk Q x) (Quotient.mk Q y))
  symm := ⟨fun x y h => ⟨h.1.symm, by
    rw [G.adj_comm y x]
    exact h.2.trans (not_congr ⟨hσ _ _, hσ _ _⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end MonDepMW


