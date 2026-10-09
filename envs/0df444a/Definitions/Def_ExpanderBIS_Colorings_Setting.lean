-- Prove2me | Definitions.Def_ExpanderBIS_Colorings_Setting
-- name    : ExpanderBIS_Colorings_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:42.892026+00:00
-- url     : https://prove2.me/theorems/73697211-8678-4c9a-86df-c94a1602ef6e
-- title:
--   pp. 3, 5, 12, 18–19, 23, 26–27, 30 — random regular bipartite graphs, proper colorings, patterns, χ_{A,B}(S), the G³ polymer models and Z̃_G(q)
-- statement:
--   This file fixes every object of §5 of Jenssen, Keevash and Perkins.
--
--   **Graphs.** The vertex set is $V = \mathcal O \sqcup \mathcal E$ with two sides of size $m$ (so $n = 2m$): the odd side $\mathcal O$ and the even side $\mathcal E$. $\mathcal G^{\mathrm{bip}}(2m,\Delta)$ is the finite set of labelled simple graphs $G$ on $V$ all of whose edges join $\mathcal O$ to $\mathcal E$ and in which every vertex has degree exactly $\Delta$. A property $P$ holds for **almost every** $\Delta$-regular bipartite graph if
--   $$\frac{\#\{G \in \mathcal G^{\mathrm{bip}}(2m,\Delta) : P(m,G)\}}{\#\mathcal G^{\mathrm{bip}}(2m,\Delta)} \longrightarrow 1 \qquad (m \to \infty).$$
--
--   **Expansion.** For $S \subseteq V$, the vertex boundary is $\partial S = \{v \notin S : v \text{ is adjacent to a vertex of } S\}$ and $S^+ = S \cup \partial S$. $G$ is a bipartite $(\sigma,\rho)$-expander (Definition 21) if $|\partial S| \ge \rho|S|$ for every $S$ contained in one side with $|S| \le \sigma m$. The standing assumption of §5 is that $G$ is a $\bigl(\tfrac{4\log\Delta}{\Delta}, \tfrac{\Delta}{4\log\Delta} - \tfrac12\bigr)$-expander.
--
--   **Colorings and patterns.** $\mathcal X_q(G)$ is the set of proper colorings $f : V \to [q]$, and $Z_G(q) = |\mathcal X_q(G)|$. A pattern is a pair $(A,B)$ of disjoint sets with $A \cup B = [q]$; it is encoded by $A$, with $B = [q] \setminus A$, so there are $2^q$ patterns. A coloring $f$ agrees with $(A,B)$ at $v$ if $v \in \mathcal O$ and $f(v) \in A$, or $v \in \mathcal E$ and $f(v) \in B$; otherwise it disagrees. $\chi_{A,B}(S)$ is the set of proper colorings that disagree with $(A,B)$ at every vertex of $S$ and agree at every vertex of $V \setminus S$.
--
--   **Polymers.** $G^3$ is the graph on $V$ in which distinct $u, v$ are adjacent when $d_G(u,v) \le 3$. A set is $G^3$-connected if it induces a connected subgraph of $G^3$ (Definition 19); its $G^3$-connected components are those of $G^3[S]$. A set $S$ is **little** if $|S| \le 4q\frac{\log\Delta}{\Delta}m$, and **sparse** if all of its $G^3$-connected components are little. A polymer is a little $G^3$-connected set; $\mathcal C(G)$ is the set of polymers, and two polymers are compatible if $d_G(\gamma_1,\gamma_2) > 3$. For a pattern $(A,B)$ the weight of a polymer and the polymer partition function are
--   $$w_{A,B}(\gamma) = \frac{|\chi_{A,B}(\gamma)|}{|A|^m|B|^m}, \qquad \Xi_{A,B}(G) = \sum_{\Gamma} \prod_{\gamma \in \Gamma} w_{A,B}(\gamma),$$
--   the sum running over all families $\Gamma \subseteq \mathcal C(G)$ of pairwise compatible polymers, the empty family included. The approximant of Lemma 29 is
--   $$\tilde Z_G(q) = \sum_{(A,B)} |A|^m|B|^m\, \Xi_{A,B}(G).$$
--
--   Finally $\hat Z$ is an $\varepsilon$-relative approximation to $Z$ (Definition 10) if $e^{-\varepsilon}\hat Z \le Z \le e^{\varepsilon}\hat Z$, and the decay function of §5.1 is $g(\gamma) = \frac{\Delta}{10q^2\log\Delta}|\gamma|$.
--
--   These objects are the vocabulary of every statement of the mission: the reduction (Lemma 29) and the Kotecký–Preiss condition of §5.1 are both statements about $\tilde Z_G(q)$, $w_{A,B}$ and $\mathcal C(G)$.
--
--   **Formalization Note.** Vertices are `Fin m ⊕ Fin m` (`Sum.inl` = $\mathcal O$, `Sum.inr` = $\mathcal E$); this fixed-sides labelled model of $\mathcal G^{\mathrm{bip}}(n,\Delta)$ is a disclosed choice, since the paper does not fix a bipartition. Distances use the extended distance `SimpleGraph.edist`, so vertices in different components are at distance $\infty$. `Connected` in Mathlib includes nonemptiness, so polymers are nonempty. For a pattern with an empty side, $|A|^m|B|^m = 0$ and Lean's convention $x/0 = 0$ makes every weight $0$, so $\Xi_{A,B} = 1$ and the pattern contributes $0$ to $\tilde Z_G(q)$ (for $m \ge 1$); the paper's sum over all patterns is kept. `log` is the natural logarithm.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 3, 5, 12, 18–19, 23, 26–27, 30: §1 (𝒢^bip), §1.2, Definitions 10, 19, 21, 26, §5 (χ_{A,B}(S), little sets, polymers, Ξ_{A,B}, Lemma 29's Z̃_G(q)), §5.1 (g)

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

open Classical Filter

namespace ExpanderBIS.Colorings

noncomputable section

/-- The set `𝒳_q(G)` of proper `q`-colorings `f : V(G) → [q]`. -/
def properColorings {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q : ℕ) :
    Finset (ExpanderBIS.RandomHardCore.Vertex m → Fin q) :=
  Finset.univ.filter (fun f => ∀ u v, G.Adj u v → f u ≠ f v)

/-- A pattern `(A, B)` is encoded by `A ⊆ [q]`, with `B = [q] \ A`.
`f` agrees with `(A, B)` at `v` if `v ∈ 𝒪` and `f v ∈ A`, or `v ∈ ℰ` and `f v ∈ B`. -/
def Agrees {m q : ℕ} (A : Finset (Fin q)) (f : ExpanderBIS.RandomHardCore.Vertex m → Fin q) (v : ExpanderBIS.RandomHardCore.Vertex m) : Prop :=
  (v.isLeft ∧ f v ∈ A) ∨ (v.isRight ∧ f v ∉ A)

/-- `χ_{A,B}(S)`: proper colorings that disagree with `(A, B)` at every `v ∈ S` and agree
at every `v ∉ S`. -/
def chi {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q : ℕ) (A : Finset (Fin q))
    (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : Finset (ExpanderBIS.RandomHardCore.Vertex m → Fin q) :=
  (properColorings G q).filter
    (fun f => (∀ v ∈ S, ¬ Agrees A f v) ∧ ∀ v, v ∉ S → Agrees A f v)

/-- `S` is little: `|S| ≤ 4q (log Δ/Δ) m`. -/
def IsLittle {m : ℕ} (q Δ : ℕ) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : Prop :=
  (S.card : ℝ) ≤ 4 * q * (Real.log Δ / Δ) * m

/-- The cube `G³`: `u ~ v` iff `u ≠ v` and `d_G(u, v) ≤ 3` (extended distance, so
vertices in different components are never adjacent). -/
def powerThree {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m) where
  Adj u v := u ≠ v ∧ G.edist u v ≤ 3
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by simpa [SimpleGraph.edist_comm] using h.2⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Definition 19: `S` is `G³`-connected if `G³[S]` is connected (in particular nonempty). -/
def IsG3Connected {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : Prop :=
  ((powerThree G).induce (S : Set (ExpanderBIS.RandomHardCore.Vertex m))).Connected

/-- The `G³`-connected component of `S` containing `v` (empty if `v ∉ S`). -/
def g3Comp {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) (v : ExpanderBIS.RandomHardCore.Vertex m) :
    Finset (ExpanderBIS.RandomHardCore.Vertex m) :=
  S.filter (fun u => ∃ hv : v ∈ S, ∃ hu : u ∈ S,
    ((powerThree G).induce (S : Set (ExpanderBIS.RandomHardCore.Vertex m))).Reachable ⟨v, hv⟩ ⟨u, hu⟩)

/-- The `G³`-connected components of `S`. -/
def g3Components {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) :
    Finset (Finset (ExpanderBIS.RandomHardCore.Vertex m)) :=
  S.image (g3Comp G S)

/-- `S` is sparse if every `G³`-connected component of `S` is little. -/
def IsSparse {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q Δ : ℕ) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : Prop :=
  ∀ γ ∈ g3Components G S, IsLittle q Δ γ

/-- The polymers `𝒞(G)`: little, `G³`-connected vertex sets. -/
def colPolymers {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q Δ : ℕ) :
    Finset (Finset (ExpanderBIS.RandomHardCore.Vertex m)) :=
  Finset.univ.filter (fun γ => IsLittle q Δ γ ∧ IsG3Connected G γ)

/-- Compatibility: `d_G(γ₁, γ₂) > 3`. -/
def Compat3 {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (γ₁ γ₂ : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : Prop :=
  ∀ u ∈ γ₁, ∀ v ∈ γ₂, (3 : ℕ∞) < G.edist u v

/-- The weight `w_{A,B}(γ) = |χ_{A,B}(γ)| / (|A|^m |B|^m)` (Lean's `x / 0 = 0` makes it `0`
for a pattern with an empty side). -/
def colWeight {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q : ℕ) (A : Finset (Fin q))
    (γ : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : ℝ :=
  ((chi G q A γ).card : ℝ) /
    ((A.card : ℝ) ^ m * ((Finset.univ \ A).card : ℝ) ^ m)

/-- The polymer partition function `Ξ_{A,B}(G) = Σ_{Γ ∈ 𝒢} Π_{γ ∈ Γ} w_{A,B}(γ)`, over the
families of pairwise compatible polymers (the empty family included). -/
def colXi {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q Δ : ℕ) (A : Finset (Fin q)) : ℝ :=
  ∑ Γ ∈ (colPolymers G q Δ).powerset,
    if (∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η → Compat3 G γ η) then
      ∏ γ ∈ Γ, colWeight G q A γ else 0

/-- `Z̃_G(q) = Σ_{(A,B) ∈ 𝒫} |A|^m |B|^m Ξ_{A,B}(G)`, over all `2^q` patterns. -/
def Ztilde {m : ℕ} (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m)) (q Δ : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin q)).powerset,
    (A.card : ℝ) ^ m * ((Finset.univ \ A).card : ℝ) ^ m * colXi G q Δ A

/-- The decay function `g(γ) = (Δ/(10 q² log Δ)) |γ|` of §5.1. -/
def colDecay (q Δ : ℕ) {m : ℕ} (γ : Finset (ExpanderBIS.RandomHardCore.Vertex m)) : ℝ :=
  (Δ : ℝ) / (10 * (q : ℝ) ^ 2 * Real.log Δ) * γ.card

end

end ExpanderBIS.Colorings


