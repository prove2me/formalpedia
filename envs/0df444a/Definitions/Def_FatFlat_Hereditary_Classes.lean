-- Prove2me | Definitions.Def_FatFlat_Hereditary_Classes
-- name    : FatFlat_Hereditary_Classes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:43:28.811493+00:00
-- url     : https://prove2.me/theorems/97ff7acb-3543-414a-8a6d-677f15ccb2fd
-- title:
--   Drill-flatness of a graph; ISMF, FSMF, drill-flat and pattern-free graph classes
-- statement:
--   - A graph $G$ is **$(\alpha,\beta)$-drill-flat with overhead $N:\mathbb N\to\mathbb N$ and budget $s\in\mathbb N$** if for every $m\in\mathbb N$ and $A\subseteq V(G)$ with $|A|\ge N(m)$ there are $B\subseteq A$ with $|B|=m$ and $X\subseteq V(G)$ with $|X|\le s$ such that $B$ is $(\alpha,\mathrm{Ball}_G(X,\beta))$-scattered.
--   - A class $\mathcal C$ is **induced-shallow-minor-free (ISMF)** if for every $d\in\mathbb N$ there is a graph $H_d$ that no $G\in\mathcal C$ contains as a $d$-shallow induced minor.
--   - $\mathcal C$ is **fat-shallow-minor-free (FSMF)** if there is an integer $\delta\ge1$ such that for every $\alpha\in\mathbb N$ there is a graph $H_\alpha$ that no $G\in\mathcal C$ contains as an $\alpha$-shallow $\delta$-fat minor.
--   - $\mathcal C$ is **drill-flat** if there is $\beta\ge1$ such that for every $\alpha\ge1$ there are $N:\mathbb N\to\mathbb N$ and $s\in\mathbb N$ such that every $G\in\mathcal C$ is $(\alpha,\beta)$-drill-flat with overhead $N$ and budget $s$ ($N$ and $s$ do not depend on $G$).
--   - $\mathcal C$ is **pattern-free** if for every $r\ge3$ there is $k\in\mathbb N$ such that no $G\in\mathcal C$ contains $K(r,k)$ or $W(r,k)$ as an induced subgraph.
--
--   **Formalization Note.** The excluded graphs $H_d$, $H_\alpha$ are taken on a vertex type $\mathrm{Fin}\,n$; since containment as a (fat) shallow minor is invariant under isomorphism, this is every finite graph.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Definition 1.1 p. 3 (PDF 5) with §2.4 p. 10 (PDF 12), Definitions 3.1–3.3 p. 11 (PDF 13), Theorem 1.2 (4) p. 3 (PDF 5). PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- `G` is **`(α, β)`-drill-flat with overhead `N` and budget `s`** (Definition 1.1, p. 3, in
the unweighted form of §2.4, p. 10): for every `m ∈ ℕ` and every vertex set `A` with
`|A| ≥ N(m)` there are `B ⊆ A` with `|B| = m` and a vertex set `X` with `|X| ≤ s` such that `B`
is `(α, Ball_G(X, β))`-scattered. -/
def IsDrillFlat {V : Type} (G : SimpleGraph V) (α β : ℕ) (N : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (m : ℕ) (A : Finset V), N m ≤ A.card →
    ∃ B : Finset V, B ⊆ A ∧ B.card = m ∧
      ∃ X : Finset V, X.card ≤ s ∧ IsScatteredOff G α (ball G (X : Set V) β) (B : Set V)

/-- **ISMF** (Definition 3.1, p. 11): for every `d ∈ ℕ` there is a (finite) graph `H_d` that no
graph of `C` contains as a `d`-shallow induced minor. -/
def ISMF (C : GraphClass) : Prop :=
  ∀ d : ℕ, ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), C V G → ¬ IsShallowInducedMinor H G d

/-- **FSMF** (Definition 3.2, p. 11): there is an integer `δ ≥ 1` such that for every `α ∈ ℕ`
there is a (finite) graph `H_α` that no graph of `C` contains as an `α`-shallow `δ`-fat
minor. -/
def FSMF (C : GraphClass) : Prop :=
  ∃ δ : ℕ, 1 ≤ δ ∧ ∀ α : ℕ, ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), C V G → ¬ IsShallowFatMinor H G α δ

/-- **Drill-flat class** (Definition 3.3, p. 11): there is a drill radius `β ≥ 1` such that for
every scatter radius `α ≥ 1` there are `N : ℕ → ℕ` and `s ∈ ℕ` such that every graph of `C` is
`(α, β)`-drill-flat with overhead `N` and budget `s` (`N`, `s` do not depend on the graph). -/
def DrillFlat (C : GraphClass) : Prop :=
  ∃ β : ℕ, 1 ≤ β ∧ ∀ α : ℕ, 1 ≤ α → ∃ (N : ℕ → ℕ) (s : ℕ),
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), C V G → IsDrillFlat G α β N s

/-- **Pattern-free** (Theorem 1.2 (4), p. 3): for every `r ≥ 3` there is `k ∈ ℕ` such that no
graph of `C` contains `K(r, k)` or `W(r, k)` as an induced subgraph. -/
def PatternFree (C : GraphClass) : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ k : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), C V G →
    IsEmpty (subdividedClique r k ↪g G) ∧ IsEmpty (web r k ↪g G)

end FatFlat.Hereditary


