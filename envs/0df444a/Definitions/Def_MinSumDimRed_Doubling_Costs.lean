-- Prove2me | Definitions.Def_MinSumDimRed_Doubling_Costs
-- name    : MinSumDimRed_Doubling_Costs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:33:43.485936+00:00
-- url     : https://prove2.me/theorems/6274a046-d315-45ef-8ea7-2b7f9167cc06
-- title:
--   Min-sum costs of sets and their images, $(1\pm\varepsilon)$, the distortion graph (Def. 3.1), $\theta$-everywhere sparse graphs (Def. 3.2) and 1-median centers
-- statement:
--   Points live in $\mathbb R^d$ = `Pt d` = `EuclideanSpace ℝ (Fin d)` with the Euclidean norm. An instance $X = \{p_0, \dots, p_{n-1}\} \subseteq \mathbb R^d$ is an injective family `p : Fin n → Pt d`, and a subset of $X$ is a finite set of indices.
--
--   1. **Distance tables** `eucl p i j` $= \|p_i - p_j\|$ and `imgDist f p i j` $= \|f(p_i) - f(p_j)\|$ for a map $f : \mathbb R^d \to \mathbb R^t$.
--   2. **Cost of a set** (eq. (1), pp. 1–2): `setCost p C` $= \mathrm{cost}(C) = \sum_{x, y \in C} \|x - y\|$ over **ordered** pairs (each unordered pair twice, diagonal terms $0$), via the published `MinSumClust.cost`; `imgSetCost f p C` $= \mathrm{cost}(f(C)) = \sum_{x, y \in C} \|f(x) - f(y)\|$, summed over the points of $C$, so coinciding images are counted with multiplicity (the multisets of p. 3). For a labelling $\sigma$, `MinSumFPT.labCost (eucl p) σ` is $\mathrm{cost}(P)$ and `MinSumFPT.labCost (imgDist f p) σ` is $\mathrm{cost}(f(P))$; `MinSumFPT.optCost (eucl p) k` is $\mathrm{OPT}$.
--   3. **$a \in (1 \pm \varepsilon) b$** `WithinFactor ε a b`: $(1 - \varepsilon) b \le a \le (1 + \varepsilon) b$.
--   4. **Distortion graph** (Definition 3.1, p. 11) `distortionGraph ε f`: the simple graph on $\mathbb R^d$ with $x \sim y$ iff $x \ne y$ and $\|f(x) - f(y)\| \notin (1 \pm \varepsilon)\|x - y\|$ (for $x = y$ the condition never holds, so nothing is lost). The distortion graph of a set $Y$ is its subgraph induced on $Y$.
--   5. **$\theta$-everywhere sparse** (Definition 3.2, p. 11) `IsEverywhereSparseOn G V θ`: the subgraph of $G$ induced on the finite vertex set $V$ satisfies $\deg(u) \le \theta |V|$ for every $u \in V$, the degree counting neighbours inside $V$; $V = \emptyset$ is allowed.
--   6. **1-median center** (p. 12) `IsOneMedianCenter S c`: $c \in \mathbb R^d$ minimises $c' \mapsto \sum_{y \in S} \|y - c'\|$ over all $c' \in \mathbb R^d$, for a finite $S \subseteq \mathbb R^d$.
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), pp. 1–3 (eq. (1), images of partitions), p. 11 (Definitions 3.1, 3.2), p. 12 (1-median)

import Mathlib
import Definitions.Def_MinSumFPT_labCost

namespace MinSumDimRed.Doubling

/-!
# Min-sum costs, the distortion graph, everywhere-sparse graphs and the 1-median

Dallal, Krauthgamer, *Dimension Reduction and Coresets for Min-Sum k-Clustering*,
arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…): eq. (1), pp. 1–2 (min-sum
cost over ordered pairs); p. 3 (images `g(A)`, `g(P)` as multisets); p. 11, Definition 3.1
(distortion graph), Definition 3.2 (θ-everywhere sparse); p. 12 (1-median center).

**Formalization Note.** An instance `X ⊆ ℝ^d` with `n` points is an injective family
`p : Fin n → Pt d`; a set of points of `X` is a `Finset (Fin n)` of indices. The cost of a set
`C` is the published `MinSumClust.cost` (ordered pairs, diagonal included) for the distance
`‖p i - p j‖`, and the cost of its image `f(C)` uses `‖f (p i) - f (p j)‖`, so coinciding images
are counted with multiplicity (the paper's multisets). The k-partition costs `cost(P)`,
`cost(f(P))` and `OPT` are the published `MinSumFPT.labCost` / `MinSumFPT.optCost` for these two
distance tables. -/

/-- Euclidean space `ℝ^d` with the Euclidean norm. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Distance table of the instance: `‖p i - p j‖`. -/
noncomputable def eucl {n d : ℕ} (p : Fin n → Pt d) : Fin n → Fin n → ℝ :=
  fun i j => ‖p i - p j‖

/-- Distance table of the image of the instance under `f`: `‖f (p i) - f (p j)‖`. -/
noncomputable def imgDist {n d t : ℕ} (f : Pt d → Pt t) (p : Fin n → Pt d) :
    Fin n → Fin n → ℝ :=
  fun i j => ‖f (p i) - f (p j)‖

/-- `cost(C) = ∑_{x,y ∈ C} ‖x - y‖` (ordered pairs) for a set `C` of points of the instance. -/
noncomputable def setCost {n d : ℕ} (p : Fin n → Pt d) (C : Finset (Fin n)) : ℝ :=
  MinSumClust.cost (eucl p) C

/-- `cost(f(C)) = ∑_{x,y ∈ C} ‖f(x) - f(y)‖` (ordered pairs, over the points of `C`). -/
noncomputable def imgSetCost {n d t : ℕ} (f : Pt d → Pt t) (p : Fin n → Pt d)
    (C : Finset (Fin n)) : ℝ :=
  MinSumClust.cost (imgDist f p) C

/-- `a ∈ (1 ± ε) b`: the closed interval `(1 - ε) b ≤ a ≤ (1 + ε) b`. -/
def WithinFactor (ε a b : ℝ) : Prop :=
  (1 - ε) * b ≤ a ∧ a ≤ (1 + ε) * b

/-- Definition 3.1: the distortion graph of a map `f` at accuracy `ε`: `x ~ y` iff
`‖f(x) - f(y)‖ ∉ (1 ± ε)‖x - y‖` (and `x ≠ y`; for `x = y` the condition never holds). -/
def distortionGraph {d t : ℕ} (ε : ℝ) (f : Pt d → Pt t) : SimpleGraph (Pt d) where
  Adj x y := x ≠ y ∧ ¬ WithinFactor ε ‖f x - f y‖ ‖x - y‖
  symm := ⟨fun x y h => by
    refine ⟨h.1.symm, ?_⟩
    rw [← norm_neg (f y - f x), neg_sub, ← norm_neg (y - x), neg_sub]
    exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- Definition 3.2 applied to an induced subgraph: the subgraph `G[V]` of `G` induced on the
finite vertex set `V` is `θ`-everywhere sparse, i.e. every `u ∈ V` has at most `θ |V|`
neighbours in `V`. (`V = ∅` is allowed.) -/
def IsEverywhereSparseOn {β : Type*} (G : SimpleGraph β) (V : Finset β) (θ : ℝ) : Prop :=
  ∀ u ∈ V, (((V.filter (fun v => G.Adj u v)).card : ℕ) : ℝ) ≤ θ * (V.card : ℝ)

/-- `c` is an optimal center of the finite set `S ⊆ ℝ^d` for the 1-median objective
`c ↦ ∑_{y ∈ S} ‖y - c‖`, minimised over all of `ℝ^d`. -/
def IsOneMedianCenter {d : ℕ} (S : Finset (Pt d)) (c : Pt d) : Prop :=
  ∀ c' : Pt d, ∑ y ∈ S, ‖y - c‖ ≤ ∑ y ∈ S, ‖y - c'‖

end MinSumDimRed.Doubling


