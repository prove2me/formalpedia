-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
-- name    : TreeCorrMatch_ErrorFree_TreePairLaws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:56.3552+00:00
-- url     : https://prove2.me/theorems/93fe550a-20fd-404d-9b32-aae7d86787e8
-- title:
--   Poisson Galton–Watson trees, the tree-pair laws $Q$ and $P$, and the likelihood ratio $L_k$
-- statement:
--   Let $\lambda>0$ and $s\in(0,1]$. A **Poisson Galton–Watson tree** $H$ with offspring mean $\lambda$ starts from a root, and every node independently has a $\mathrm{Poi}(\lambda)$ number of ordered children; $H_k$ is its truncation at depth $k$.
--
--   Under the **independent tree-pair law** $Q$, $H$ and $\tilde H$ are independent Poisson Galton–Watson trees with offspring mean $\lambda$. Under the **correlated tree-pair law** $P$, an intersection tree $H^*$ is a Poisson Galton–Watson tree with offspring mean $\lambda s$; $H$ and $\tilde H$ are obtained from $H^*$ by two conditionally independent augmentations, each adding at every node of $H^*$ an independent $\mathrm{Poi}(\lambda(1-s))$ number of exclusive children, below each of which hangs an independent Poisson Galton–Watson tree with offspring mean $\lambda$. Equivalently, at depth $k+1$ the two roots share $\mathrm{Poi}(\lambda s)$ common children, each the root of an independent correlated pair of depth $k$, and each root has its own $\mathrm{Poi}(\lambda(1-s))$ exclusive children, each the root of an independent Galton–Watson tree of depth $k$.
--
--   For $(t,\tilde t)\in\mathcal Z_k\times\mathcal Z_k$ the **likelihood ratio** is
--
--   $$L_k(t,\tilde t)=\frac{P([H_k]=t,\,[\tilde H_k]=\tilde t)}{Q([H_k]=t,\,[\tilde H_k]=\tilde t)}.$$
--
--   The file also provides the probability that the class pair of a random tree pair lies in a set, and the joint probability of an event of a random tree pair and of independent algorithmic randomness $\omega\sim\nu$, $\sum_{(h,\tilde h)}\mu(h,\tilde h)\,\nu\{\omega: E(h,\tilde h,\omega)\}$.
--
--   **Formalization Note** The laws of the depth-$k$ truncations are built directly as probability mass functions on ordered trees (`gwLaw`, `indepPairLaw`, `corrPairLaw`), with `poi r` the Poisson law of Mathlib's `poissonMeasure`. Only the classes $[H_k]$ enter the statements, so the order in which common and exclusive children are listed is immaterial. Outside $\mathcal Z_k\times\mathcal Z_k$ the ratio is $0/0=0$; inside, $Q>0$.
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 6, §2.3 (PDF p. 8)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_RootedTree

/-!
Poisson Galton–Watson trees truncated at depth `k`, the independent and correlated tree-pair laws
`Q` and `P`, and the likelihood ratio `L_k`.

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), §2.3, p. 6.
-/

namespace TreeCorrMatch.ErrorFree

open MeasureTheory ProbabilityTheory

/-- The Poisson law `Poi(r)` on `ℕ` (a negative `r` is read as `0`). -/
noncomputable def poi (r : ℝ) : PMF ℕ := (poissonMeasure r.toNNReal).toPMF

/-- The law of a list of `c` independent draws from `p`. -/
noncomputable def iidList {α : Type} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | c + 1 => p.bind fun x => (iidList p c).map (x :: ·)

/-- The law of the depth-`k` truncation `H_k` of a Poisson Galton–Watson tree with offspring mean
`λ`: the root has `Poi(λ)` children, each the root of an independent such tree of depth `k - 1`. -/
noncomputable def gwLaw (lam : ℝ) : ℕ → PMF OTree
  | 0 => PMF.pure OTree.leaf
  | k + 1 => (poi lam).bind fun c => (iidList (gwLaw lam k) c).map OTree.node

/-- The independent tree-pair law `Q` of `(H_k, H̃_k)`: two independent depth-`k` truncated Poisson
Galton–Watson trees with offspring mean `λ`. -/
noncomputable def indepPairLaw (lam : ℝ) (k : ℕ) : PMF (OTree × OTree) :=
  (gwLaw lam k).bind fun a => (gwLaw lam k).map fun b => (a, b)

/-- The correlated tree-pair law `P` of `(H_k, H̃_k)`: the intersection tree `H*` is Poisson
Galton–Watson with offspring mean `λs`; in each of two conditionally independent augmentations
every node of `H*` receives an independent `Poi(λ(1 - s))` number of exclusive children, below each
of which hangs an independent Poisson Galton–Watson tree with offspring mean `λ`. Written
recursively: the roots share `Poi(λs)` common children, each the root of an independent correlated
pair of depth `k - 1`, and each root has its own `Poi(λ(1 - s))` exclusive children, each the root
of an independent Galton–Watson tree of depth `k - 1`. -/
noncomputable def corrPairLaw (lam s : ℝ) : ℕ → PMF (OTree × OTree)
  | 0 => PMF.pure (OTree.leaf, OTree.leaf)
  | k + 1 =>
    (poi (lam * s)).bind fun cs =>
    (iidList (corrPairLaw lam s k) cs).bind fun common =>
    (poi (lam * (1 - s))).bind fun c₁ =>
    (iidList (gwLaw lam k) c₁).bind fun ex₁ =>
    (poi (lam * (1 - s))).bind fun c₂ =>
    (iidList (gwLaw lam k) c₂).map fun ex₂ =>
      (OTree.node (common.map Prod.fst ++ ex₁), OTree.node (common.map Prod.snd ++ ex₂))

/-- The probability that a random ordered tree pair with law `μ` has unlabeled classes `(x, y)`. -/
noncomputable def classPairProb (μ : PMF (OTree × OTree)) (x y : UTree) : ℝ :=
  (μ.toOuterMeasure {p | cls p.1 = x ∧ cls p.2 = y}).toReal

/-- The probability that a random ordered tree pair with law `μ` has its pair of unlabeled classes
in the set `F`. -/
noncomputable def classSetProb (μ : PMF (OTree × OTree)) (F : Set (UTree × UTree)) : ℝ :=
  (μ.toOuterMeasure {p | (cls p.1, cls p.2) ∈ F}).toReal

/-- The likelihood ratio `L_k(t, t̃) = P([H_k] = t, [H̃_k] = t̃) / Q([H_k] = t, [H̃_k] = t̃)` on
`Z_k × Z_k`. -/
noncomputable def likelihoodRatio (lam s : ℝ) (k : ℕ) (x y : UTree) : ℝ :=
  classPairProb (corrPairLaw lam s k) x y / classPairProb (indepPairLaw lam k) x y

/-- The joint probability of an event `E` of a random ordered tree pair with law `μ` and of
independent algorithmic randomness `ω ∼ ν`: `∑_{(h, h̃)} μ(h, h̃) · ν{ω : E h h̃ ω}`. -/
noncomputable def pairSeedProb {Ω : Type} [MeasurableSpace Ω] (μ : PMF (OTree × OTree))
    (ν : Measure Ω) (E : OTree → OTree → Ω → Prop) : ℝ :=
  (∑' p : OTree × OTree, μ p * ν {ω | E p.1 p.2 ω}).toReal

end TreeCorrMatch.ErrorFree


