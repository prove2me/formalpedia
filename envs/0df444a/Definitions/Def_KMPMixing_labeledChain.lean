-- Prove2me | Definitions.Def_KMPMixing_labeledChain
-- name    : KMPMixing_labeledChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:10.04476+00:00
-- url     : https://prove2.me/theorems/ea4e9456-2bda-48cf-b3e4-a17201b31e7c
-- title:
--   The labeled KMP chain $M^{(t,G)}_{\mathrm{LKMP}}$ and $\pi_{\mathrm{LKMP}}$
-- statement:
--   A labeled configuration of $t$ particles on $G=(V=[d],E)$ is $x\in\Omega_G=[d]^t$, where $x_\ell$ is the vertex of particle $\ell$; write $\#_i(x)=|\{\ell:x_\ell=i\}|$. The map $x\mapsto(\#_1(x),\dots,\#_d(x))\in\Delta_G$ forgets the labels.
--
--   The labeled KMP chain picks a uniformly random edge $e=\{i,j\}\in E$, sets $m=\#_i(x)+\#_j(x)$, draws $a$ uniformly from $\{0,\dots,m\}$, and sends a uniformly random $a$-subset of the $m$ particles at $i$ or $j$ to $i$ and the rest to $j$. With $S_{ij}(x)=\{\ell:x_\ell\in\{i,j\}\}$, its transition matrix is
--   $$
--   M^{(t,G)}_{\mathrm{LKMP}}(x,x')=\frac1{|E|}\sum_{\{i,j\}\in E}\frac{\mathbb 1[S_{ij}(x)=S_{ij}(x'),\ x'_\ell=x_\ell\ \forall\ell\notin S_{ij}(x)]}{(m+1)\binom{m}{\#_i(x')}}.
--   $$
--   The distribution
--   $$
--   \pi_{\mathrm{LKMP}}(x)=\frac{\prod_{i=1}^d\#_i(x)!}{t!\,\binom{t+d-1}{d-1}}
--   $$
--   is its stationary law (Lemma 3.4).
--
--   The labeled chain carries the conditional product structure used for the mixing bound of the unlabeled chain.
--
--   **Formalization Note** $\Omega_G$ is `Fin t → Fin d`. Edges are averaged over the pairs $(i,j)$ with $i<j$. $t+d-1$ and $d-1$ are natural-number subtractions, which are the paper's values for $d\ge1$.
-- source:
--   Chen et al., arXiv:2609.38044, Eq. (1), p.10; Definition 3.3, p.16 (PDF p.18); Lemma 3.4 and its proof, pp.16–17 (PDF pp.18–19); the map f of the proof of Lemma 3.5, p.17

import Mathlib
import Definitions.Def_KMPMixing_kmpChain

namespace KMPMixing

open MarkovMixing

/-- `#_i(x) = |{ℓ ∈ [t] : x_ℓ = i}|`, the number of particles at vertex `i` in the labeled
configuration `x ∈ Ω_G = [d]^t` (arXiv:2609.38044, Eq. (1), p.10 (PDF p.12), and Definition 3.3,
p.16 (PDF p.18)).

**Formalization Note** A labeled configuration is `x : Fin t → Fin d`: particle `ℓ` sits at
vertex `x ℓ`. -/
def count {d t : ℕ} (x : Fin t → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun ℓ => x ℓ = i).card

/-- The multiplicity vector `(#_1(x), …, #_d(x)) ∈ Δ_G` of a labeled configuration, the map
`f : Ω_G → Δ_G` of the proof of Lemma 3.5 (arXiv:2609.38044, p.17 (PDF p.19)). -/
def unlabel {d t : ℕ} (x : Fin t → Fin d) : State d t :=
  ⟨fun i => count x i, by
    rw [Finset.Nat.mem_antidiagonalTuple]
    unfold count
    rw [← Finset.card_eq_sum_card_fiberwise (fun ℓ _ => Finset.mem_univ (x ℓ))]
    simp⟩

/-- The labeled KMP update on a fixed edge `{i, j}` (arXiv:2609.38044, Definition 3.3, step 2,
p.16 (PDF p.18), and the transition probability in the proof of Lemma 3.4, p.17 (PDF p.19)):
with `S_{ij}(x) = {ℓ : x_ℓ ∈ {i, j}}` and `m = #_i(x) + #_j(x)`, an integer `a` is drawn
uniformly from `{0, …, m}` and a uniformly random `a`-subset of the `m` particles at `i` or `j`
goes to `i`, the rest to `j`. Hence
`L_{ij}(x, x') = 𝟙[S_{ij}(x) = S_{ij}(x'), x_ℓ = x'_ℓ ∀ ℓ ∉ S_{ij}(x)] / ((m + 1) · C(m, #_i(x')))`.

**Formalization Note** Used only for `i ≠ j`; under the indicator `#_i(x') + #_j(x') = m`, so
the kernel is symmetric in `i, j`. -/
noncomputable def labeledEdgeKernel {d t : ℕ} (i j : Fin d) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℝ :=
  fun x x' =>
    if (∀ ℓ, (x ℓ = i ∨ x ℓ = j) ↔ (x' ℓ = i ∨ x' ℓ = j)) ∧
        (∀ ℓ, ¬ (x ℓ = i ∨ x ℓ = j) → x' ℓ = x ℓ) then
      1 / (((count x i + count x j : ℕ) + 1 : ℝ) *
        ((count x i + count x j).choose (count x' i) : ℝ))
    else 0

/-- The transition matrix `M^{(t,G)}_LKMP` of the labeled KMP chain on `Ω_G = [d]^t`
(arXiv:2609.38044, Definition 3.3, p.16 (PDF p.18)): pick a uniformly random edge
`e = {i, j} ∈ E` and apply `labeledEdgeKernel i j`,
`M(x, x') = (1/|E|) Σ_{{i,j} ∈ E} L_{ij}(x, x')`.

**Formalization Note** The average runs over `edgePairs G` (edges with `i < j`). -/
noncomputable def labeledChain {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] (t : ℕ) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℝ :=
  ((edgePairs G).card : ℝ)⁻¹ • ∑ p ∈ edgePairs G, labeledEdgeKernel p.1 p.2

/-- The distribution `π_LKMP(x) = ∏_{i=1}^d #_i(x)! / (t! · C(t + d − 1, d − 1))` on
`Ω_G = [d]^t` (arXiv:2609.38044, Lemma 3.4, p.16 (PDF p.18)).

**Formalization Note** `t + d - 1` and `d - 1` are natural-number subtractions; they are the
paper's values for `d ≥ 1`, and every statement using this definition assumes `d ≥ 2`. -/
noncomputable def labeledStationary (d t : ℕ) : (Fin t → Fin d) → ℝ :=
  fun x => ((∏ i, (count x i).factorial : ℕ) : ℝ) /
    ((t.factorial : ℝ) * ((t + d - 1).choose (d - 1) : ℝ))

end KMPMixing


