-- Prove2me | Definitions.Def_AgreementTop736_Exact_Supplement_Layers
-- name    : AgreementTop736_Exact_Supplement_Layers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:32.375537+00:00
-- url     : https://prove2.me/theorems/4a7e3734-3b91-4fbd-bdb4-ac95200b08d6
-- title:
--   Finite coherent layered set posets and their uniform subface laws
-- statement:
--   A finite ground set $X$ has face families $P_0,\ldots,P_k$, ordered by containment. Every face in $P_j$ has $q_j$ elements. For $i\le j\le k$, every $j$-face contains exactly $d_{i,j}>0$ faces of $P_i$. Coherence says that for $i\le j\le t\le k$, $B\in P_i$, $C\in P_t$ and $B\subseteq C$,
--   $$\#\{A\in P_j:B\subseteq A\subseteq C\}
--   =\frac{d_{j,t}d_{i,j}}{d_{i,t}}.$$
--   A nonnegative top law $\mu$ is supported on $P_k$ and sums to one. Its tested-layer kernel is
--   $$D_s(S\mid K)=\begin{cases}1/d_{s,k}&K\in P_k,\ S\in P_s,\ S\subseteq K,\\0&\text{otherwise.}\end{cases}$$
--   The induced layer law is $\mu_s(S)=\sum_K\mu(K)D_s(S\mid K)$. The published sampling scheme is instantiated with this kernel, the same top law at every layer, and sizes $N=q_k$, $n=q_s$; its upward kernel and independent conditional-parent test then apply directly.
--
--   The layer data contain no assignments or agreement bounds. They describe the general coherent set posets of the paper, including distributions that vanish on some faces.
--
--   **Formalization Note** Ranks are natural numbers, with only ranks at most $k$ constrained or used. Coherence is encoded after multiplying by the positive integer $d_{i,t}$, so there is no truncated natural division. A scheme here is its data alone: no uniform-inclusion, variance or spectral condition is bundled into the poset. The new theorem does not assume the base scheme's separate validity predicate.
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), p.8, Section 2.2, layered posets, coherence and the displayed kernels. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Model

/-! Kaufman–Pham, STOC 2027 submission #736, §2.2 p.8.
Finite coherent layers of sets, with an arbitrary probability law on their top layer.
These data are independent of the assignments and contain no agreement conclusion. -/

namespace AgreementTop736.Exact.Supplement

open Finset
noncomputable section

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- Layer data on ranks 0,...,k. Values of these functions above k are unused. -/
structure LayeredPoset where
  k : ℕ
  faces : ℕ → Finset (Finset V)
  q : ℕ → ℕ
  d : ℕ → ℕ → ℕ
  μ : Finset V → ℝ

variable {V}

namespace LayeredPoset

/-- The standing assumptions of §2.2. The last coherence identity is the printed
fraction with its positive denominator cleared, so no truncated Nat division is used. -/
structure IsCoherent (P : LayeredPoset V) : Prop where
  face_size : ∀ j, j ≤ P.k → ∀ C ∈ P.faces j, C.card = P.q j
  d_pos : ∀ i j, i ≤ j → j ≤ P.k → 0 < P.d i j
  subface_count : ∀ i j, i ≤ j → j ≤ P.k → ∀ C ∈ P.faces j,
    ((P.faces i).filter (fun B => B ⊆ C)).card = P.d i j
  coherence : ∀ i j t, i ≤ j → j ≤ t → t ≤ P.k →
    ∀ C ∈ P.faces t, ∀ B ∈ P.faces i, B ⊆ C →
      ((P.faces j).filter (fun A => B ⊆ A ∧ A ⊆ C)).card * P.d i t =
        P.d j t * P.d i j
  μ_nonneg : ∀ K, 0 ≤ P.μ K
  μ_sum : ∑ K, P.μ K = 1
  μ_support : ∀ K, 0 < P.μ K → K ∈ P.faces P.k

/-- Uniform s-subface sampling within a top face, zero off the indicated incidence. -/
def down (P : LayeredPoset V) (s : ℕ) (K S : Finset V) : ℝ :=
  if K ∈ P.faces P.k ∧ S ∈ P.faces s ∧ S ⊆ K then 1 / (P.d s P.k : ℝ) else 0

/-- Both tests use the same top law; their marginal, upward law and independent
conditional-parent test are exactly those of the published Scheme. -/
def scheme (P : LayeredPoset V) (s : ℕ) : Scheme V where
  μ := P.μ
  D := P.down s
  N := P.q P.k
  n := P.q s

/-- Induced layer law μ_s(S)=Σ_K μ_k(K)D_s(S|K), as on p.8. -/
def layerMass (P : LayeredPoset V) (s : ℕ) (S : Finset V) : ℝ :=
  (P.scheme s).μH S

end LayeredPoset
end
end AgreementTop736.Exact.Supplement


