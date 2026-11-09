-- Prove2me | Definitions.Def_RGGThreshold_InE
-- name    : RGGThreshold_InE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:04.772069+00:00
-- url     : https://prove2.me/theorems/4bdffb9b-d05f-40a4-ba4b-27309284ee12
-- title:
--   The pseudorandomness event $\mathcal E(K^{\mathcal E})$ on graphs
-- statement:
--   Let $K>0$ and let $H$ be a graph on $[n]$ with adjacency matrix $A$. Then $H\in\mathcal E$ when:
--
--   1. for $k\in\{1,2\}$ and distinct $s_1,\dots,s_k\in[n]$: $\displaystyle\sum_{1\le i\le n}|A_{s_1i}-p|\cdots|A_{s_ki}-p|\le Kp^kn$;
--   2. for $k\in\{1,2\}$, every interval $I=[s+1,\dots,n]$ and distinct $s_1,\dots,s_k$: $\displaystyle\Big|\sum_{i\in I}(A_{s_1i}-p)\cdots(A_{s_ki}-p)\Big|\le K\sqrt{p^kn\log n}$;
--   3. $\|A-pJ\|_{op}\le K\sqrt{np}$;
--   4. for every $s\in[n]$: $\displaystyle\sum_{s<i<j\le n}\big|(A_{si}-p)(A_{sj}-p)(A_{ij}-p)\big|\le Kp^3n^2$.
--
--   These are the degree, codegree and spectral regularity conditions under which the main estimate is proved; Lemma 2.3 shows that the random geometric graph satisfies them with high probability.
--
--   **Formalization Note** Only the conditions on $A$ are encoded; the paper's "which implies" forms in $\lambda$ are consequences. The diagonal entries $A_{ss}=0$ enter (1) and (2) literally, as $|0-p|=p$. $\|\cdot\|_{op}$ is the $\ell^2\to\ell^2$ operator (spectral) norm, the published `HighDimProb.QuadraticForms.opNorm`. The intervals are $\{i: s\le i\}$ for $0\le s<n$ in 0-based labels.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Definition 2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_RGGThreshold_centredAdj
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm

namespace RGGThreshold

/-- The pseudorandomness event `𝓔 = 𝓔(K^𝓔)` on graphs (Hunter–Milojević–Sudakov,
arXiv:2607.22480, held version, sha256 1a398ef9…, Definition 2.2, p.9 (PDF p.11)). With `A` the
adjacency matrix of `H`, `H ∈ 𝓔` when:

* (i) for `k ∈ {1, 2}` and distinct `s₁, …, s_k`: `∑_{i} |A_{s₁i}-p| ⋯ |A_{s_k i}-p| ≤ K p^k n`;
* (ii) for `k ∈ {1, 2}`, every interval `I = [s+1, …, n]` and distinct `s₁, …, s_k`:
  `|∑_{i ∈ I} (A_{s₁i}-p) ⋯ (A_{s_k i}-p)| ≤ K √(p^k n log n)`;
* (iii) `‖A - pJ‖_op ≤ K √(np)`;
* (iv) for every `s`: `∑_{s<i<j} |(A_{si}-p)(A_{sj}-p)(A_{ij}-p)| ≤ K p³ n²`.

**Formalization Note** Only the conditions on `A` are encoded; the paper's "which implies" forms
in `λ` are consequences. Vertices are `Fin n`, so the paper's `[s+1, …, n]` is
`tailSet n s = {i | s ≤ i}` for `0 ≤ s < n`. The diagonal `A_{ss} = 0` enters (i) and (ii) as
`|0 - p| = p`, literally. `‖·‖_op` is the `ℓ² → ℓ²` operator (spectral) norm, the published
`HighDimProb.QuadraticForms.opNorm`. -/
def InE (K : ℝ) (n : ℕ) (p : ℝ) (H : SimpleGraph (Fin n)) : Prop :=
  (∀ s₁ : Fin n, ∑ i, |centredAdj p H s₁ i| ≤ K * p * n) ∧
  (∀ s₁ s₂ : Fin n, s₁ ≠ s₂ →
    ∑ i, |centredAdj p H s₁ i| * |centredAdj p H s₂ i| ≤ K * p ^ 2 * n) ∧
  (∀ s : ℕ, s < n → ∀ s₁ : Fin n,
    |∑ i ∈ tailSet n s, centredAdj p H s₁ i| ≤ K * Real.sqrt (p * n * Real.log n)) ∧
  (∀ s : ℕ, s < n → ∀ s₁ s₂ : Fin n, s₁ ≠ s₂ →
    |∑ i ∈ tailSet n s, centredAdj p H s₁ i * centredAdj p H s₂ i| ≤
      K * Real.sqrt (p ^ 2 * n * Real.log n)) ∧
  HighDimProb.QuadraticForms.opNorm (Matrix.of fun i j => centredAdj p H i j) ≤
    K * Real.sqrt (n * p) ∧
  (∀ s : Fin n, ∑ i, ∑ j,
    (if s < i ∧ i < j then |centredAdj p H s i * centredAdj p H s j * centredAdj p H i j| else 0)
      ≤ K * p ^ 3 * n ^ 2)

end RGGThreshold


