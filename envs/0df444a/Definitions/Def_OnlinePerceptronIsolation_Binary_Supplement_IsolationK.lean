-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_IsolationK
-- name    : OnlinePerceptronIsolation_Binary_Supplement_IsolationK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:07:12.3252+00:00
-- url     : https://prove2.me/theorems/5b1a4cfa-c540-4d87-9214-c7a7939a4e72
-- title:
--   Definition 2.2 — isolation and deterministic K-success
-- statement:
--   For signings $\sigma,\tau\in\{-1,+1\}^n$, let $d(\sigma,\tau)$ count their unequal coordinates and put $B_h(\sigma)=\{\tau:d(\sigma,\tau)\le h\}$, for a real radius $h$. A solution is isolated when
--   $$\sigma\in S^h(G,K)\quad\Longleftrightarrow\quad\sigma\in S(G,K),\qquad S(G,K)\cap B_h(\sigma)=\{\sigma\}.$$
--   For a deterministic output map $A$, define
--   $$p_K(A,h)=\mathbb P_{G\sim\mathcal G^{m,n}}\{A(G)\in S^h(G,K)\}.$$
--   The Hamming distance and product Gaussian law are the published ones. Isolation is checked against every feasible signing, and the centre must belong to the ball. Consequently a negative radius has no isolated points. Probabilities use the real value of the canonical Gaussian measure, which is finite, with its outer-measure interpretation for arbitrary sets; no Borel restriction is imposed on $K$ in the two unrestricted K-lemmas.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.2, last sentence; §4.3, printed p. 6, PDF p. 8; K-version applied in §4.3, printed p. 15, PDF p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_SolutionsK
import Definitions.Def_OnlinePerceptronIsolation_Binary_Isolation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Definition 2.2, last sentence: the closed Hamming ball meets the solution set
in exactly its centre, including the membership of the centre in the ball. -/
noncomputable def IsIsolatedK {m n : ℕ} (G : Fin m × Fin n → ℝ)
    (K : Set ℝ) (h : ℝ) (σ : Fin n → ℝ) : Prop :=
  IsSolutionK G K σ ∧ ∀ τ : Fin n → ℝ,
    (IsSolutionK G K τ ∧ (hamming σ τ : ℝ) ≤ h) ↔ τ = σ

/-- Actual Gaussian success probability, with K fixed independently of the matrix. -/
noncomputable def detSuccessK {m n : ℕ}
    (A : Fin n → (Fin m × Fin n → ℝ) → ℝ) (K : Set ℝ) (h : ℝ) : ℝ :=
  (ABPOnline.gaussMat m n).real {G | IsIsolatedK G K h (fun i => A i G)}

end OnlinePerceptronIsolation.Binary.Supplement


