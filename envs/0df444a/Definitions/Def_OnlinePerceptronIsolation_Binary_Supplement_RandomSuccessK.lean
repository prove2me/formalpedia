-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RandomSuccessK
-- name    : OnlinePerceptronIsolation_Binary_Supplement_RandomSuccessK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:07:50.461854+00:00
-- url     : https://prove2.me/theorems/cf18040e-9f49-4e83-945a-b2095c4ba323
-- title:
--   Randomized success for general perceptrons
-- statement:
--   Let $(\Xi,\nu)$ be any seed probability space, independent of $G\sim\mathcal G^{m,n}$. For a seed-indexed signing map $A$, set
--   $$p_K(\nu,A,h)=\mathbb P_{(\xi,G)\sim\nu\otimes\mathcal G^{m,n}}\{A(\xi,G)\in S^h(G,K)\}.$$
--   The algorithm class is the published jointly measurable randomized-online predicate, with each fixed seed giving a measurable deterministic online map. Fixing $K$ outside the map restricts no algorithm for that input set. Arbitrary seed spaces and laws are allowed. The probability is the real value of the product measure (outer measure on arbitrary sets); the well-separated inputs of Theorem 3.2 are Borel. No success property is built into the algorithm class.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.3, last sentence; §4.3, printed p. 15, PDF p. 17; Definition 2.3 printed p. 6, PDF p. 8; averaging Eqs. (A.60)–(A.61), printed p. 24, PDF p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_IsolationK
import Definitions.Def_OnlinePerceptronIsolation_Binary_RandomizedOnline
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- The independent seed law is unrestricted; online maps use the published predicate. -/
noncomputable def randomSuccessK {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    {m n : ℕ} (A : Ξ → Fin n → (Fin m × Fin n → ℝ) → ℝ)
    (K : Set ℝ) (h : ℝ) : ℝ :=
  (ν.prod (ABPOnline.gaussMat m n)).real
    {p | IsIsolatedK p.2 K h (fun i => A p.1 i p.2)}

end OnlinePerceptronIsolation.Binary.Supplement


