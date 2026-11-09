-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling
-- name    : ThinningSprinkling306_ToughCycles_Sprinkling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:10.077027+00:00
-- url     : https://prove2.me/theorems/5f319212-77c1-4fed-ab9f-9a8b0537d3fe
-- title:
--   Independent sprinkling rounds and exposed unions
-- statement:
--   For sets $U_0,U_1,\ldots$, the exposed set at time $i$ is $W_i=\bigcup_{j=0}^i U_j$. The graph at that time is the actual induced graph $G[W_i]$.
--
--   For integer $k$ and real $p,t$ define
--   $$
--   m=\left\lfloor\frac{kp^2t}{128}\right\rfloor,\qquad q=\frac{16}{kpt}.
--   $$
--   The sprinkling law samples $U_0$ with parameter $p/4$ and $U_1,\ldots,U_m$ independently with parameter $q$. The final sprinkling in Claim 2 is a fresh independent $p/8$-random set. The floor reading makes the suppressed round count integral and preserves $mq\le p/8$ once parameters are positive.
--
--   This is the probability law and its unions, not an assumption that unexplored variables remain independent. Exploration and conditional-probability arguments remain proof obligations. The asymptotic regime ensures positive round count and $q\le1$ eventually.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 9, proof of Lemma 4.2; Section 2, p. 5 (PDF p. 7) (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths
import Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling

namespace ThinningSprinkling306.ToughCycles

/-- W_i is the union of the sets exposed through round i. -/
noncomputable def exposed {n : ℕ} (U : ℕ → Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  (Finset.range (i + 1)).biUnion U

noncomputable def roundCount (k : ℕ) (p t : ℝ) : ℕ := ⌊(k : ℝ) * p ^ 2 * t / 128⌋₊

noncomputable def roundProbability (k : ℕ) (p t : ℝ) : ℝ := 16 / ((k : ℝ) * p * t)

noncomputable def sprinklingProbability {n : ℕ} (k : ℕ) (p t : ℝ)
    (E : (Fin (roundCount k p t + 1) → Finset (Fin n)) → Prop) : ℝ :=
  independentProbability
    (fun i : Fin (roundCount k p t + 1) =>
      if i.val = 0 then p / 4 else roundProbability k p t) E

noncomputable def sprinklingUnion {n m : ℕ}
    (U : Fin (m + 1) → Finset (Fin n)) : Finset (Fin n) := Finset.univ.biUnion U

end ThinningSprinkling306.ToughCycles


