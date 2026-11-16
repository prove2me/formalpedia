-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_MismatchSuccessK
-- name    : OnlinePerceptronIsolation_Binary_Supplement_MismatchSuccessK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:36.908228+00:00
-- url     : https://prove2.me/theorems/1252b076-16bf-49ab-be02-cbe2a79d5d9d
-- title:
--   Section 4.3 — successful output mismatching its suffix baseline
-- statement:
--   For a deterministic online map $A$, a set $K$, a real radius $h$ and a suffix length $r$, define
--   $$q_K(A,h,r)=\mathbb P_G\{A(G)\in S^h(G,K),\ A(G)\ne A^{(r)}(G)\}.$$
--   Here $A^{(r)}$ is the published suffix-parallel baseline: it keeps the committed prefix and signs each suffix column with the decision the original algorithm would make if that column arrived immediately after the prefix. The function is computed from $A$ and $G$, and $r$ is chosen before sampling $G$. This is the exact mismatch event used by the K-version of Lemma 4.1; it is not an assumed error bound.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), §4.3, K-version of Eqs. (4.1)–(4.2), printed p. 15, PDF p. 17; original events printed p. 12, PDF p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_IsolationK
import Definitions.Def_OnlinePerceptronIsolation_Binary_SuffixBaseline
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Section 4.3's K-version of Success intersected with the complement of Match_r. -/
noncomputable def mismatchSuccessK {m n : ℕ}
    (A : Fin n → (Fin m × Fin n → ℝ) → ℝ) (K : Set ℝ) (h : ℝ) (r : ℕ) : ℝ :=
  (ABPOnline.gaussMat m n).real
    {G | IsIsolatedK G K h (fun i => A i G) ∧
      (fun i => A i G) ≠ suffixBaseline A r G}

end OnlinePerceptronIsolation.Binary.Supplement


