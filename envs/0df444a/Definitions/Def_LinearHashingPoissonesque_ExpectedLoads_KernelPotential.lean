-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_KernelPotential
-- name    : LinearHashingPoissonesque_ExpectedLoads_KernelPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:01:13.136191+00:00
-- url     : https://prove2.me/theorems/0309056c-e6e2-4d38-883a-9767f86c0118
-- title:
--   Centered coset potentials and the next-vector sample space
-- statement:
--   For binary vectors $\mathbb F_2^u$ and a tuple $v=(v_1,\ldots,v_i)$, put $V_i=\operatorname{span}(v_1,\ldots,v_i)$, with $V_0=\{0\}$. For $S\subseteq\mathbb F_2^u$ and real $\lambda$, define
--
--   $$\overline S_i(x)=|(x+V_i)\cap S|-\frac{|S|}{2^{u-i}},\qquad \Phi_i(S;\lambda;v)=\frac1{2^u}\sum_{x\in\mathbb F_2^u}\exp(\lambda\overline S_i(x)).$$
--
--   The next vector is sampled uniformly from $\mathbb F_2^u\setminus V_i$. The potential after appending that vector uses $i+1$ in its center. The objects here are explicit counts and exponential sums, not a sequence characterized by an assumed recurrence. Lemma 2 uses linearly independent tuples with $i<u$, making the next-vector sample space nonempty.
--
--   **Formalization Note** Binary coordinate vectors are `Fin u → ZMod 2`. Membership in $x+V_i$ is tested by $s-x\in V_i$. Natural subtraction in the exponent is used only with $i\le u$ in the theorem.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.10, Section 3, definitions preceding Lemma 2; p.8, span convention; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Mathlib

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Section 2, p.8, and Section 3, p.10: binary coordinate vectors. -/
abbrev BinaryVector (u : ℕ) := Fin u → ZMod 2

/-- Span of the already fixed tuple. At i = 0 this is {0}. -/
noncomputable def tupleSpan {u i : ℕ} (v : Fin i → BinaryVector u) :
    Submodule (ZMod 2) (BinaryVector u) :=
  Submodule.span (ZMod 2) (Set.range v)

/-- The source's centered coset count, with the center changing with i. -/
noncomputable def centeredCosetLoad {u i : ℕ} (S : Finset (BinaryVector u))
    (v : Fin i → BinaryVector u) (x : BinaryVector u) : ℝ := by
  classical
  exact ((S.filter (fun s => s - x ∈ tupleSpan v)).card : ℝ) -
    (S.card : ℝ) / (2 : ℝ) ^ (u - i)

/-- The actual exponential potential Φ_i, not an abstract recurrence. -/
noncomputable def kernelPotential {u i : ℕ} (S : Finset (BinaryVector u))
    (lam : ℝ) (v : Fin i → BinaryVector u) : ℝ :=
  (∑ x : BinaryVector u, Real.exp (lam * centeredCosetLoad S v x)) / (2 : ℝ) ^ u

/-- Uniform conditional sample space F₂^u \ span(v). -/
noncomputable def nextVectors {u i : ℕ} (v : Fin i → BinaryVector u) :
    Finset (BinaryVector u) := by
  classical
  exact Finset.univ.filter (fun w => w ∉ tupleSpan v)

end LinearHashingPoissonesque.ExpectedLoads


