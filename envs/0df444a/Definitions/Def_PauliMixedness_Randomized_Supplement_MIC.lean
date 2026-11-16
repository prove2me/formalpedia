-- Prove2me | Definitions.Def_PauliMixedness_Randomized_Supplement_MIC
-- name    : PauliMixedness_Randomized_Supplement_MIC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:54:52.601822+00:00
-- url     : https://prove2.me/theorems/466ac381-bd8c-4ed1-8f84-2325d4f8b9c0
-- title:
--   Measurement information channel and traceless Schatten norms
-- statement:
--   For a finite POVM $M$, its measurement information channel acts on every complex matrix by
--
--   $$L_M(A)=\sum_{x:\operatorname{Tr}M_x\ne0}\frac{\operatorname{Tr}(M_xA)}{\operatorname{Tr}M_x}M_x.$$
--
--   Zero-trace effects are zero and are omitted. Use the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}(A^\dagger B)$. The operator norm on the traceless subspace is the supremum of $\operatorname{Re}\langle A,L_M(A)\rangle$ over traceless $A$ with $\langle A,A\rangle=1$. The trace norm there is
--
--   $$t_M=\sum_{x:\operatorname{Tr}M_x\ne0}\frac{\operatorname{Tr}(M_x^2)}{\operatorname{Tr}M_x}-1.$$
--
--   This is the sum of the channel's nonnegative eigenvalues after removing the identity eigenvalue. The class quantities $o_{\mathcal M}$ and $t_{\mathcal M}$ are the separate suprema of these two norms over $M\in\mathcal M$. Each defining supremum includes zero, so the empty class and the zero-dimensional traceless space have norm zero. POVM positivity and normalization imply the bounds $0\le o_M\le1$ and $0\le t_M\le2^N-1$; the real suprema cannot be unbounded.
--
--   This implements the traceless-subspace reading used in the lower-bound statement, rather than a norm on state matrices or on channel entries.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Definition 3.1 p.10; Theorem 1.3 p.3; Eq. (8) p.20

import Definitions.Def_PauliMixedness_Randomized_Supplement_Measurements

noncomputable section
open scoped BigOperators

namespace PauliMixedness.Randomized.Supplement

/-- Definition 3.1 p.10, on arbitrary complex matrices. A zero-trace PSD effect
is zero, so its undefined fraction is omitted explicitly. -/
def measurementInformationChannel {N : ℕ} (M : FinitePOVM N)
    (A : Operator N) : Operator N :=
  ∑ x, if (M.effect x).trace = 0 then 0 else
    (((M.effect x * A).trace / (M.effect x).trace) • M.effect x)

/-- Squared Hilbert--Schmidt norm, not an entrywise or matrix row-sum norm. -/
def hsNormSq {N : ℕ} (A : Operator N) : ℝ := (A.conjTranspose * A).trace.re

/-- Largest MIC eigenvalue on the complex traceless Hilbert--Schmidt space.
The MIC is self-adjoint PSD there, so the unit Rayleigh supremum is its
operator norm. Including zero also defines the zero-dimensional case correctly. -/
def micOpNorm {N : ℕ} (M : FinitePOVM N) : ℝ :=
  sSup ({0} ∪ {v : ℝ | ∃ A : Operator N,
    A.trace = 0 ∧ hsNormSq A = 1 ∧
      v = (A.conjTranspose * measurementInformationChannel M A).trace.re})

/-- Sum of MIC eigenvalues on the traceless space: subtract the identity
eigenvalue 1. Zero effects contribute zero; no rank restriction is imposed. -/
def micTraceNorm {N : ℕ} (M : FinitePOVM N) : ℝ :=
  (∑ x, if (M.effect x).trace = 0 then 0 else
    (M.effect x * M.effect x).trace.re / (M.effect x).trace.re) - 1

/-- Separate suprema over the measurement class, each including zero.
For finite POVMs the op values lie in [0,1], trace values in [0,2^N-1];
thus these real suprema are bounded, including for empty classes. -/
def classOpNorm {N : ℕ} (M : Set (FinitePOVM N)) : ℝ :=
  sSup ({0} ∪ micOpNorm '' M)

def classTraceNorm {N : ℕ} (M : Set (FinitePOVM N)) : ℝ :=
  sSup ({0} ∪ micTraceNorm '' M)

end PauliMixedness.Randomized.Supplement


