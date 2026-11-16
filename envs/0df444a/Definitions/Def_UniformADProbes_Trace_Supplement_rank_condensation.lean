-- Prove2me | Definitions.Def_UniformADProbes_Trace_Supplement_rank_condensation
-- name    : UniformADProbes_Trace_Supplement_rank_condensation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:03.925359+00:00
-- url     : https://prove2.me/theorems/35e2ff14-0187-4700-a7b8-926a068356db
-- title:
--   Appendix A.1 — Fixed rank-condensation probes
-- statement:
--   Let $N\ge2$, $M=N(N+1)/2$, and let $U_0,\ldots,U_{M-1}$ be the published probes in lexicographic order, with $U_0=1$. Set $R=(3N^3)^{N-1}$. The fixed integers and polynomials are
--   $$
--   H_0=(M-1)R\,2^{(N-2)(M-2)},\qquad
--   \tau=N!H_0^{N-1}+2,\qquad
--   Z_0=1,\quad Z_{j+1}=\sum_{i=1}^{M-1}(2^j\tau)^{i-1}U_i.
--   $$
--   For a tree $T$ on $n$ vertices, $\mathcal M_T$ is the published real cyclic module of $(A_T,D_T)$ from the all-ones vector, including the empty word, and $z_i=Z_i(A_T,D_T)\mathbf1$. The sum excludes $U_0$. These definitions provide the exact fixed family in Lemma A.1; no input-dependent basis selection occurs.
--
--   **Formalization Note** Indices are zero-based. Missing list entries default to zero; every index used for the source range is present. The functions are total outside $N\ge2$, where the source gives no claim. In the rendered PDF, $R$ multiplies a power of two; the structured planning brief misread this as a power of $R$. The PDF formula is retained.
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Appendix A.1, equation (13), p. 11 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
noncomputable section

namespace UniformADProbes.Trace.Supplement

/-- Appendix A.1, rendered PDF p.12: R times a power of TWO. -/
def condensationH0 (N : ℕ) : ℕ :=
  let M := N * (N + 1) / 2
  let R := (3 * N^3)^(N - 1)
  (M - 1) * R * 2^((N - 2) * (M - 2))

def condensationTau (N : ℕ) : ℕ :=
  Nat.factorial N * (condensationH0 N)^(N - 1) + 2

/-- Equation (13). Only indices 0,...,N-1 are used in the statements. -/
def condensedProbe (N : ℕ) : ℕ → NCPoly
  | 0 => 1
  | j + 1 =>
    ((List.range ((probeList N).length - 1)).map fun i =>
      (((2^j * condensationTau N)^i : ℕ) : ℤ) •
        ((probeList N)[i + 1]?.getD 0)).sum

def treeModule {n : ℕ} (T : SimpleGraph (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  cyclicModule (realMatrix (adjacency T)) (realMatrix (degreeMatrix T)) (ones n)

def condensedResponse {n : ℕ} (N : ℕ) (T : SimpleGraph (Fin n))
    (i : ℕ) : Fin n → ℝ :=
  (polyEval (realMatrix (adjacency T)) (realMatrix (degreeMatrix T))
    (condensedProbe N i)).mulVec (ones n)

end UniformADProbes.Trace.Supplement


