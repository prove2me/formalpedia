-- Prove2me | Definitions.Def_DetPermanentApprox_Main_Parameters
-- name    : DetPermanentApprox_Main_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:59.159901+00:00
-- url     : https://prove2.me/theorems/c9972745-d116-4ba2-8381-61aebe9ed65a
-- title:
--   Dyadic precision, rounded matrices, and the optimization box
-- statement:
--   For precision $s$, set $\alpha=2^{-s}$, $\eta=\alpha/16$, $\delta=\eta/(s+1)$, $t=1-\delta$, and $K=4\delta^{-2}$. For dimension $n$ and grid parameter $p$, set $R_0=2n^2(n+p)/\delta$ and $h=\eta/(64n^2)$. Rounded data are rational matrices in $[0,1]$, on the $2^{-p}$ grid, with permanent at least one and with every support edge extendable to a perfect matching.
--
--   The objective uses exactly the previously defined polynomial $U$, evaluated on the field-rescaled support weights of $C$, minus $t$ times the field sum. The box is the coordinate interval $[-R_0,R_0]^{2n}$, and clipping is coordinatewise. Scaling and minimization inputs have fixed layouts; $U,t,\eta$ are computed from the supplied data rather than supplied with correctness certificates.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), §4 and Appendix A, pp. 20–25, equations (4.1)–(4.2) (PDF pp. 20–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_PolynomialComputation

namespace DetPermanentApprox.Main

def alpha (s : ℕ) : ℚ := 1 / (2 : ℚ) ^ s
def eta (s : ℕ) : ℚ := alpha s / 16
def delta (s : ℕ) : ℚ := eta s / (s + 1)
def targetMarginal (s : ℕ) : ℚ := 1 - delta s
def degreeCutoff (s : ℕ) : ℚ := 4 / delta s ^ 2
def boxRadius (n p s : ℕ) : ℚ := 2 * (n : ℚ) ^ 2 * (n + p) / delta s
def stepSize (n s : ℕ) : ℚ := eta s / (64 * (n : ℚ) ^ 2)

def realMatrix {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (C i j : ℝ)

def RoundedData {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) : Prop :=
  (∀ i j, 0 ≤ C i j ∧ C i j ≤ 1) ∧
    (∀ i j, ∃ k : ℕ, C i j = k / (2 : ℚ) ^ p) ∧
    1 ≤ (realMatrix C).permanent ∧ TotalSupport (realMatrix C)

noncomputable def matrixSurrogate {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ) :
    Poly (Support (realMatrix C)) :=
  surrogate (supportGraph (realMatrix C)) (degreeCutoff s) (eta s : ℝ)

noncomputable def surrogateObjective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ)
    (θ : Vertex n → ℝ) : ℝ :=
  evaluate (matrixSurrogate C s)
    (fieldWeights (supportGraph (realMatrix C)) (supportWeights (realMatrix C)) θ) -
      (targetMarginal s : ℝ) * ∑ v, θ v

open Classical in
noncomputable def vertexDegree {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (θ : Vertex n → ℝ) (v : Vertex n) : ℝ :=
  ∑ e : Support (realMatrix C), if Incident (supportGraph (realMatrix C)) v e then
    fieldWeights (supportGraph (realMatrix C)) (supportWeights (realMatrix C)) θ e else 0

def box (n p s : ℕ) : Set (Vertex n → ℝ) :=
  {θ | ∀ v, |θ v| ≤ (boxRadius n p s : ℝ)}

noncomputable def clip (n p s : ℕ) (θ : Vertex n → ℚ) : Vertex n → ℚ :=
  fun v => min (boxRadius n p s) (max (-boxRadius n p s) (θ v))

def scaleInput {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : List ℝ :=
  matrixInput A ++ [(alpha s : ℝ)]

def rationalScaleInput {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (s : ℕ) : List ℚ :=
  rationalMatrixInput A ++ [alpha s]

/-- The polynomial U and t,η are computed from C,s; their definitions are not
certificates supplied as input. Construction of U is included in the cost theorem. -/
def minimizationInput {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p s : ℕ) : List ℝ :=
  matrixInput (realMatrix C) ++ [(p : ℝ), (s : ℝ)]

end DetPermanentApprox.Main


