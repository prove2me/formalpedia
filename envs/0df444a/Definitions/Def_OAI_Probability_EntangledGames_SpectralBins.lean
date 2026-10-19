-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
-- name    : OAI_Probability_EntangledGames_SpectralBins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:56:02.780023+00:00
-- url     : https://prove2.me/theorems/d3de845e-ff22-4946-9654-6a43c0745d93
-- title:
--   Randomly shifted logarithmic spectral bins: bin weights, bin projections and the spectral envelope
-- statement:
--   Fix a bin width $\varepsilon$ and a shift $s$ (real numbers; the intended range is $0<\varepsilon\le 1$ and $s\in[0,1]$). A positive real $a$ receives the integer bin label
--   $$\ell_{\varepsilon,s}(a)=\Bigl\lfloor\frac{\log a}{\varepsilon}+s\Bigr\rfloor\in\mathbb{Z},$$
--   so that for $\varepsilon>0$ bin $\ell$ consists of the reals $a$ with $e^{\varepsilon(\ell-s)}\le a<e^{\varepsilon(\ell+1-s)}$. The file defines the following scalar and matrix quantities.
--
--   1. **Separation indicator.** For $u,v,s\in\mathbb{R}$: $\operatorname{sep}(u,v,s)=0$ if $\lfloor u+s\rfloor=\lfloor v+s\rfloor$, and $1$ otherwise.
--   2. **Bin envelope.** For $a,b\in\mathbb{R}$: $\beta_{\varepsilon,s}(a,b)=(a-b)^2+2ab\,\operatorname{sep}\bigl(\tfrac{\log a}{\varepsilon},\tfrac{\log b}{\varepsilon},s\bigr)$.
--   3. **Bin weight.** $w_{\varepsilon,s}(a)=e^{\varepsilon(\ell_{\varepsilon,s}(a)-s)}$ if $a>0$, and $w_{\varepsilon,s}(a)=0$ if $a\le 0$. For $\varepsilon>0$ this is the largest point of the geometric grid $\{e^{\varepsilon(\ell-s)}:\ell\in\mathbb{Z}\}$ not exceeding $a$.
--   4. **Eigenbasis overlaps.** For Hermitian $A,B\in\mathbb{C}^{n\times n}$ with chosen orthonormal eigenbases $(u_i)$ of $A$ and $(v_j)$ of $B$ (the columns of the unitaries $U_A,U_B$ that diagonalize them), $o_{ij}=|(U_A^*U_B)_{ij}|^2=|\langle u_i,v_j\rangle|^2$; the matrix $(o_{ij})$ is doubly stochastic.
--   5. **Spectral envelope.** With the eigenvalues $\lambda_i(A)$, $\lambda_j(B)$ listed along the same eigenbases,
--   $$\mathcal E_{\varepsilon,s}(A,B)=\sum_{i,j}\beta_{\varepsilon,s}\bigl(\lambda_i(A),\lambda_j(B)\bigr)\,o_{ij}.$$
--   6. **Bin scale and bin indicator.** For $\ell\in\mathbb{Z}$: $\sigma_{\varepsilon,s}(\ell)=e^{\varepsilon(\ell-s)}$, and $\chi_{\varepsilon,s,\ell}(a)=1$ if $a>0$ and $\ell_{\varepsilon,s}(a)=\ell$, $\chi_{\varepsilon,s,\ell}(a)=0$ otherwise.
--   7. **Bin projection.** For $A\in\mathbb{C}^{n\times n}$, $P_\ell(A)=\chi_{\varepsilon,s,\ell}(A)$ (functional calculus). For Hermitian $A$ this is the orthogonal projection onto the span of the eigenvectors of $A$ whose eigenvalues are positive and have label $\ell$.
--
--   The construction discretizes a positive semidefinite matrix by rounding each positive eigenvalue down to a geometric grid of ratio $e^{\varepsilon}$ shifted by a random $s$. Two close eigenvalues land in different bins only for a small set of shifts, which is what the separation indicator records. Averaged over $s\in[0,1]$, the spectral envelope of positive semidefinite $A,B$ is at most $\frac{3}{\varepsilon}\|A-B\|_2\sqrt{2(\|A\|_2^2+\|B\|_2^2)}$ when $0<\varepsilon\le 1$ ($\|\cdot\|_2$ the Hilbert–Schmidt norm), and for every finite set $L$ of labels it dominates the weighted mismatch $\sum_{\ell\in L}\sigma_{\varepsilon,s}(\ell)^2\,\|P_\ell(A)-P_\ell(B)\|_2^2$ of the bin projections. This is the quantitative input for correlated, binned approximations of two players' operators.
--
--   **Formalization Note** The definitions are `separated`, `binEnvelope`, `binWeight`, `overlap`, `spectralEnvelope`, `binScale`, `binIndicator` and `binProjection`. Eigenvalues and diagonalizing unitaries are Mathlib's `IsHermitian.eigenvalues` and `IsHermitian.eigenvectorUnitary`, so `overlap` and `spectralEnvelope` take Hermitian-ness proofs as arguments. The formulas hold for all real inputs with Lean's conventions `Real.log 0 = 0`, `Real.log x = Real.log |x|` and division by zero giving $0$; `binProjection` uses `cfc`, which returns $0$ for a non-Hermitian matrix. The two bounds in the last paragraph are proved separately and are not part of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SpectralBins.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SpectralBins.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_n u_ι

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open MeasureTheory Set
open scoped Interval

namespace ThresholdParallelRepetition.QuantumSampling

def separated (u v s : ℝ) : ℝ := if ⌊u+s⌋ = ⌊v+s⌋ then 0 else 1

def binEnvelope (a b ε s : ℝ) : ℝ :=
  (a-b)^2 + 2*a*b*separated (Real.log a/ε) (Real.log b/ε) s

def binWeight (a ε s : ℝ) : ℝ :=
  if 0 < a then Real.exp (ε*((⌊Real.log a/ε+s⌋ : ℝ)-s)) else 0

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def overlap {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
    (hB.eigenvectorUnitary : Matrix n n ℂ)) i j)

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def spectralEnvelope {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ε s : ℝ) : ℝ := ∑ i, ∑ j, binEnvelope (hA.eigenvalues i) (hB.eigenvalues j) ε s * overlap hA hB i j

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

def binScale (ε s : ℝ) (l : ℤ) : ℝ := Real.exp (ε*((l:ℝ)-s))
def binIndicator (ε s : ℝ) (l : ℤ) (a : ℝ) : ℝ :=
  if 0 < a ∧ ⌊Real.log a/ε+s⌋ = l then 1 else 0

variable {n : Type u_n} [Fintype n] [DecidableEq n]

def binProjection (A : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) : Matrix n n ℂ :=
  cfc (binIndicator ε s l) A

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end

end OAI


