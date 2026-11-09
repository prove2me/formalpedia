-- Prove2me | Definitions.Def_BinarySketchTruncation_Opposite_ExplicitKernel
-- name    : BinarySketchTruncation_Opposite_ExplicitKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:38.160232+00:00
-- url     : https://prove2.me/theorems/47d80c21-90f2-4c52-a50f-f68e6a0589b2
-- title:
--   The computed single-bit and independent-addition simulation kernels
-- statement:
--   For distinct biases $p_0,p_1\in[0,1]$, define
--
--   $$
--   a=\frac{p_1(1-2p_0)}{p_1-p_0},\qquad
--   b=\frac{(1-p_0)(2p_1-1)}{p_1-p_0},\qquad
--   K_1=\begin{pmatrix}a&1-a\\ b&1-b\end{pmatrix},\quad K_0=\mathrm{Id}.
--   $$
--
--   Rows are indexed by input bits $u=0,1$ and columns by output bits. For a dimension $k$ and conditional noise laws $\nu_0,\nu_1$ on $\mathbb F_2^k$, define the real-valued matrix
--
--   $$
--   K(s\mid u)=\sum_{v_0,v_1}\nu_0(v_0)\nu_1(v_1)
--   \prod_i K_{v_{0i}\oplus v_{1i}}(s_i\oplus v_{0i}\mid u_i).
--   $$
--
--   For zero dimension use the unique identity kernel. For equal biases use the identity kernel; under the sufficient condition of Proposition 2 those biases must both equal $1/2$ unless the dimension is zero. The rational formula is evaluated only in the distinct-bias branch.
--
--   This is the paper's construction using the independent coupling of $v_0,v_1$. Stochasticity and the induced-law equalities are conclusions of Proposition 2, not conditions built into this definition. Outside its sufficient regime the computed matrix is not claimed to simulate the desired laws.
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), pp. 7–8, Lemma 2 proof and Proposition 2 proof (PDF pp. 8–9)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite

/-- Lemma 2's matrix, rows indexed by the input bit, columns by the output.
The equality branch is kept separate from the rational formula. -/
noncomputable def flipKernel (p₀ p₁ : Bias) (u s : Bit) : ℝ :=
  if p₀ = p₁ then (if s = u then 1 else 0)
  else
    let a := (p₁ : ℝ) * (1 - 2 * (p₀ : ℝ)) / ((p₁ : ℝ) - (p₀ : ℝ))
    let b := (1 - (p₀ : ℝ)) * (2 * (p₁ : ℝ) - 1) / ((p₁ : ℝ) - (p₀ : ℝ))
    let r := if u = 0 then a else b
    if s = 0 then r else 1 - r

/-- K_0 is identity; K_1 is the single-bit flip simulation. -/
noncomputable def coordinateKernel (p₀ p₁ : Bias) (d u s : Bit) : ℝ :=
  if d = 0 then (if s = u then 1 else 0) else flipKernel p₀ p₁ u s

/-- Proposition 2's proof, printed p. 8 (PDF 9), choosing the independent
coupling of the two noise laws. This definition computes the witness, with
identity branches for k=0 and equal biases. It does not assume stochasticity. -/
noncomputable def explicitKernel (k : ℕ) (p₀ p₁ : Bias)
    (ν : Experiment (Vec k)) (u s : Vec k) : ℝ :=
  if k = 0 then (if s = u then 1 else 0)
  else if p₀ = p₁ then (if s = u then 1 else 0)
  else ∑ v₀ : Vec k, ∑ v₁ : Vec k,
    (ν false v₀).toReal * (ν true v₁).toReal *
      ∏ i, coordinateKernel p₀ p₁ (v₀ i + v₁ i) (u i) (s i + v₀ i)

end BinarySketchTruncation.Opposite


