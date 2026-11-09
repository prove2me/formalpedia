-- Prove2me | Definitions.Def_TranspositionIID_Main_Entropy
-- name    : TranspositionIID_Main_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:18.481196+00:00
-- url     : https://prove2.me/theorems/c832c370-6403-4ce0-9999-1f1e827ee923
-- title:
--   Extended nonnegative entropy dissipation at zero densities
-- statement:
--   For nonnegative conductances $c$ and density values $a,b$, define an edge contribution to be zero if $c=0$ or $a=b=0$, infinite if $c>0$ and exactly one of $a,b$ is zero, and otherwise $c(a-b)(\log a-\log b)$. Then
--   $$\mathcal E_P(f,\log f)=\tfrac12\sum_{a,b}\operatorname{edge}(\mu(a)P(a,b),f(a),f(b)).$$
--   The sum takes values in $[0,+\infty]$. For positive densities it equals the published real bilinear Dirichlet form embedded into this extended type. This preserves the paper's meaning for point masses and other laws with zero density values.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). §2.1, zero-density edge convention, printed p.3 = PDF p.3

import Mathlib
import Definitions.Def_GibbsCongestion_dirichletForm

noncomputable section

namespace TranspositionIID.Main

/-- Nonnegative entropy edge, with the extended-value convention of §2.1, p.3.
Zero conductance and two zero densities contribute zero; exactly one zero contributes infinity. -/
def entropyEdge (c a b : ℝ) : ENNReal :=
  if c = 0 ∨ (a = 0 ∧ b = 0) then 0
  else if a = 0 ∨ b = 0 then ⊤
  else ENNReal.ofReal (c * (a - b) * (Real.log a - Real.log b))

/-- Extended entropy dissipation. Its valid domain is nonnegative conductances and densities. -/
def entropyDissipation {S : Type*} [Fintype S]
    (P : Matrix S S ℝ) (μ f : S → ℝ) : ENNReal :=
  (1 / 2) * ∑ a, ∑ b, entropyEdge (μ a * P a b) (f a) (f b)

end TranspositionIID.Main


