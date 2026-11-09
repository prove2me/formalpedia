-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_SuffixBaseline
-- name    : OnlinePerceptronIsolation_Binary_SuffixBaseline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:53.440877+00:00
-- url     : https://prove2.me/theorems/c0fd7ee2-10df-4cd5-9657-ac0fb0184d3b
-- title:
--   The computed suffix-parallel baseline
-- statement:
--   For a deterministic online algorithm $A$ and $0\le r<n$, the baseline $A^{(r)}$ keeps the actual first $n-r$ signs of $A$. Each remaining column $Y$ is signed using the same response that $A$ would give if $Y$ arrived immediately after that frozen prefix:
--   $$A^{(r)}_{n-r+i}(G)=\operatorname{SubAlg}_{n-r+1}(Y_i;G',\sigma',\kappa)\quad(1\le i\le r).$$
--   In Lean this response is evaluated on the original prefix, with $Y_i$ inserted at zero-based position $n-r$ and all unseen columns zero-filled. Nonanticipation makes the filling irrelevant. Neither the stage nor the history changes across suffix columns. The associated probability is that $A$ outputs an isolated solution and disagrees with this computed baseline. For $r=0$ or $r>n$ the total definition returns the original output; the theorem uses only $r<n$.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 3.3, Eqs. (3.4)-(3.5), printed p.8, PDF p.10; Eqs. (4.1)-(4.2), printed p.12, PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Isolation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Definition 3.3, printed p.8 / PDF p.10. The zero-based stage n-r is reused for
EVERY suffix column. Unseen columns are filled with zero; nonanticipation makes them irrelevant.
For r=0 or invalid r>n this is the original output (only r<n is used in statements). -/
def suffixBaseline {m n : ℕ} (A : Fin n → (Fin m × Fin n → ℝ) → ℝ)
    (r : ℕ) (G : Fin m × Fin n → ℝ) (k : Fin n) : ℝ :=
  if hp : r ≤ n ∧ n - r < n then
    if k.val < n - r then A k G
    else A ⟨n - r, hp.2⟩ (fun ij =>
      if ij.2.val < n - r then G ij
      else if ij.2.val = n - r then G (ij.1, k) else 0)
  else A k G

/-- Equations (4.1)--(4.2): success together with failure to match the computed baseline. -/
noncomputable def mismatchSuccess {m n : ℕ}
    (A : Fin n → (Fin m × Fin n → ℝ) → ℝ) (κ h : ℝ) (r : ℕ) : ℝ :=
  (ABPOnline.gaussMat m n).real
    {G | IsIsolated G κ h (fun i => A i G) ∧
      (fun i => A i G) ≠ suffixBaseline A r G}

end OnlinePerceptronIsolation.Binary


