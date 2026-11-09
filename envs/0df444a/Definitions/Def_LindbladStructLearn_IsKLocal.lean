-- Prove2me | Definitions.Def_LindbladStructLearn_IsKLocal
-- name    : LindbladStructLearn_IsKLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:26.66963+00:00
-- url     : https://prove2.me/theorems/7eca1544-7fe9-439a-9a78-9ab9275ac1d2
-- title:
--   $k$-locality of a coefficient vector
-- statement:
--   A coefficient vector $\lambda$ is $k$-local if every term present, i.e. every pair $\overline P = (P_1,P_2)$ with $P_1 \ne I$ and $\lambda_{\overline P} \ne 0$, satisfies $|\mathrm{supp}(P_1)\cup\mathrm{supp}(P_2)| \le k$. For $P_2 = I$ this is the paper's $|\mathrm{supp}(P)| \le k$ for the coherent terms.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.1, p.13

import Mathlib
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- `k`-locality of a coefficient vector (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.1, p.13): every term present
(`λ_(P₁,P₂) ≠ 0`, `P₁ ≠ I`) has `|supp(P₁) ∪ supp(P₂)| ≤ k`. -/
def IsKLocal {n : ℕ} (k : ℕ) (x : Pauli n × Pauli n → ℂ) : Prop :=
  ∀ P : Pauli n × Pauli n, P.1 ≠ 0 → x P ≠ 0 → (pairSupport P).card ≤ k

end LindbladStructLearn


