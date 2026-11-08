-- Prove2me | Definitions.Def_MonoidProdQ_IsAdvMatrix
-- name    : MonoidProdQ_IsAdvMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:43:05.436115+00:00
-- url     : https://prove2.me/theorems/ecd967b3-fb86-47fb-b546-3de22b0c3953
-- title:
--   Adversary matrix
-- statement:
--   Let $f$ be a function on a finite promise domain $D\subseteq\Sigma^I$. An **adversary matrix** for $f$ is a real symmetric matrix $\Gamma$ indexed by $D\times D$ such that
--
--   $$\Gamma_{xy}=0\qquad\text{whenever } f(x)=f(y).$$
--
--   Entries may be negative. These are the matrices over which the negative-weight general adversary bound is taken.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Adversary bounds, p.24

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, "Adversary bounds", p.24: `Γ` is an adversary matrix for `f` on the promise
domain `D`: "a real symmetric matrix indexed by promise inputs, with Γ_{xy} = 0 whenever
f(x) = f(y)". Inputs are words `x : I → Sig` over a finite input alphabet; `f` has any output
type. -/
def IsAdvMatrix {I Sig Out : Type*} (f : (I → Sig) → Out) (D : Finset (I → Sig))
    (Γ : Matrix D D ℝ) : Prop :=
  Γ.IsSymm ∧ ∀ x y : D, f x = f y → Γ x y = 0

end MonoidProdQ


