-- Prove2me | Definitions.Def_VectorCalculus_conservative
-- name    : VectorCalculus_conservative
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T00:02:28.707607+00:00
-- url     : https://prove2.me/theorems/5dc9943a-5503-4949-be5d-69b32b215875
-- title:
--   Conservative vector field: $\mathbf{F} = \nabla\phi$ with $\phi$ continuous
-- statement:
--   A vector field $\mathbf F$ on $\mathbb R^n$ is *conservative* if it can be written as $\mathbf F = \nabla\phi$ for some scalar field $\phi$, called a potential. Following the discussion of §1.3.4, the potential is required to be continuous and defined at every point of $\mathbb R^n$.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.2 (p. 21), definition of a conservative field, together with the requirement stated in §1.3.4 (p. 25) that $\phi$ be continuous and defined everywhere

import Definitions.Def_VectorCalculus_grad

namespace VectorCalculus

/-- A vector field `F` on `ℝⁿ` is *conservative* if `F = ∇φ` for some continuous
scalar field (potential) `φ` defined on all of `ℝⁿ`. -/
def IsConservative {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∃ φ : (Fin n → ℝ) → ℝ, Continuous φ ∧ ∀ y, F y = grad φ y

end VectorCalculus


