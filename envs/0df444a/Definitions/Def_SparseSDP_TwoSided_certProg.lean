-- Prove2me | Definitions.Def_SparseSDP_TwoSided_certProg
-- name    : SparseSDP_TwoSided_certProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:58.52055+00:00
-- url     : https://prove2.me/theorems/67841245-4185-4cac-bddf-495ee6ecafb1
-- title:
--   The computable upper certificate of Lemma 2.5, as a charged program
-- statement:
--   Given a charged product with $M_g$, the certificate program shifts by $\omega$ (the proof's $A_g=M_g+\omega_DI$), runs the Lánczos loop from a random start for
--   $$
--   k=\min\{d,\lceil c_E\sqrt{R\omega/\zeta}\,\log(d/\delta_{\mathrm{eig}})\rceil\}
--   $$
--   steps, takes the Ritz value $\hat\lambda=\lambda_{\max}(T_\ell)$ and returns $\tilde u=R(\hat\lambda-\omega)$, Eq. (69).
--
--   **Formalization Note** The formula for $k$ pins the $\tilde O(\min\{n+1,\sqrt{R\omega_D/\zeta}\})$ of Eq. (67); the constant is `P.cE`.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 2.5 and proof, pp. 20–21, Eqs. (67)–(69)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_alg7

open Matrix

namespace SparseSDP.TwoSided

variable {d : ℕ}

/-- The iteration count of the certificate: `min{d, ⌈c_E √(Rω/ζ) log(d/δ_eig)⌉}`, which pins the
`Õ(min{n + 1, √(Rω_D/ζ)})` of Eq. (67), p. 21. -/
noncomputable def certIters (P : Consts) (d : ℕ) (R ω ζ δe : ℝ) : ℕ :=
  min d ⌈P.cE * √(R * ω / ζ) * Real.log (d / δe)⌉₊

/-- The computable upper certificate of Lemma 2.5 (pp. 20–21): shift by `ω` (the proof's
`A_g = M_g + ω_D I`), run Lánczos from a random start, take the Ritz value `λ̂` of `T_ℓ`, and return
`ũ = R(λ̂ − ω)`, Eq. (69). `mv` is the charged product with `M_g`. -/
noncomputable def certProg (P : Consts) (R ω ζ δe : ℝ) (mv : Vec d → Prog (Vec d)) :
    Prog ℝ := do
  let k ← op 12 (certIters P d R ω ζ δe)
  let u ← drawSphere d
  let kr ← lanczosCore
    (fun v => do
      let w ← mv v
      axpy ω v w) u k
  let lam ← tridiagLamMax kr.α kr.β
  op 2 (R * (lam - ω))

end SparseSDP.TwoSided


