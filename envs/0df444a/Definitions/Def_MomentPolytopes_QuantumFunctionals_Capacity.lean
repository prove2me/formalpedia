-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_Capacity
-- name    : MomentPolytopes_QuantumFunctionals_Capacity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:04:09.73008+00:00
-- url     : https://prove2.me/theorems/aec51bb3-74bb-4ff2-a7cc-1850055dd527
-- title:
--   Kempf–Ness function, Busemann functions on P, the logarithmic X-capacity and the K-invariant capacity log Cap_p
-- statement:
--   Let $P=\mathrm{PD}(n_1)\times\dots\times\mathrm{PD}(n_d)$ and $K=\mathrm U(n_1)\times\dots\times\mathrm U(n_d)$. For a tensor tuple $v\ne0$ the **Kempf–Ness function** is $f_v(x)=\log\langle v,x\cdot v\rangle$ on $P$, with $x\cdot v=(I\otimes x_1\otimes\dots\otimes x_d)v$.
--
--   For a tuple $X$ of Hermitian matrices (block-diagonal), the **Busemann function** of the ray $t\mapsto e^{tX}$ is
--   $$b_X(x)=\lim_{t\to\infty}\Big(\|X\|_F\,\big\|\log\big(x^{-1/2}e^{Xt}x^{-1/2}\big)\big\|_F-\|X\|_F^2\,t\Big),\qquad x\in P,$$
--   normalized so that $b_X(I)=0$; norms are Frobenius norms of the whole block-diagonal matrix.
--
--   The **logarithmic $X$-capacity** is
--   $$\log\operatorname{cap}_X(v)=\tfrac12\inf_{x\in P}\big(f_v(x)+b_X(x)\big)\in[-\infty,\infty),$$
--   and for $p\in C$ (read as a tuple of diagonal matrices) the **K-invariant logarithmic $p$-capacity** is
--   $$\log\operatorname{Cap}_p(v)=\sup_{u\in K}\log\operatorname{cap}_p(u\cdot v).$$
--
--   **Formalization Note** Both capacities are `EReal`-valued ($-\infty=\bot$), never truncated to a real. The limit defining $b_X$ exists for every $x\in P$ (p. 14); it is taken with `limUnder atTop`. Matrix powers, logarithms and exponentials are the functional calculus `cfc`.
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), Definition 6.4, p. 30; p. 34 (b_X) and Definition 6.11; Definition 6.13, p. 35; §2.1–2.2, p. 14

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope

set_option autoImplicit false

open scoped ComplexOrder Matrix

open Filter

namespace MomentPolytopes.QuantumFunctionals

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- `P = PD(n_1) × ⋯ × PD(n_d)`: tuples of positive-definite matrices (Example 2.1, p. 15). -/
def PDTuple {d : ℕ} (n : Fin d → ℕ) : Type :=
  {x : MatTuple n // ∀ ℓ, (x ℓ).PosDef}

/-- Kempf–Ness function `f_v(x) = log⟨v, x · v⟩`, `x · v = (I ⊗ x_1 ⊗ ⋯ ⊗ x_d) v`
(Definition 6.4, p. 30). `⟨v, x · v⟩` is real and positive for `x ∈ P`, `v ≠ 0`. -/
noncomputable def kempfNess (v : Ten d n0 n) (x : MatTuple n) : ℝ :=
  Real.log (tinner v (act x v)).re

/-- Frobenius norm of a tuple, i.e. of the block-diagonal matrix: `(∑_ℓ ‖X_ℓ‖_F²)^{1/2}`. -/
noncomputable def frobNormTuple (X : MatTuple n) : ℝ :=
  Real.sqrt (∑ ℓ, frobNorm (X ℓ) ^ 2)

/-- The Busemann function on `P` of the geodesic ray `t ↦ e^{tX}`, `X ∈ H` (p. 34):
`b_X(x) = lim_{t→∞} (‖X‖_F ‖log(x^{−1/2} e^{Xt} x^{−1/2})‖_F − ‖X‖_F² t)`, all matrices
block-diagonal. The limit exists for every `x ∈ P`; this fixes `b_X(I) = 0`. -/
noncomputable def busemann (X : MatTuple n) (x : MatTuple n) : ℝ :=
  limUnder atTop (fun t : ℝ =>
    frobNormTuple X *
        frobNormTuple (fun ℓ => cfc Real.log
          (cfc (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (x ℓ) * hermExp t (X ℓ) *
            cfc (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (x ℓ))) -
      frobNormTuple X ^ 2 * t)

/-- Logarithmic `X`-capacity (Definition 6.11, p. 34):
`log cap_X(v) = ½ inf_{x ∈ P} (f_v(x) + b_X(x)) ∈ [−∞, ∞)`, computed in `EReal`. -/
noncomputable def logCapX (X : MatTuple n) (v : Ten d n0 n) : EReal :=
  ((1 / 2 : ℝ) : EReal) * ⨅ x : PDTuple n, ((kempfNess v x.1 + busemann X x.1 : ℝ) : EReal)

/-- A vector tuple `p ∈ ℝ^{n_1} × ⋯ × ℝ^{n_d}` read as the tuple of diagonal matrices
`(diag p_1, …, diag p_d) ∈ A`. -/
noncomputable def diagTuple (p : SpecTuple n) : MatTuple n :=
  fun ℓ => Matrix.diagonal (fun i => ((p ℓ i : ℝ) : ℂ))

/-- K-invariant logarithmic `p`-capacity (Definition 6.13, p. 35):
`log Cap_p(v) = sup_{u ∈ K} log cap_p(u · v)`, `p` read as a tuple of diagonal matrices. -/
noncomputable def logCap (p : SpecTuple n) (v : Ten d n0 n) : EReal :=
  ⨆ u : UTuple n, logCapX (diagTuple p) (uact u v)

end MomentPolytopes.QuantumFunctionals


