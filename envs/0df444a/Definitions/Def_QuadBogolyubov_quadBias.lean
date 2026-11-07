-- Prove2me | Definitions.Def_QuadBogolyubov_quadBias
-- name    : QuadBogolyubov_quadBias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:03.651972+00:00
-- url     : https://prove2.me/theorems/ea822d6e-878d-4645-bf14-9c3f8ed081e6
-- title:
--   Relative density $\delta_W(A)$ and quadratic bias $\beta_W(A)$
-- statement:
--   For a quadratic variety $W$ and $A\subseteq\mathbb F_2^n$, the **relative density** is $\delta_W(A)=|A\cap W|/|W|$ and the **quadratic bias** is
--   $$\beta_W(A)=\big\|\mathbf 1_{A\cap W}-\delta_W(A)\mathbf 1_W\big\|_{U^3(W)}.$$
--   $A$ is $\varepsilon$-quadratically uniform on $W$ when $\beta_W(A)\le\varepsilon$. These are the quantities tracked by the density-increment argument.
--
--   **Formalization Note** For empty $W$ both Lean values are $0$.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §4.1, p.12

import Mathlib
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

namespace QuadBogolyubov

/-- The **relative density** `δ_W(A) = |A ∩ W| / |W|` of a set `A ⊆ 𝔽₂ⁿ` in a quadratic variety
`W`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §4.1, p.12:
"denote the relative density of A in W by δW(A) := |A ∩ W|/|W|."

**Formalization Note.** For empty `W` the Lean value is `0`. -/
noncomputable def relDensity {n : ℕ} (W : QuadVariety n) (A : Finset (Fin n → ZMod 2)) : ℝ :=
  ((A ∩ W.carrier).card : ℝ) / (W.carrier.card : ℝ)

/-- The **quadratic bias** `β_W(A) = ‖1_{A∩W} − δ_W(A) 1_W‖_{U³(W)}` of `A` relative to `W`.

§4.1, p.12: "Define the quadratic bias of A relative to W by βW(A) := ∥1A∩W − δW(A)1W∥_{U3(W)}.
We say that A is ε-quadratically uniform on W if βW(A) ≤ ε." -/
noncomputable def quadBias {n : ℕ} (W : QuadVariety n) (A : Finset (Fin n → ZMod 2)) : ℝ :=
  localU3 W (fun x => ind (A ∩ W.carrier) x - (relDensity W A : ℂ) * ind W.carrier x)

end QuadBogolyubov


