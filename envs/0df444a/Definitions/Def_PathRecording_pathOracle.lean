-- Prove2me | Definitions.Def_PathRecording_pathOracle
-- name    : PathRecording_pathOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:07:44.793468+00:00
-- url     : https://prove2.me/theorems/0db087dd-1ad5-4251-8409-2af96eb09005
-- title:
--   The path recording oracle $Q^{\mathrm{Path}}_{\rho,t+1}$
-- statement:
--   The **append map** $\mathrm{App}^{(t)}_{x,y}:\mathrm{Path}_t\to\mathrm{Path}_{t+1}$ appends a pair at the end:
--   $$\mathrm{App}^{(t)}_{x,y}|x_1,\dots,x_t\rangle\otimes|y_1,\dots,y_t\rangle=|x_1,\dots,x_t,x\rangle\otimes|y_1,\dots,y_t,y\rangle.\qquad(5.3)$$
--   Given Schur–Weyl data at $t$ and at $t+1$, the **path recording oracle** is the linear operator $V\otimes\mathrm{Path}_t\to V\otimes\mathrm{Path}_{t+1}$
--   $$Q^{\mathrm{Path}}_{\rho,t+1}=\sum_{x,y\in B(V)}|y\rangle\langle x|\otimes W_{t+1}\,\Omega_{\mathcal A_{t+1}}\,\mathrm{App}^{(t)}_{x,y}\,W_t^+\,\Omega_{\mathcal A_t}.\qquad(5.8)$$
--
--   This is the stateful oracle that, by Theorem 5.3, perfectly simulates queries to $\rho(g)$ for a Haar-random $g$.
--
--   **Formalization Note** The full form (5.8) is used, not the form (5.9) restricted to the legal subspace. The operator is a matrix indexed by `Fin N × PathIdx N (t+1)` and `Fin N × PathIdx N t`.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Eq. (5.3), p.60 and Definition 5.1, Eq. (5.8), p.62

import Mathlib
import Definitions.Def_PathRecording_reweight

set_option autoImplicit false

namespace PathRecording

/-!
# The append map and the path recording oracle `Q^{Path}_{ρ,t+1}`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2:

* Eq. (5.3), p.60: `App^{(t)}_{x,y} : Path_t → Path_{t+1}`,
  `App^{(t)}_{x,y} |x⃗, y⃗⟩ = |x₁,…,x_t, x⟩ ⊗ |y₁,…,y_t, y⟩`.
* Definition 5.1, Eq. (5.8), p.62: on `V ⊗ Path_t`,
  `Q^{Path}_{ρ,t+1} = Σ_{x,y∈B(V)} |y⟩⟨x| ⊗ W_{t+1} · Ω_{𝒜_{t+1}} · App^{(t)}_{x,y} · W_t^+ · Ω_{𝒜_t}`,
  which outputs an element of `V ⊗ Path_{t+1}`.

**Formalization Note.**
* The oracle uses the Schur–Weyl data at both `t` (for `W_t^+`, `Ω_{𝒜_t}`) and `t + 1` (for
  `W_{t+1}`, `Ω_{𝒜_{t+1}}`); it is the full form (5.8), not the restricted form (5.9).
* `V ⊗ Path_t` has basis `|x⟩ ⊗ |x⃗, y⃗⟩` indexed by `Fin N × PathIdx N t`; the matrix entry from
  `(x, p)` to `(y, p')` is `(W_{t+1} Ω_{𝒜_{t+1}} App^{(t)}_{x,y} W_t^+ Ω_{𝒜_t})_{p',p}`.
* The new pair is appended at the last position (`Fin.snoc`).
-/

open Matrix

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ} {ρ : UnitaryRep G N}

/-- The append map `App^{(t)}_{x,y} |x⃗, y⃗⟩ = |x⃗, x⟩ ⊗ |y⃗, y⟩` as a `Path_{t+1} × Path_t` matrix
(arXiv:2606.30281v2, Eq. (5.3), p.60). -/
noncomputable def append (t : ℕ) (x y : Fin N) : Matrix (PathIdx N (t + 1)) (PathIdx N t) ℂ :=
  Matrix.of fun p q =>
    if p = (Fin.snoc (α := fun _ => Fin N) q.1 x, Fin.snoc (α := fun _ => Fin N) q.2 y) then 1
    else 0

/-- The path recording oracle `Q^{Path}_{ρ,t+1} : V ⊗ Path_t → V ⊗ Path_{t+1}`,
`Σ_{x,y} |y⟩⟨x| ⊗ W_{t+1} Ω_{𝒜_{t+1}} App^{(t)}_{x,y} W_t^+ Ω_{𝒜_t}`
(arXiv:2606.30281v2, Definition 5.1, Eq. (5.8), p.62). -/
noncomputable def pathOracle {t : ℕ} (S : SchurWeylData ρ t) (S' : SchurWeylData ρ (t + 1)) :
    Matrix (Fin N × PathIdx N (t + 1)) (Fin N × PathIdx N t) ℂ :=
  Matrix.of fun a b =>
    (S'.reweight * S'.omega * append t b.1 a.1 * S.reweightPlus * S.omega) a.2 b.2

end PathRecording


