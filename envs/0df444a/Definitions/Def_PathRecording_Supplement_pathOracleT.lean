-- Prove2me | Definitions.Def_PathRecording_Supplement_pathOracleT
-- name    : PathRecording_Supplement_pathOracleT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:31:01.141599+00:00
-- url     : https://prove2.me/theorems/4f98e77b-ba6f-4fe5-b54d-93df5885f29b
-- title:
--   The transpose path-recording oracle $Q^{\mathrm{Path},\top}_{\rho,t+1}$
-- statement:
--   Let $\rho:G\to U(N)$ be a continuous unitary representation and fix Schur–Weyl data at $t$ and $t+1$. The **transpose path-recording oracle** maps $V\otimes\mathrm{Path}_t$ to $V\otimes\mathrm{Path}_{t+1}$ by
--   $$Q^{\mathrm{Path},\top}_{\rho,t+1}:=\sum_{x,y\in B(V)}|y\rangle\langle x|\otimes W_{t+1}\,\Omega_{\mathcal A_{t+1}}\,\mathrm{App}^{(t)}_{y,x}\,W_t^+\,\Omega_{\mathcal A_t},$$
--   where $\mathrm{App}^{(t)}_{y,x}|\vec x,\vec y\rangle=|\vec x,y\rangle\otimes|\vec y,x\rangle$ appends the reversed pair, $W_t,W_t^+$ are the reweighting operators and $\Omega_{\mathcal A_t}$ is the commutant EPR projector.
--
--   It differs from the forward path-recording oracle (5.8) only in the order of the appended pair; it simulates transpose queries $\rho(g)^\top$.
--
--   **Formalization Note** The full form with $W_t^+\Omega_{\mathcal A_t}$ on the right is kept, as in the published `PathRecording.pathOracle`.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 5.8, p.67

import Mathlib
import Definitions.Def_PathRecording_pathOracle

set_option autoImplicit false

namespace PathRecording.Supplement

/-!
# The transpose path-recording oracle `Q^{Path,⊤}_{ρ,t+1}`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 5.8, p.67:
`Q^{Path,⊤}_{ρ,t+1} := Σ_{x,y∈B(V)} |y⟩⟨x| ⊗ W_{t+1} Ω_{𝒜_{t+1}} App^{(t)}_{y,x} W_t^+ Ω_{𝒜_t}`.

**Formalization Note.** This is the published `PathRecording.pathOracle` (Eq. (5.8)) with the
appended pair reversed: `App^{(t)}_{y,x}` (published `append t y x`) in place of `App^{(t)}_{x,y}`.
The matrix entry from `(x, p)` to `(y, p')` of `V ⊗ Path_t → V ⊗ Path_{t+1}` is
`(W_{t+1} Ω_{𝒜_{t+1}} App^{(t)}_{y,x} W_t^+ Ω_{𝒜_t})_{p', p}`; the full form, with `W_t^+ Ω_{𝒜_t}`
on the right, is kept.
-/

open Matrix

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ} {ρ : UnitaryRep G N}

/-- `Q^{Path,⊤}_{ρ,t+1} = Σ_{x,y} |y⟩⟨x| ⊗ W_{t+1} Ω_{𝒜_{t+1}} App^{(t)}_{y,x} W_t^+ Ω_{𝒜_t}`
(arXiv:2606.30281v2, Theorem 5.8, p.67). -/
noncomputable def pathOracleT {t : ℕ} (S : SchurWeylData ρ t) (S' : SchurWeylData ρ (t + 1)) :
    Matrix (Fin N × PathIdx N (t + 1)) (Fin N × PathIdx N t) ℂ :=
  Matrix.of fun a b =>
    (S'.reweight * S'.omega * append t a.1 b.1 * S.reweightPlus * S.omega) a.2 b.2

end PathRecording.Supplement


