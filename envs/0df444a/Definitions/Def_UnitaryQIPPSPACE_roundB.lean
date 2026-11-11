-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_roundB
-- name    : UnitaryQIPPSPACE_roundB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:49.763858+00:00
-- url     : https://prove2.me/theorems/e2b4e457-bd1d-44f4-890f-2ea9a5d60579
-- title:
--   The rounded operator $B$ of eq. (12) and its polar factor $W$
-- statement:
--   Given a map $C$ on $\mathcal L(\mathcal H)$, a unit vector $|\phi\rangle$ and a vector $|v\rangle$ (in Lemma 4.1 the top eigenvector of $\sigma=C(|\phi\rangle\langle\phi|)$), $B$ is the linear operator with
--   $$B|\phi\rangle=|v\rangle,\qquad B|\phi^\perp\rangle=Q_vC(|\phi^\perp\rangle\langle\phi|)|v\rangle\ \text{ for } \langle\phi|\phi^\perp\rangle=0,\qquad Q_v=I-|v\rangle\langle v|,$$
--   and $W:=B(B^\dagger B)^{-1/2}$ is its unitary polar factor.
--
--   This is the construction that rounds an almost unitary channel to an exact unitary.
--
--   **Formalization Note** Column $j$ of $B$ is $\langle\phi|e_j\rangle\,v+Q_vC(|e_j^\perp\rangle\langle\phi|)v$ with $e_j^\perp=e_j-\langle\phi|e_j\rangle\phi$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.1, eq. (12), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ObliviousRSP_pureState

open Matrix
open scoped MatrixOrder

namespace UnitaryQIPPSPACE

/-- **The operator `B` of eq. (12)** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819,
held version sha256 9e357a00…, Lemma 4.1 (2), p. 19 (PDF p. 21)): "Let `|v_max⟩` be the eigenstate
of `σ` for `λ_max(σ)`, and `Q_{v_max} = I − |v_max⟩⟨v_max|`. Define a linear operator `B ∈ L(H)` via
the following actions: `B|ϕ⟩ = |v_max⟩`, `∀ |ϕ^⊥⟩ : ⟨ϕ|ϕ^⊥⟩ = 0, B|ϕ^⊥⟩ = Q_{v_max} C(|ϕ^⊥⟩⟨ϕ|) |v_max⟩`."

For a map `C` on `L(ℂ^ι)`, a unit vector `ϕ` and a vector `v`, column `j` of `roundB C ϕ v` is
`B e_j = ⟨ϕ|e_j⟩ v + Q_v C(|x^⊥⟩⟨ϕ|) v` with `x^⊥ = e_j − ⟨ϕ|e_j⟩ϕ` the component of `e_j`
orthogonal to `ϕ`; for linear `C` and unit `ϕ` this is the unique linear operator with the two
defining actions. -/
noncomputable def roundB {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℂ → Matrix ι ι ℂ)
    (ϕ v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    let x : ι → ℂ := Pi.single j 1
    let c : ℂ := star ϕ ⬝ᵥ x
    (c • v + (1 - ObliviousRSP.pureState v).mulVec ((C (Matrix.vecMulVec (x - c • ϕ) (star ϕ))).mulVec v)) i

/-- **The unitary projection** `W := B (B†B)^{−1/2}` (Lemma 4.1 (3), p. 19), the unitary factor of
the polar decomposition of an invertible `B`. -/
noncomputable def roundW {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  B * (CFC.sqrt (Bᴴ * B))⁻¹

end UnitaryQIPPSPACE


