-- Prove2me | Definitions.Def_TeleportGates_Ck_bell1
-- name    : TeleportGates_Ck_bell1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:10.850434+00:00
-- url     : https://prove2.me/theorems/3b10f697-5132-4811-9862-7942d5ff2b9f
-- title:
--   Single-qubit Bell basis vector $\beta_{xz}=(|0x\rangle+(-1)^z|1\bar x\rangle)/\sqrt2$
-- statement:
--   For bits $x,z\in\{0,1\}$ let $\bar x=1-x$. The Bell basis vector with outcome $xz$ is the two-qubit state
--
--   $$\beta_{xz}=\frac{1}{\sqrt2}\bigl(|0x\rangle+(-1)^z|1\bar x\rangle\bigr)\in\mathbb C^2\otimes\mathbb C^2 .$$
--
--   The first tensor factor is the qubit being teleported, the second the half of the EPR pair it is measured with. The four vectors $\beta_{00},\beta_{01},\beta_{10},\beta_{11}$ form an orthonormal basis; measuring in this basis is the Bell measurement of quantum teleportation.
--
--   **Formalization Note** A qubit's basis index is a boolean, `false` $=|0\rangle$. The vector is normalized; the paper writes it without the factor $1/\sqrt2$.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1 (the Bell basis |0x⟩ + (−1)^z|1x̄⟩)

import Mathlib

namespace TeleportGates.Ck

/-- **The single-qubit Bell basis vector `β_{xz}`.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1: "|α⟩ and one qubit of |Ψ⟩ are
measured together in the Bell basis |0x⟩ + (−1)^z|1x̄⟩ (where x, z = {0, 1}, and x̄ = 1 − x)".

`bell1 x z` is the two-qubit vector `(|0x⟩ + (−1)^z |1x̄⟩)/√2`, with amplitudes
`bell1 x z (u, v) = (1/√2)·[u = 0 ∧ v = x] + (1/√2)·(−1)^z·[u = 1 ∧ v = x̄]`.

**Formalization Note.** A qubit's basis index is a `Bool`, `false` = `|0⟩`, `true` = `|1⟩`.
The first factor `u` is the qubit being teleported (the paper's `|α⟩`, or an input qubit), the
second factor `v` is the EPR half it is measured with: the paper writes the teleported qubit's ket
first. The vector is normalized (the paper writes it unnormalized); the four vectors `bell1 x z`
form an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bell1 (x z : Bool) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p =>
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
      (if p.1 = false ∧ p.2 = x then 1
        else if p.1 = true ∧ p.2 = !x then (if z then -1 else 1) else 0)

end TeleportGates.Ck


