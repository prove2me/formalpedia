-- Prove2me | Definitions.Def_AKR2008_Defs
-- name    : AKR2008_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T22:28:23.298982+00:00
-- url     : https://prove2.me/theorems/4f78c23d-4a63-4a50-8364-5e1411c82757
-- title:
--   EPR photon pair with detector: states (1), (2) and reduced state of photon 2
-- statement:
--   Definitions for Sec. II of Albers–Kiefer–Reginatto (2008).
--
--   Let $\mathcal H$ be a complex inner-product space (the detector). A vector of photon 1 $\otimes$ photon 2 $\otimes$ detector is recorded by its detector-valued components $\Psi_{ij}\in\mathcal H$, $i,j\in\{0,1\}$, where $|0\rangle = |\uparrow\rangle$ is horizontal and $|1\rangle = |\downarrow\rangle$ vertical polarization.
--
--   1. **`polKet i`** — the basis vector $|i\rangle\in\mathbb C^2$.
--   2. **`psiBefore Φ₀`** — Eq. (1): $|\Psi_0\rangle = \tfrac{1}{\sqrt2}\bigl(|\uparrow\rangle_1|\downarrow\rangle_2 - |\downarrow\rangle_1|\uparrow\rangle_2\bigr)|\Phi_0\rangle$.
--   3. **`psiAfter Φ↑ Φ↓`** — Eq. (2): $|\Psi\rangle = \tfrac{1}{\sqrt2}\bigl(|\uparrow\rangle_1|\downarrow\rangle_2|\Phi_\uparrow\rangle - |\downarrow\rangle_1|\uparrow\rangle_2|\Phi_\downarrow\rangle\bigr)$.
--   4. **`reducedPhoton2 Ψ`** — the reduced density matrix of photon 2 obtained from $|\Psi\rangle\langle\Psi|$ by tracing out photon 1 and the detector:
--   $$\rho_2(\Psi)_{jj'} = \sum_{i\in\{0,1\}} \langle \Psi_{ij'}, \Psi_{ij}\rangle_{\mathcal H}.$$
--   5. **`rhoHat`** — Eq. (3): $\hat\rho = \tfrac12\bigl(|\uparrow\rangle\langle\uparrow| + |\downarrow\rangle\langle\downarrow|\bigr)$ as a $2\times2$ complex matrix.
--
--   These definitions are shared by the goal theorem and by Milestones 1–2.
--
--   **Formalization Note** The tensor product $\mathbb C^2\otimes\mathbb C^2\otimes\mathcal H$ is identified with the space of functions $\{0,1\}^2\to\mathcal H$; Mathlib's inner product is conjugate-linear in its first argument, which is why the entry $(j,j')$ pairs $\Psi_{ij'}$ on the left with $\Psi_{ij}$ on the right.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-2, Sec. II, Eqs. (1)–(3)

import Mathlib

/-!
# Albers–Kiefer–Reginatto (2008), Sec. II: the EPR-type states (1), (2) and the
reduced density operator (3) of photon 2.

The joint Hilbert space is `ℂ² ⊗ ℂ² ⊗ H` (photon 1 ⊗ photon 2 ⊗ detector), where `H` is an
arbitrary complex inner-product space.  Using the canonical isomorphism
`ℂ² ⊗ ℂ² ⊗ H ≅ (Fin 2 × Fin 2 → H)`, a joint vector is recorded by its `H`-valued components
`Ψ i j` (`i` = polarization of photon 1, `j` = polarization of photon 2).
Polarization index `0` is horizontal (`↑`), index `1` is vertical (`↓`).
-/

namespace AKR2008

open scoped InnerProductSpace

/-- A vector of photon 1 ⊗ photon 2 ⊗ detector, given by its detector-valued components:
`Ψ i j ∈ H` is the component along `|i⟩₁ |j⟩₂`. -/
abbrev JointState (H : Type*) := Fin 2 → Fin 2 → H

/-- The computational basis vector `|i⟩` of a single photon's polarization space `ℂ²`
(`|0⟩ = |↑⟩` horizontal, `|1⟩ = |↓⟩` vertical). -/
def polKet (i : Fin 2) : Fin 2 → ℂ := fun k => if k = i then 1 else 0

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Eq. (1): `|Ψ₀⟩ = (1/√2)(|↑⟩₁|↓⟩₂ − |↓⟩₁|↑⟩₂) |Φ₀⟩`. -/
noncomputable def psiBefore (Φ₀ : H) : JointState H := fun i j =>
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • ((polKet 0 i * polKet 1 j - polKet 1 i * polKet 0 j) • Φ₀)

/-- Eq. (2): `|Ψ⟩ = (1/√2)(|↑⟩₁|↓⟩₂|Φ↑⟩ − |↓⟩₁|↑⟩₂|Φ↓⟩)`. -/
noncomputable def psiAfter (Φup Φdown : H) : JointState H := fun i j =>
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • ((polKet 0 i * polKet 1 j) • Φup - (polKet 1 i * polKet 0 j) • Φdown)

/-- The reduced density operator of photon 2 obtained from the pure state `|Ψ⟩⟨Ψ|` by tracing
out photon 1 and the detector:
`ρ₂(j, j') = ∑ᵢ ⟨Ψ i j', Ψ i j⟩_H` (matrix entries in the basis `|↑⟩, |↓⟩`). -/
noncomputable def reducedPhoton2 (Ψ : JointState H) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun j j' => ∑ i, ⟪Ψ i j', Ψ i j⟫_ℂ

/-- Eq. (3): `ρ̂ = ½ (|↑⟩₂⟨↑|₂ + |↓⟩₂⟨↓|₂)`. -/
noncomputable def rhoHat : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (Matrix.vecMulVec (polKet 0) (star (polKet 0)) +
    Matrix.vecMulVec (polKet 1) (star (polKet 1)))

end AKR2008


