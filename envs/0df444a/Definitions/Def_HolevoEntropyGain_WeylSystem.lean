-- Prove2me | Definitions.Def_HolevoEntropyGain_WeylSystem
-- name    : HolevoEntropyGain_WeylSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:46.047524+00:00
-- url     : https://prove2.me/theorems/3c719570-85d6-4861-9885-4615ff96e793
-- title:
--   Irreducible strongly continuous Weyl system for a commutation matrix $\Delta$
-- statement:
--   Let $\Delta$ be a real $2s\times 2s$ matrix and $H = \ell^2(I)$ a separable Hilbert space. A **Weyl system** for $\Delta$ on $H$ is a family of bounded operators $W(z)$, $z \in \mathbb R^{2s}$, such that
--
--   1. every $W(z)$ is unitary and the Weyl form of the canonical commutation relations holds:
--   $$
--   W(z)W(w) = \exp\!\Big(-\tfrac i2\, z^\top \Delta w\Big)\, W(z+w), \qquad z,w\in\mathbb R^{2s};
--   $$
--   2. $W$ is strongly continuous: $t \mapsto W(tz)\psi$ is continuous for every $z$ and every $\psi\in H$;
--   3. $W$ is irreducible: the only closed subspaces of $H$ invariant under every $W(z)$ are $\{0\}$ and $H$.
--
--   This is $W(z) = \exp(iRz)$ for canonical variables $R = (R_1,\dots,R_{2s})$ with $[R_j,R_k] = i\Delta_{jk}$, the representation of the CCR in which Bosonic Gaussian states and channels are defined. The three conditions are the platform's general CCR predicates `IsCCR`, `WeylRegular` and `HilbertIrreducible` (Dereziński's notes, `Intake100.P23`) for the bilinear form $\omega(z,w) = z^\top\Delta w$.
--
--   **Formalization Note** The paper says only "the Weyl system … giving the representation for the Canonical Commutation Relations". This is read as the irreducible, strongly continuous (Schrödinger) representation; for a reducible representation the paper's Proposition 2 is false (take $W\otimes I$ on $H\otimes\mathbb C^2$ and $\Phi = \mathrm{id}\otimes(\text{trace and prepare } |0\rangle)$). $W(0) = I$ follows from the axioms, and continuity along lines implies joint strong continuity. The sign of $\Delta$ is immaterial: every statement of the mission quantifies over all $\Delta$ and is invariant under $\Delta\mapsto-\Delta$.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.4 (Weyl system W(z) = exp(iRz) giving the representation of the CCR)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Intake100.P23 (IsCCR WeylRegular HilbertIrreducible)

namespace HolevoEntropyGain

/-- The Weyl system `W(z) = exp(iRz)`, `z ∈ Z`, in the Hilbert space `H = Hilbert I`, giving the
representation of the Canonical Commutation Relations with commutation matrix `Δ`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.4, PDF p.4).

The three fields are the platform's general CCR predicates (`Intake100.P23`, Dereziński) at the real
vector space `Z = ℝ^{2s}` with the bilinear form `ω(z, w) = zᵀΔw`: unitary `W(z)` with
`W(z)W(w) = exp(-(i/2) zᵀΔw) W(z + w)`, strong continuity along every line, and irreducibility.

**Formalization Note** (reading R1) "The representation" of the CCR is read as a strongly continuous
irreducible one, the Schrödinger representation by Stone–von Neumann. The reducible reading makes
Proposition 2 false: `W ⊗ I` on `L² ⊗ ℂ²` with `Φ = id ⊗ (trace and prepare |0⟩)` has `K = I`, `μ = 0`,
yet `Φ[I] ≠ I` and the entropy gain of `ρ₀ ⊗ I/2` is `-log 2`.

**Formalization Note** (R9) `[Rⱼ, Rₖ] = iΔⱼₖ` gives `W(z)W(w) = exp(-(i/2) zᵀΔw) W(z + w)`. Every
statement quantifies over every `Δ`, and (15), (17)–(19) are invariant under `Δ ↦ -Δ`, so the sign
convention changes no instance. `W(0) = I` follows: `W(0)` is a unitary idempotent. Continuity along
lines gives joint strong continuity, since `W(z)` is a phase times a product of the unitaries
`W(zⱼeⱼ)`. -/
structure WeylSystem (I : Type) {s : ℕ} (Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ) where
  /-- The unitary `W(z)`. -/
  operator : (Fin (2 * s) → ℝ) → Hilbert I →L[ℂ] Hilbert I
  /-- Unitarity and the Weyl form of the CCR, with `ω(z, w) = zᵀΔw`. -/
  ccr : IsCCR (Matrix.toLinearMap₂' ℝ Δ) operator
  /-- Strong continuity. -/
  regular : WeylRegular operator
  /-- Irreducibility: the only closed invariant subspaces are `⊥` and `⊤`. -/
  irreducible : HilbertIrreducible operator

end HolevoEntropyGain


