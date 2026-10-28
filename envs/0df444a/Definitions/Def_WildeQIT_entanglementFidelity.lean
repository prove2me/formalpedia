-- Prove2me | Definitions.Def_WildeQIT_entanglementFidelity
-- name    : WildeQIT_entanglementFidelity
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:47:59.10443+00:00
-- url     : https://prove2.me/theorems/fa8fbda0-b1ef-483b-bcdf-d84033b42b8b
-- title:
--   Entanglement fidelity $F_e(\rho,\mathcal{N}) = \langle\psi|(\mathrm{id}_R\otimes\mathcal{N})(|\psi\rangle\langle\psi|)|\psi\rangle$
-- statement:
--   **Definition 9.5.1 (Entanglement Fidelity).** Let $\rho_A$ be a state, $\mathcal{N} : \mathcal{L}(\mathcal{H}_A) \to \mathcal{L}(\mathcal{H}_A)$ a quantum channel, $|\psi\rangle_{RA}$ a purification of $\rho_A$, and $\sigma_{RA} \equiv (\mathrm{id}_R \otimes \mathcal{N}_A)(|\psi\rangle\langle\psi|_{RA})$. The entanglement fidelity is
--
--   $$
--   F_e(\rho, \mathcal{N}) \equiv \langle \psi | \sigma | \psi \rangle .
--   $$
--
--   It measures how well the channel preserves the entanglement of the input with a reference system; it does not depend on the choice of purification or of Kraus representation (Theorem 9.5.1, Exercise 9.5.2).
--
--   **Formalization Note.** `WildeQIT.entanglementFidelity ρ N := expectedFidelity ψ (N.tensorIdApply a (vecMulVec ψ (star ψ)))` with `ψ := canonicalPurification ρ` (the canonical purification $(I_R \otimes \sqrt\rho)|\Gamma\rangle$, reference indexed by a copy of `a`), `N : WildeQIT.QChannel a a` in Kraus form and `tensorIdApply` the action of $\mathrm{id}_R \otimes \mathcal{N}$.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.5.2 "Entanglement Fidelity", Definition 9.5.1 (Entanglement Fidelity).

import Definitions.Def_WildeQIT_expectedFidelity
import Definitions.Def_WildeQIT_uhlmannFidelity
import Definitions.Def_WildeQIT_diamondNorm

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.5.2, Definition 9.5.1 (Entanglement Fidelity).

For a state `ρ_A`, a channel `𝒩 : L(ℋ_A) → L(ℋ_A)`, a purification `|ψ⟩_{RA}` of `ρ_A` and
`σ_{RA} ≡ (id_R ⊗ 𝒩)(|ψ⟩⟨ψ|_{RA})`, the entanglement fidelity is `F_e(ρ, 𝒩) ≡ ⟨ψ|σ|ψ⟩`.
The purification used is the canonical one `|φ^ρ⟩ = (I_R ⊗ √ρ)|Γ⟩` (its value does not depend on
the choice, Theorem 9.5.1 / Exercise 9.5.2).
-/

open Matrix

namespace WildeQIT

/-- **Definition 9.5.1 (Entanglement Fidelity).** `F_e(ρ, 𝒩) = ⟨ψ|(id_R ⊗ 𝒩)(|ψ⟩⟨ψ|)|ψ⟩` with
`|ψ⟩` the canonical purification of `ρ`. -/
noncomputable def entanglementFidelity {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Matrix a a ℂ) (N : QChannel a a) : ℝ :=
  expectedFidelity (canonicalPurification ρ)
    (N.tensorIdApply a (vecMulVec (canonicalPurification ρ) (star (canonicalPurification ρ))))

end WildeQIT


