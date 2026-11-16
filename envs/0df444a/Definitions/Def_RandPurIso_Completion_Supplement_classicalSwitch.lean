-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_classicalSwitch
-- name    : RandPurIso_Completion_Supplement_classicalSwitch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:41.462022+00:00
-- url     : https://prove2.me/theorems/a184c63e-7bf7-4cf8-9c12-a60143aafd72
-- title:
--   The classically controlled (dephased) switch $\widetilde{\mathrm{Sw}}[\Phi,\Psi]$
-- statement:
--   For channels $\Phi,\Psi$ on a common space $X$, the **classically controlled switch** measures the control qubit $\mathbf C$ in the computational basis and uses the outcome to choose the order of the two channels:
--
--   $$
--   \widetilde{\mathrm{Sw}}[\Phi,\Psi](\rho)=|0\rangle\langle 0|\otimes \Psi\big(\Phi(\langle 0|\rho|0\rangle)\big)+|1\rangle\langle 1|\otimes \Phi\big(\Psi(\langle 1|\rho|1\rangle)\big),
--   $$
--
--   with the same order convention as $\mathrm{Sw}[\Phi,\Psi]$ (outcome $0$: $\Phi$ first). It uses one forward query to each channel and only the channel maps themselves.
--
--   It is the simulation of the quantum switch in Appendix A, where it is shown to be within trace distance $1/2$ of $\mathrm{Sw}[\Phi,\Psi]$.
--
--   **Formalization Note** The page's identity $\widetilde{\mathrm{Sw}}=\mathrm{Sw}\circ\Delta_{\mathbf C}=\Delta_{\mathbf C}\circ\mathrm{Sw}$ is a fact of its proof, not part of the definition.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Appendix A, p. 64

import Mathlib
open Matrix

namespace RandPurIso.Completion.Supplement

/-- The block `⟨c|ρ|c⟩_C` of a matrix on `C ⊗ X` at control value `c`. -/
def ctrlBlock {X : Type} (c : Bool) (ρ : Matrix (Bool × X) (Bool × X) ℂ) : Matrix X X ℂ :=
  fun i j => ρ (c, i) (c, j)

/-- **The classically controlled (dephased) switch** `S̃w[Φ, Ψ]` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Appendix A, p. 64).

Measure the control `C` in the computational basis and use the outcome to choose the order of the
two channels: `ρ ↦ Σ_{c ∈ {0,1}} |c⟩⟨c| ⊗ O_c(⟨c|ρ|c⟩)` with `O_0 = Ψ ∘ Φ` (`Φ` first) and
`O_1 = Φ ∘ Ψ`, the order convention of `Sw[Φ, Ψ]` (§3.2). It uses one forward query to each of the
channel maps `Φ`, `Ψ`.

**Formalization Note.** Only the channel maps are used (no Kraus representation). The page's
identity `S̃w[Φ,Ψ] = Sw[Φ,Ψ] ∘ Δ_C = Δ_C ∘ Sw[Φ,Ψ]` is a fact of its proof, not part of this
definition. The control qubit is `Bool` (`false = |0⟩`). -/
def classicalSwitch {X : Type} (Φ Ψ : Matrix X X ℂ → Matrix X X ℂ)
    (ρ : Matrix (Bool × X) (Bool × X) ℂ) : Matrix (Bool × X) (Bool × X) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if p.1 then Φ (Ψ (ctrlBlock p.1 ρ)) else Ψ (Φ (ctrlBlock p.1 ρ))) p.2 q.2
    else 0

end RandPurIso.Completion.Supplement


