-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_qswitch
-- name    : RandPurIso_Completion_Supplement_qswitch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:26.496509+00:00
-- url     : https://prove2.me/theorems/f1ecbe8d-3dd2-46f4-a75e-afb311ffeb87
-- title:
--   The quantum switch $\mathrm{Sw}[\Phi,\Psi]$ of two channels given by Kraus families
-- statement:
--   Let $\Phi(\rho)=\sum_a K^\Phi_a\rho(K^\Phi_a)^\dagger$ and $\Psi(\rho)=\sum_b K^\Psi_b\rho(K^\Psi_b)^\dagger$ be channels on a common finite-dimensional space $X$, given by Kraus families over finite index sets. The **quantum switch** is the map on $\mathbf C\otimes X$, with $\mathbf C$ a control qubit,
--
--   $$
--   \mathrm{Sw}[\Phi,\Psi](\rho)=\sum_{a,b}S_{a,b}\,\rho\,S_{a,b}^\dagger,\qquad S_{a,b}=|0\rangle\langle 0|\otimes K^\Psi_bK^\Phi_a+|1\rangle\langle 1|\otimes K^\Phi_aK^\Psi_b .
--   $$
--
--   On control $0$ it applies $\Phi$ and then $\Psi$; on control $1$ it applies $\Psi$ and then $\Phi$, coherently. The **self-switch** of $\Phi$ is $\mathrm{Sw}[\Phi,\Phi]$.
--
--   The switch is the resource whose query cost is studied in §7 and Appendix A: one self-switch distinguishes the SAME and DIFF ensembles perfectly.
--
--   **Formalization Note** The switch is defined on Kraus families (the page notes the result does not depend on the representation); the control qubit is `Bool` with `false` $=|0\rangle$. That a family is trace preserving is a hypothesis where needed.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.2, p. 21

import Mathlib
open Matrix

namespace RandPurIso.Completion.Supplement

/-- The Kraus operator `S_{a,b} = |0⟩⟨0| ⊗ K^Ψ_b K^Φ_a + |1⟩⟨1| ⊗ K^Φ_a K^Ψ_b` of the quantum switch
(Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.2, p. 21), for Kraus families `K = K^Φ` and `K' = K^Ψ` on a common space `X`. The control
qubit is `Bool`, with `false = |0⟩` and `true = |1⟩`. -/
def switchKraus {X ι κ : Type} [Fintype X] (K : ι → Matrix X X ℂ) (K' : κ → Matrix X X ℂ)
    (a : ι) (b : κ) : Matrix (Bool × X) (Bool × X) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if p.1 then (K a * K' b) p.2 q.2 else (K' b * K a) p.2 q.2)
    else 0

/-- **The quantum switch** `Sw[Φ, Ψ]` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.2, p. 21).

For channels `Φ(ρ) = Σ_a K^Φ_a ρ (K^Φ_a)†` and `Ψ(ρ) = Σ_b K^Ψ_b ρ (K^Ψ_b)†` on a common space `X`,
`Sw[Φ, Ψ](ρ) = Σ_{a,b} S_{a,b} ρ S_{a,b}†` on `C ⊗ X`, with
`S_{a,b} = |0⟩⟨0| ⊗ K^Ψ_b K^Φ_a + |1⟩⟨1| ⊗ K^Φ_a K^Ψ_b`: control `0` applies `Φ` then `Ψ`, control `1`
applies `Ψ` then `Φ`. The self-switch of `Φ` is `Sw[Φ, Φ]`.

**Formalization Note.** The switch is defined on Kraus families (`K : ι → Matrix X X ℂ`,
`K' : κ → Matrix X X ℂ` over finite index types), as the page defines it; the page notes that the
result does not depend on the chosen operator-sum representations. That a family is a channel
(`Σ_a K_a† K_a = 1`) is a hypothesis where it is needed. The control qubit is `Bool`
(`false = |0⟩`). -/
noncomputable def qswitch {X ι κ : Type} [Fintype X] [Fintype ι] [Fintype κ]
    (K : ι → Matrix X X ℂ) (K' : κ → Matrix X X ℂ) (ρ : Matrix (Bool × X) (Bool × X) ℂ) :
    Matrix (Bool × X) (Bool × X) ℂ :=
  ∑ a, ∑ b, switchKraus K K' a b * ρ * (switchKraus K K' a b)ᴴ

end RandPurIso.Completion.Supplement


