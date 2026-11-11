-- Prove2me | Definitions.Def_RandPurIso_Completion_contractionChannel
-- name    : RandPurIso_Completion_contractionChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:12.322165+00:00
-- url     : https://prove2.me/theorems/e1add057-fd06-4945-bd02-b7eec6b8a04e
-- title:
--   The CPTP map $\Phi_V$ of a contraction (Definition 3.4)
-- statement:
--   For a contraction $V:A\to B$ let $B_\perp=B\oplus\mathrm{Span}\{|\perp\rangle\}$. The **associated CPTP map** $\Phi_V:\mathbf L(A)\to\mathbf L(B_\perp)$ is
--   $$\Phi_V(\rho)=V\rho V^\dagger+\operatorname{Tr}\big((I_A-V^\dagger V)\rho\big)\,|\perp\rangle\langle\perp|.$$
--   It outputs the special state $|\perp\rangle$ when the map "fails".
--
--   **Formalization Note** $B_\perp$ is `Option B` with `none` $=\perp$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.4, p. 18

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **The CPTP map `Φ_V` of a contraction** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.4, p. 18):
`Φ_V(ρ) = VρV† + Tr((I_A − V†V)ρ) |⊥⟩⟨⊥|`, a map `L(A) → L(B ⊕ Span{|⊥⟩})`.

**Formalization Note.** `B⊥ = B ⊕ Span{|⊥⟩}` is `Option B` with `none = ⊥`. The formula is
written for every matrix `K`; it is the paper's `Φ_V` when `K` is a contraction. -/
noncomputable def contractionChannel {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (K : Matrix Y X ℂ) (ρ : Matrix X X ℂ) : Matrix (Option Y) (Option Y) ℂ :=
  fun i j => match i, j with
    | some b, some b' => (K * ρ * Kᴴ) b b'
    | none, none => ((1 - Kᴴ * K) * ρ).trace
    | _, _ => 0

end RandPurIso.Completion


