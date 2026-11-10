-- Prove2me | Definitions.Def_TolProdTest_omegaHi
-- name    : TolProdTest_omegaHi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:14.904845+00:00
-- url     : https://prove2.me/theorems/e1c463a8-985f-4d4a-9336-cab78ef48ef4
-- title:
--   Successive compressions $\omega^{\mathrm{hi}}_c$, $\omega^{\mathrm{lo}}_c$ of Lemma 3.6
-- statement:
--   Fix a coloring $C:[n]\to[q]$, an integer $R$ and $\rho$. For each colour $c$ let $\Pi^{\mathrm{hi}}_c=\mathbf 1_{(1/R,1]}(\rho_c)$ (extended by the identity outside $B_c$), $\Pi^{\mathrm{lo}}_c=I-\Pi^{\mathrm{hi}}_c$, and $\Pi^{\mathrm{hi}}_{<c}=\prod_{j<c}\Pi^{\mathrm{hi}}_j$. Set $\omega^{\mathrm{hi}}_0=\rho$ and
--
--   $$
--   \omega^{\mathrm{hi}}_c=\Pi^{\mathrm{hi}}_c\Pi^{\mathrm{hi}}_{<c}\,\rho\,\Pi^{\mathrm{hi}}_{<c}\Pi^{\mathrm{hi}}_c,\qquad
--   \omega^{\mathrm{lo}}_c=\Pi^{\mathrm{lo}}_c\Pi^{\mathrm{hi}}_{<c}\,\rho\,\Pi^{\mathrm{hi}}_{<c}\Pi^{\mathrm{lo}}_c .
--   $$
--
--   After all $q$ colours, $\omega^{\mathrm{hi}}_q=(\bigotimes_c\Pi^{\mathrm{hi}}_c)\rho(\bigotimes_c\Pi^{\mathrm{hi}}_c)$ is the bounded-rank core, and the $\omega^{\mathrm{lo}}_c$ are the discarded parts.
--
--   **Formalization Note** Colours are 0-based (`Fin q`): `omegaHi C R ρ m` compresses by the high projectors of the first $m$ colours (the paper's $\omega^{\mathrm{hi}}_m$), and `omegaLo C R ρ c` uses the colours $j<c$ in the order of `Fin q`.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.6, eq. (53), p.14

import Mathlib
import Definitions.Def_TolProdTest_blockMarginal
import Definitions.Def_TolProdTest_highProj

set_option autoImplicit false

namespace TolProdTest

/-- `Π^hi_c := 1_{(1/R,1]}(ρ_c)`, lifted to the whole space, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.6, p.14: "the projector to the
eigenspaces of ρ_c with eigenvalues larger than 1/R". The block projector is `highProj (ρ_c) R`, the
functional calculus of the indicator of `(1/R, 1]`. -/
noncomputable def piHi {n d q : ℕ} (C : Fin n → Fin q) (R : ℕ)
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (c : Fin q) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  liftBlock C c (highProj (blockMarginal C c ρ) R)

/-- `∏_{j < m} Π^hi_j`: the product of the high projectors of the first `m` colours (0-based; the factors act on
disjoint blocks and commute). `piHiLt … 0 = I`. -/
noncomputable def piHiLt {n d q : ℕ} (C : Fin n → Fin q) (R : ℕ)
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (m : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  (((List.finRange q).filter fun j => decide (j.val < m)).map (piHi C R ρ)).prod

/-- **Successive high compressions** `ω^hi`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (53), p.14: "Set ω^hi_0 := ρ and
ω^hi_c := Π^hi_c Π^hi_{<c} ρ Π^hi_{<c} Π^hi_c". With 0-based colours, `omegaHi C R ρ m` is the compression of `ρ`
by the high projectors of the first `m` colours, i.e. the paper's `ω^hi_m`; `omegaHi C R ρ 0 = ρ` and
`omegaHi C R ρ q = (⊗_c Π^hi_c) ρ (⊗_c Π^hi_c)`. -/
noncomputable def omegaHi {n d q : ℕ} (C : Fin n → Fin q) (R : ℕ)
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (m : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  piHiLt C R ρ m * ρ * piHiLt C R ρ m

/-- **Discarded low parts** `ω^lo_c := Π^lo_c Π^hi_{<c} ρ Π^hi_{<c} Π^lo_c`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (53), p.14, with
`Π^lo_c := I − Π^hi_c`. Colour `c : Fin q` is 0-based: `Π^hi_{<c}` is the product over the colours `j` with
`j < c`. -/
noncomputable def omegaLo {n d q : ℕ} (C : Fin n → Fin q) (R : ℕ)
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (c : Fin q) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  (1 - piHi C R ρ c) * piHiLt C R ρ c.val * ρ * piHiLt C R ρ c.val * (1 - piHi C R ρ c)

end TolProdTest


