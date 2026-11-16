-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_searchChannel
-- name    : RandPurIso_Completion_Supplement_searchChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:51:14.072546+00:00
-- url     : https://prove2.me/theorems/4ac33bdd-f5af-41d2-b64f-70eda2dfae05
-- title:
--   The search channel $\mathcal C_z$ and its natural dilation
-- statement:
--   Let $m,L\ge1$, $d\ge2$, $z\in\{0,1\}^m$, and let $(\phi^{(i)})_{i\in[m]}$ be $m$ families of hidden pairs. The **search channel** $\mathcal C_z$ acts on $\mathcal H([m])\otimes\mathbf{In}$: it measures the index register in the computational basis and on outcome $i$ applies $\mathsf{SAME}_i$ (built from $\phi^{(i)}$) if $z_i=0$ or $\mathsf{DIFF}_i$ if $z_i=1$, returning $i$ with the output:
--
--   $$
--   \mathcal C_z(\rho)=\sum_{i\in[m]}|i\rangle\langle i|\otimes\Phi_i\big(\langle i|\rho|i\rangle\big),\qquad \Phi_i\in\{\mathsf{SAME}_i,\mathsf{DIFF}_i\}.
--   $$
--
--   The module also defines its natural isometry dilation $|i\rangle|\psi\rangle\mapsto|i\rangle V_i|\psi\rangle\otimes|i\rangle_{\mathrm{env}}$, the Kraus family read off it, and the law of the $m$ independent families of hidden pairs ($mL$ independent Haar unitaries).
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §7.3, p. 58

import Mathlib
import Definitions.Def_RandPurIso_Completion_Supplement_hiddenDilation
import Definitions.Def_RandPurIso_Completion_Supplement_hiddenPairMeasure
open Matrix MeasureTheory

namespace RandPurIso.Completion.Supplement

/-- The block `⟨i|ρ|i⟩` of a matrix on `H([m]) ⊗ X` at index `i`. -/
def idxBlock {m : ℕ} {X : Type} (i : Fin m) (ρ : Matrix (Fin m × X) (Fin m × X) ℂ) : Matrix X X ℂ :=
  fun a b => ρ (i, a) (i, b)

/-- **The search channel `C_z`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7.3, p. 58).

For `z ∈ {0,1}^m` and `m` families of hidden pairs `U i` (`i ∈ [m]`), `C_z` acts on
`H([m]) ⊗ In`: it measures the index register in the computational basis and on outcome `i`
applies `SAME_i` (built from `U i`) if `z_i = 0` or `DIFF_i` if `z_i = 1` to the rest, returning
`i` with the output: `C_z(ρ) = Σ_i |i⟩⟨i| ⊗ Φ_i(⟨i|ρ|i⟩)`.

**Formalization Note.** Bits of `z` are `Bool` (`false = 0`), so `hiddenChannel (z i)` is SAME
when `z i = false` and DIFF when `z i = true`. -/
noncomputable def searchChannel {m L d : ℕ} (z : Fin m → Bool)
    (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (Fin m × InSp L d) (Fin m × InSp L d) ℂ) :
    Matrix (Fin m × InSp L d) (Fin m × InSp L d) ℂ :=
  fun p q => if p.1 = q.1 then hiddenChannel (z p.1) (U p.1) (idxBlock p.1 ρ) p.2 q.2 else 0

/-- The natural isometry dilation of `C_z` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7.3): `|i⟩|ψ⟩ ↦ |i⟩ V_i|ψ⟩ ⊗ |i⟩_env`, with
`V_i = V^SAME_i` or `V^DIFF_i` and a copy of the measured index kept in the environment
`H([m]) ⊗ X ⊗ B ⊗ Extra`. -/
noncomputable def searchDilation {m L d : ℕ} (z : Fin m → Bool)
    (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix ((Fin m × InSp L d) × (Fin m × HEnv L d)) (Fin m × InSp L d) ℂ :=
  fun r j => if r.1.1 = j.1 ∧ r.2.1 = j.1 then hiddenDilation (z j.1) (U j.1) (r.1.2, r.2.2) j.2 else 0

/-- The Kraus family of `C_z` read off its natural dilation; it is the operator-sum
representation used for `Sw[C_z, C_z]`. -/
noncomputable def searchKraus {m L d : ℕ} (z : Fin m → Bool)
    (U : Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin m × HEnv L d → Matrix (Fin m × InSp L d) (Fin m × InSp L d) ℂ :=
  dilKraus (searchDilation z U)

/-- The law of the `m` independent families of hidden pairs of §7.3 (`m · L` independent Haar
unitaries on `ℂ^d`). -/
noncomputable abbrev searchMeasure (m L d : ℕ) :
    Measure (Fin m → Fin L → Matrix.unitaryGroup (Fin d) ℂ) :=
  Measure.pi fun _ : Fin m => hiddenPairMeasure L d

end RandPurIso.Completion.Supplement


