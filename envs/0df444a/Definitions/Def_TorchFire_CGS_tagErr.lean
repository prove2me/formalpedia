-- Prove2me | Definitions.Def_TorchFire_CGS_tagErr
-- name    : TorchFire_CGS_tagErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:43:47.373222+00:00
-- url     : https://prove2.me/theorems/fc89ba25-15df-45c7-b107-e929261fbe10
-- title:
--   The flame vector $|K\rangle$, the tag projector $\Pi$, $e_{\mathrm{tag}}$ (30) and $e_{\mathrm{cl}}$ (29)
-- statement:
--   1. The honest CGS flame vector $|K\rangle_{YU}=2^{-r/2}\sum_{y}|y\rangle_Y|W_y\rangle_U$ (23).
--   2. The tag projector $\Pi$ of Remark 4.25: the diagonal projector on $(Z,Y,R_0,R_1)$ onto the basis values with $\mathrm{Fire.Check}(z,(y,\tau_0,\tau_1))=1$, identity on all other registers, extended by the identity on an arbitrary finite register $E$.
--   3. **The coherent tag error**
--   $$e_{\mathrm{tag}}(E)=\sup_{\Vert|\psi\rangle_{ZE}\Vert=1}\big\Vert(I-\Pi)\,\mathrm{Fire.Tag}^O(|K\rangle\otimes|\psi\rangle_{ZE}\otimes|0\rangle)\big\Vert^2$$
--   ((30), (51)), with $|0\rangle$ the response and signing workspace.
--   4. **The cloning error** $e_{\mathrm{cl}}=D(\mathrm{Fire.Clone}^O(pk,s,|K\rangle\langle K|),|K\rangle\langle K|^{\otimes2})$ ((29), (51)).
--
--   **Formalization Note** The supremum is a real supremum over the unit vectors of $Z\otimes E$; the set of values is bounded by $1$ and nonempty for nonempty $E$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), (23) p.27; Remarks 4.24–4.25 (29)–(30) p.29; (51) p.54

import Mathlib
import Definitions.Def_TorchFire_CGS_cloneChan

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

variable {mu : ℕ}

/-- **The honest CGS flame vector** `|K⟩_{YU} = 2^{−r/2} Σ_{y ∈ {0,1}^r} |y⟩_Y |W_y⟩_U` (23), p.27
(Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held
version sha256 4e43d2f2…afd593). -/
noncomputable def flameVec (ω : Sample mu) : KReg mu → ℂ :=
  fun f => (((Real.sqrt 2 : ℝ) : ℂ) ^ r mu)⁻¹ * cosetState ω.1 f.1 f.2

/-- **The tag projector `Π`** of Remark 4.25 (p.29) on the tag registers extended by a register `E`:
the diagonal projector onto the basis values of `(Z, Y, R_0, R_1)` with
`Fire.Check(z, (y, τ_0, τ_1)) = 1` (a ⊥-flagged response is a malformed tag), the identity on all
other registers. -/
noncomputable def tagProj (ω : Sample mu) (E : Type) [Fintype E] [DecidableEq E] :
    Matrix (TagSpace mu × E) (TagSpace mu × E) ℂ :=
  Matrix.diagonal fun p => if checkIn ω p.1.2.1 (tagOf p.1) then 1 else 0

/-- **The coherent tag error** `sup_{‖|ψ⟩_{ZE}‖=1} ‖(I − Π) Fire.Tag^O(|K⟩ ⊗ |ψ⟩_{ZE} ⊗ |0⟩)‖²`
((30), Remark 4.25, p.29; `e_tag` of (51), p.54), with `Fire.Tag^O` and `Π` extended by the identity
on `E`, and `|0⟩` the response and signing workspace registers.

**Formalization Note** The supremum is a real `⨆` over the unit vectors of `Z ⊗ E`; the set of values
is bounded (by `1`, `Fire.Tag^O` being unitary) and nonempty for nonempty `E`, so it is the true
supremum. -/
noncomputable def tagErr (ω : Sample mu) (E : Type) [Fintype E] [DecidableEq E] : ℝ :=
  ⨆ ψ : {ψ : Bits (ell mu) × E → ℂ // l2norm ψ = 1},
    l2norm (((1 - tagProj ω E) * liftOn (fun p : TagSpace mu × E => (p.1, p.2)) (tag ω)).mulVec
      (fun p : TagSpace mu × E =>
        if p.1.2.2 = tagWs0 then flameVec ω p.1.1 * ψ.1 (p.1.2.1, p.2) else 0)) ^ 2

/-- **The CGS cloning error** `e_cl = D(Fire.Clone^O(pk, s, |K⟩⟨K|), |K⟩⟨K|^{⊗2})` ((29), Remark
4.24, p.29; (51), p.54). -/
noncomputable def cloneErr (ω : Sample mu) (pk s : Bits (hl mu)) : ℝ :=
  traceDist (cloneKey ω pk s (ketbra (flameVec ω)))
    (ketbra fun p : KReg mu × KReg mu => flameVec ω p.1 * flameVec ω p.2)

end TorchFire.CGS


