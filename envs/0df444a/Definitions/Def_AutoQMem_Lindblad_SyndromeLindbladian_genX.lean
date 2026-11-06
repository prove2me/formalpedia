-- Prove2me | Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_genX
-- name    : AutoQMem_Lindblad_SyndromeLindbladian_genX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:27.082421+00:00
-- url     : https://prove2.me/theorems/30bc7c06-52c2-49e8-bad4-0c888d07136d
-- title:
--   Induced sector processes: rates $r^{(X)}_i$, $r^{(Z)}_i$ and generators $G_X(t)$, $G_Z(t)$
-- statement:
--   A syndrome-based Lindbladian induces continuous-time Markov chains on $\Omega_X=\Omega_Z=\mathbb F_2^n$ whose transitions are single-bit flips $x\mapsto x\oplus\hat e_i$, at the rates
--   $$r^{(X)}_i(s,t)=\Gamma^{(X)}_i(t)(s),\qquad r^{(Z)}_i(s,t)=\Gamma^{(Z)}_i(t)(s),$$
--   the syndrome eigenvalues of the flip-rate operators. The backward generators are
--   $$(G_X(t)h)(e)=\sum_{i=1}^nr^{(X)}_i(H_Xe,t)\bigl(h(e\oplus\hat e_i)-h(e)\bigr),$$
--   and $G_Z(t)$ likewise with $H_Z$ and $r^{(Z)}_i$.
--
--   **Formalization Note** The rates are real and nonnegative for $t\ge0$ (the flip-rate operators are positive semidefinite and lie in the sector algebra); the real part only fixes the type.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.29, eq. (47), p. 23 (PDF p. 25); Definition 2.30, eqs. (48)–(49), p. 23

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian
import Definitions.Def_AutoQMem_Lindblad_CSSCode_eigX
import Definitions.Def_AutoQMem_Lindblad_sectorGen
open Matrix

namespace AutoQMem.Lindblad

namespace SyndromeLindbladian

variable {n mX mZ : ℕ} {C : CSSCode n mX mZ} {ι : Type} [Fintype ι]

/-- **X-sector transition rates** `r^{(X)}_i(s, t) := Γ^{(X)}_i(t)(s)`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.29,
eq. (47), p. 23 (PDF 25).

**Formalization Note.** `Γ^{(X)}_i(t)(s)` is the syndrome eigenvalue `eigX`; it is real and
nonnegative for `t ≥ 0`, `s ∈ Σ_X` (`Γ` is positive semidefinite and lies in `A_X`), and `.re`
only fixes the type. -/
noncomputable def rateX (L : SyndromeLindbladian C ι) (t : ℝ) (i : Fin n) (s : Fin mX → ZMod 2) : ℝ :=
  (C.eigX (flipRateX (L.jump t) i) s).re

/-- **Z-sector transition rates** `r^{(Z)}_i(s, t) := Γ^{(Z)}_i(t)(s)` (Definition 2.29, eq. (47)). -/
noncomputable def rateZ (L : SyndromeLindbladian C ι) (t : ℝ) (i : Fin n) (s : Fin mZ → ZMod 2) : ℝ :=
  (C.eigZ (flipRateZ (L.jump t) i) s).re

/-- **X-sector backward generator `G_X(t)`** of the induced sector process (Definition 2.30,
eq. (48), p. 23): `(G_X(t)h)(e) = Σ_i r^{(X)}_i(H_X e, t)(h(e ⊕ ê_i) − h(e))`. -/
noncomputable def genX (L : SyndromeLindbladian C ι) (t : ℝ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  sectorGen C.HX (L.rateX t)

/-- **Z-sector backward generator `G_Z(t)`** (Definition 2.30, eq. (49)):
`(G_Z(t)h)(e) = Σ_i r^{(Z)}_i(H_Z e, t)(h(e ⊕ ê_i) − h(e))`. -/
noncomputable def genZ (L : SyndromeLindbladian C ι) (t : ℝ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  sectorGen C.HZ (L.rateZ t)

end SyndromeLindbladian

end AutoQMem.Lindblad


