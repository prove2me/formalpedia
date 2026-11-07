-- Prove2me | Definitions.Def_MultiSelectPandora_thetaSeq
-- name    : MultiSelectPandora_thetaSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:32.000329+00:00
-- url     : https://prove2.me/theorems/02095e16-c5ab-4a70-8c00-cb924441f652
-- title:
--   The points of the large-value grid
-- statement:
--   Set $\theta_1:=\theta$. As long as $\varphi(\theta_l)>\varepsilon\widehat{\mathrm{OPT}}$, let $\theta_{l+1}$ be the unique $x>\theta_l$ with
--   $$\varphi(x)=\varphi(\theta_l)-\varepsilon\widehat{\mathrm{OPT}}.$$
--   Once the condition fails the sequence stays constant.
--
--   **Formalization Note** The body of Definition 3.21 writes $\varepsilon\mathrm{OPT}$ "for clarity". Footnote 1 says that the algorithm uses $\varepsilon\widehat{\mathrm{OPT}}$, since $\mathrm{OPT}$ is not known, and this is the footnote's grid. The unique solution is written as an `sInf` of the solution set.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.21 with footnote 1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_OPThat
import Definitions.Def_MultiSelectPandora_phi__4119c7
import Definitions.Def_MultiSelectPandora_theta

namespace MultiSelectPandora

/-- **The points `θ_1, θ_2, …` of the large-value grid, before its last point.** Beyhaghi–Han–Luqman manuscript, Definition 3.21
with footnote 1, p.15 (PDF p.16): `θ_1 := θ` and, as long as `φ(θ_l) > ε OPT^`, `θ_{l+1}` is the unique `x > θ_l` with
`φ(x) = φ(θ_l) − ε OPT^`.

**Formalization Note.** The body writes `ε OPT` "for clarity"; footnote 1 says the algorithm uses `ε OPT^`, since `OPT` is not
known. The grid here is the footnote's. The solution is unique, so the `sInf` of the solution set is that solution. Once the
loop's condition fails the sequence stays constant, so it is a sequence on all of `ℕ`. -/
noncomputable def thetaSeq (I : Inst) (k : ℕ) (ε : ℝ) : ℕ → ℝ
  | 0 => theta I k ε
  | l + 1 =>
    if ε * OPThat I k < phi I (thetaSeq I k ε l) then
      sInf {x : ℝ | thetaSeq I k ε l < x ∧ phi I x = phi I (thetaSeq I k ε l) - ε * OPThat I k}
    else thetaSeq I k ε l

end MultiSelectPandora


