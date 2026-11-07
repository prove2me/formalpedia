-- Prove2me | Definitions.Def_PlantedIQP_amplitude
-- name    : PlantedIQP_amplitude
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:17.456369+00:00
-- url     : https://prove2.me/theorems/67c53404-242e-4f5c-81ef-f706d28a482e
-- title:
--   Gaps, IQP amplitudes $a_f(x)$ and probabilities $p_f(x)$
-- statement:
--   For a Boolean function $F:\mathbb F_2^\iota\to\mathbb F_2$ on a finite index set, the **gap** and **normalized gap** are
--
--   $$
--   \mathrm{gap}(F)=\sum_{y}(-1)^{F(y)}=|\{F=0\}|-|\{F=1\}|,\qquad \mathrm{ngap}(F)=2^{-|\iota|}\,\mathrm{gap}(F).
--   $$
--
--   For a cubic polynomial $f$, the output **amplitude** of the IQP circuit $C(f)$ in the Hadamard basis and the output **probability** are
--
--   $$
--   a_f(x)=\mathrm{ngap}\big(f+\langle x,\cdot\rangle\big)=\frac1{2^n}\sum_{y\in\mathbb F_2^n}(-1)^{f(y)+\langle x,y\rangle},\qquad p_f(x)=a_f(x)^2 .
--   $$
--
--   These are the target probabilities of the XEB test; computing them is the verifier's task (Theorem 41) and the spoofer's obstacle (Conjecture 38).
--
--   **Formalization Note** The gap is defined for every function, including ones with a nonzero constant term (Lemma 40 needs them). The amplitude is the explicit formula (3); that it is the amplitude $\langle x|H^{\otimes n}C(f)H^{\otimes n}|0^n\rangle$ of the circuit is required of the honest prover in Theorem 43 (ii), not built into this definition.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Eq. (3), p.4 and Section 3.1, Eqs. (21)–(22), p.19

import Mathlib
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# Gaps, IQP output amplitudes `a_f(x)` and probabilities `p_f(x)`

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Eq. (3), p.4:
`a_g(x) = (1/2ⁿ) Σ_{y∈𝔽₂ⁿ} (−1)^{g(y)+x·y} =: ngap(g + ⟨x, ·⟩)`; Section 3.1, p.19: "The amplitudes
of |f⟩ in the Hadamard basis a_f(x) := ⟨x| H^{⊗n} |f⟩, (21) yield the corresponding probabilities
p_f(x) = a_f(x)² of observing x when measuring in this basis", with
"ngap(f) := (1/2ⁿ)(|{x : f(x) = 0}| − |{x : f(x) = 1}|). (22)"

**Formalization Note.**
* `gap F = Σ_y (−1)^{F(y)} ∈ ℤ` is the unnormalized gap the source uses in Eq. (52) and Theorem 36,
  and `ngap F = gap F / 2^{|ι|}`; both are defined for every function `F : (ι → 𝔽₂) → 𝔽₂` on a finite
  index set, including functions with a nonzero constant term (Lemma 40 needs them).
* `amp f x` is the explicit formula (3). That it equals `⟨x|H^{⊗n} C(f) H^{⊗n}|0ⁿ⟩` for the IQP circuit
  is not part of this definition; Theorem 43 (ii) asks for a circuit whose measured law is `pf f`.
-/

/-- `(−1)^b` for `b ∈ 𝔽₂`, as an integer. -/
def sgn (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

/-- `gap(F) = |{y : F(y) = 0}| − |{y : F(y) = 1}| = Σ_y (−1)^{F(y)}` (unnormalized, Eq. (52)). -/
def gap {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → ZMod 2) → ZMod 2) : ℤ :=
  ∑ y, sgn (F y)

/-- `ngap(F) = 2^{−|ι|} gap(F)` (Eq. (22)). -/
noncomputable def ngap {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → ZMod 2) → ZMod 2) : ℝ :=
  (gap F : ℝ) / 2 ^ Fintype.card ι

/-- The output amplitude `a_f(x) = ngap(f + ⟨x, ·⟩) = 2^{−n} Σ_y (−1)^{f(y) + ⟨x, y⟩}` (Eq. (3)). -/
noncomputable def amp {n : ℕ} (f : CubicPoly n) (x : Vec n) : ℝ :=
  ngap (fun y => f.eval y + ∑ i, x i * y i)

/-- The output probability `p_f(x) = a_f(x)²` (Section 3.1, p.19). -/
noncomputable def pf {n : ℕ} (f : CubicPoly n) (x : Vec n) : ℝ :=
  amp f x ^ 2

end PlantedIQP


