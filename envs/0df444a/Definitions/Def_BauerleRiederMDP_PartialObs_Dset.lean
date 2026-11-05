-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Dset
-- name    : BauerleRiederMDP_PartialObs_Dset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:14.975385+00:00
-- url     : https://prove2.me/theorems/b379d2fd-f2b3-4dc0-8b92-3a0ffde0029f
-- title:
--   The admissible investments $D(x)$ under partial observation
-- statement:
--   For wealth $x$, interest rate $i$ and utility domain $\operatorname{dom}U$, the set of admissible investments is
--   $$
--   D(x):=\big\{a\in\mathbb R^d \;\big|\; (1+i)\big(x+a\cdot R(y)\big)\in\operatorname{dom}U\ \text{a.s.}\big\}.
--   $$
--   The book notes that by (FM)(ii) this set does not depend on the hidden state $y$, so $D(x)$ is well defined.
--
--   **Formalization Note** The set is taken as the intersection over all $y\in E_Y$; when the sets for different $y$ coincide (as the book asserts, and as Theorem 6.1.1 assumes) it is each of them.
-- source:
--   Bäuerle & Rieder (2011), §6.1, pp.176–177 (PDF 189–190)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The admissible investments `D(x)`** of the terminal wealth problem with partial
observation.
Bäuerle & Rieder (2011), §6.1, p.176 (PDF 189): `D(x) := {a ∈ ℝ^d | (1 + i)(x + a · R(y)) ∈ dom U
IP-a.s.}`, and p.177: "Note that in view of FM (ii) `D(x)` does not depend on `y ∈ E_Y` and hence
`D(x)` is well-defined."

**Formalization Note.** Lean takes the intersection over all `y ∈ E_Y` of the sets
`{a | (1 + i)(x + a · R(y)) ∈ dom U a.s.}`; when these sets do not depend on `y` (the book's
remark, assumed in Theorem 6.1.1), this is each of them. -/
def Dset {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℝ) (domU : Set ℝ)
    (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ y, ∀ᵐ z ∂M.QR y, (1 + i) * (x + a ⬝ᵥ z) ∈ domU}

end BauerleRiederMDP.PartialObs


