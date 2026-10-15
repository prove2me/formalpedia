-- Prove2me | Definitions.Def_OAI_Probability_Ising_TwoSpin
-- name    : OAI_Probability_Ising_TwoSpin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:57:24.138756+00:00
-- url     : https://prove2.me/theorems/b8af5901-2ac8-4c69-a3cf-ed8a14558736
-- title:
--   Walsh coefficients of a two-spin table: effective coupling, local fields and balancing
-- statement:
--   A two-spin table is a function $w:\{-1,+1\}\times\{-1,+1\}\to\mathbb{R}$, thought of as the unnormalized positive joint weight of two spins $s,t$. Write $\ell(s,t)=\log w(s,t)$ and abbreviate the four entries by their signs, e.g. $\ell(+,-)=\log w(+1,-1)$. The file defines the following quantities.
--
--   1. **Walsh coefficients of $\log w$.** The constant term, the effective coupling, and the effective fields on the first and on the second spin:
--
--      $$\begin{aligned} c(w)&=\tfrac14\bigl(\ell(+,+)+\ell(-,-)+\ell(+,-)+\ell(-,+)\bigr), & K(w)&=\tfrac14\bigl(\ell(+,+)+\ell(-,-)-\ell(+,-)-\ell(-,+)\bigr),\\ A(w)&=\tfrac14\bigl(\ell(+,+)+\ell(+,-)-\ell(-,+)-\ell(-,-)\bigr), & B(w)&=\tfrac14\bigl(\ell(+,+)+\ell(-,+)-\ell(+,-)-\ell(-,-)\bigr). \end{aligned}$$
--
--      For a positive table they give the expansion $w(s,t)=\exp\bigl(c(w)+K(w)\,st+A(w)\,s+B(w)\,t\bigr)$.
--
--   2. **Balanced table.** $\tilde w(s,t)=w(s,t)\,e^{-A(w)s-B(w)t}$, the table with its two effective fields removed.
--
--   3. **Table expectation.** For $f:\{-1,+1\}^2\to\mathbb{R}$,
--
--      $$\mathbb{E}_w[f]=\frac{\sum_{s,t}w(s,t)\,f(s,t)}{\sum_{s,t}w(s,t)} .$$
--
--   For a positive table the effective coupling is one quarter of the log cross-ratio, $4K(w)=\log\frac{w(+,+)\,w(-,-)}{w(+,-)\,w(-,+)}$, and it is unchanged when the table is multiplied by single-spin factors $e^{\alpha s+\beta t}$. The balanced table of a positive table has $\mathbb{E}_{\tilde w}[s]=\mathbb{E}_{\tilde w}[t]=0$ and $\mathbb{E}_{\tilde w}[st]=\tanh K(w)$. Applied to two-spin marginals of Ising models, $K$ is the effective interaction between two sites or two contracted terminal sets.
--
--   **Formalization Note** Tables are functions `Bool → Bool → ℝ` with `true` read as $+1$; the Lean names are `tableConstant`, `tableCoupling`, `tableFieldLeft`, `tableFieldRight`, `balancedTable` and `tableExpectation`. No positivity is assumed in the definitions; for tables with nonpositive entries Lean's conventions $\log 0=0$, $\log(-x)=\log x$ and division by zero giving $0$ apply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/TwoSpin.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/TwoSpin.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Walsh coefficients of the log of a positive two-spin table. -/
noncomputable def tableConstant (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w false false) +
    Real.log (w true false) + Real.log (w false true)) / 4

noncomputable def tableCoupling (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w false false) -
    Real.log (w true false) - Real.log (w false true)) / 4

noncomputable def tableFieldLeft (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w true false) -
    Real.log (w false true) - Real.log (w false false)) / 4

noncomputable def tableFieldRight (w : Bool → Bool → ℝ) : ℝ :=
  (Real.log (w true true) + Real.log (w false true) -
    Real.log (w true false) - Real.log (w false false)) / 4

noncomputable def balancedTable (w : Bool → Bool → ℝ) (s t : Bool) : ℝ :=
  w s t * Real.exp (-tableFieldLeft w * spin s - tableFieldRight w * spin t)

noncomputable def tableExpectation (w : Bool → Bool → ℝ) (f : Bool → Bool → ℝ) : ℝ :=
  (∑ s, ∑ t, w s t * f s t) / ∑ s, ∑ t, w s t

end BufferedIsing

end OAI


