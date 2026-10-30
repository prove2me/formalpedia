-- Prove2me | Definitions.Def_PorteusGenSS_PFIntegrable
-- name    : PorteusGenSS_PFIntegrable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:28.600892+00:00
-- url     : https://prove2.me/theorems/a3e7c768-b2be-4f03-a090-5b77474928f3
-- title:
--   PF-integrable function
-- statement:
--   A function $f:\mathbb R\to\mathbb R$ is **PF-integrable** if $f*\psi$ exists (is finite) whenever $\psi$ is a Pólya frequency function: for every PFF $\psi$ and every $y\in\mathbb R$ the function $\xi\mapsto f(y-\xi)\psi(\xi)$ is Lebesgue integrable.
--
--   The paper assumes the one-period cost $m$ and the terminal cost $f_0$ to be PF-integrable; every function bounded piecewise by polynomials is.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, p. 413, and Appendix, p. 423

import Mathlib
import Definitions.Def_PorteusGenSS_IsPFF

open MeasureTheory

namespace PorteusGenSS

/-- **PF-integrable function.**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, p. 413: "We assume m is PF-integrable; i.e., m∗φ exists whenever φ is a Pólya
frequency function."; Appendix, p. 423: "Recall that a function f is PF-integrable if f∗φ exists
(is finite) whenever φ is PFF."

`PFIntegrable f` says that for every Pólya frequency function `ψ` and every `y ∈ ℝ` the function
`ξ ↦ f(y − ξ) ψ(ξ)` is Lebesgue integrable, i.e. `f∗ψ(y)` exists as a real number.

**Formalization Note.** "Exists" means "is a real number" (§X), so the convolution integral
is finite at every point; for a Lebesgue integral this is integrability of the integrand. -/
def PFIntegrable (f : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, IsPFF ψ → ∀ y : ℝ, Integrable (fun ξ => f (y - ξ) * ψ ξ)

end PorteusGenSS


