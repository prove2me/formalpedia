-- Prove2me | Definitions.Def_PermInvCC_Supplement_restrict
-- name    : PermInvCC_Supplement_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:53:00.094468+00:00
-- url     : https://prove2.me/theorems/6aa90247-c558-4f79-96e4-1b47f9a46f5e
-- title:
--   Fixed-margin restriction $f_{\rho,\sigma}$
-- statement:
--   Let $f : [q]^n \times [q]^n \to \{-1,+1,*\}$ be a partial function and let $\rho, \sigma : [q] \to \mathbb N$. The **fixed-margin restriction** $f_{\rho,\sigma}$ is the restriction of $f$ to the inputs whose histograms are $\rho$ and $\sigma$, with value undefined on all other inputs:
--
--   $$f_{\rho,\sigma}(x,y) = \begin{cases} f(x,y) & \text{if } \mathrm{hist}(x) = \rho \text{ and } \mathrm{hist}(y) = \sigma,\\ * & \text{otherwise,}\end{cases}$$
--
--   where $\mathrm{hist}(x)_a = |\{i : x_i = a\}|$.
--
--   Fixed-margin restrictions are the subproblems on which the paper's upper and lower bounds are proved: once the parties have exchanged their histograms, only the relative alignment of the strings remains to be determined.
--
--   **Formalization Note** The definition is evaluated for every $\rho,\sigma$; if one of them does not have total $n$, the restriction is nowhere defined.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.3, p.9 (PDF p.12)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_jointType

namespace PermInvCC

namespace Supplement

/-- The **fixed-margin restriction** `f_{ρ,σ}` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.3, p.9): "the
restriction of `f` to inputs with histograms `ρ` and `σ`, leaving its value undefined on all
other inputs".

**Formalization Note.** Histograms are the base `hist` (`a ↦ |{i : x_i = a}|`); "undefined" is
`none`. The definition is evaluated for every `ρ, σ : [q] → ℕ`; when one of them does not have
total `n` the restriction is nowhere defined. -/
def restrict {n q : ℕ} (f : PartialFn n q) (ρ σ : Fin q → ℕ) : PartialFn n q :=
  fun x y => if hist x = ρ ∧ hist y = σ then f x y else none

end Supplement

end PermInvCC


