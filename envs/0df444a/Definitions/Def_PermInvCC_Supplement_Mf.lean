-- Prove2me | Definitions.Def_PermInvCC_Supplement_Mf
-- name    : PermInvCC_Supplement_Mf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:53:33.268181+00:00
-- url     : https://prove2.me/theorems/7c25dee6-9225-411f-8256-3f3860f6e498
-- title:
--   The characterization parameter $M(f)=\max_{\rho,\sigma}h_{f_{\rho,\sigma}}^{-1}$
-- statement:
--   For a partial function $f : [q]^n \times [q]^n \to \{-1,+1,*\}$ define
--
--   $$M(f) := \max_{\rho,\sigma}\; h_{f_{\rho,\sigma}}^{-1},$$
--
--   where the maximum is over all pairs of nonnegative integer histograms $\rho, \sigma$ of total $n$, $f_{\rho,\sigma}$ is the fixed-margin restriction, and $h_g$ is the separation parameter of Definition 2.4: the minimum, over oppositely labelled promised joint types $T, U$ of $g$, of the type separation $h(T,U)$, with $h_g = 1$ when $g$ has at most one promised label.
--
--   $M(f)$ governs the quantum communication complexity of permutation-invariant functions up to a factor $O_q(\log n)$ (Theorem 1.2).
--
--   **Formalization Note** A histogram of total $n$ is written as a map $[q] \to \{0,\dots,n\}$ with entry sum $n$, so the index set is finite and, for $q \ge 1$, nonempty; the real supremum is then the maximum.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.2, p.2 (PDF p.5), restated p.22 (PDF p.25)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_hg
import Definitions.Def_PermInvCC_Supplement_restrict

namespace PermInvCC

namespace Supplement

/-- The **characterization parameter** `M(f) := max_{ρ,σ} h_{f_{ρ,σ}}^{-1}` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, Theorem 1.2, p.2, restated p.22): the maximum over all pairs of nonnegative integer
histograms `ρ, σ` of total `n` of the inverse separation parameter of the fixed-margin
restriction `f_{ρ,σ}`, where a restriction with at most one promised label has `h = 1`.

**Formalization Note.** A histogram of total `n` has entries in `{0, …, n}`, so it is written as
`ρ : Fin q → Fin (n+1)` with `∑ ρ_a = n`; the index set is finite and (for `q ≥ 1`) nonempty, so
the real `⨆` is the maximum. `h` is the base `hg`, which is `1` when no oppositely labelled
promised pair exists (the paper's convention for "at most one promised label"). -/
noncomputable def Mf {n q : ℕ} (f : PartialFn n q) : ℝ :=
  ⨆ p : {p : (Fin q → Fin (n + 1)) × (Fin q → Fin (n + 1)) //
      ∑ a, (p.1 a : ℕ) = n ∧ ∑ b, (p.2 b : ℕ) = n},
    (hg (restrict f (fun a => (p.1.1 a : ℕ)) (fun b => (p.1.2 b : ℕ))))⁻¹

end Supplement

end PermInvCC


