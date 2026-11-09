-- Prove2me | Definitions.Def_SharpConsist_psi
-- name    : SharpConsist_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:52.014059+00:00
-- url     : https://prove2.me/theorems/83f6b59d-d7b5-4804-8ced-4998ea75dc5c
-- title:
--   The reference profile $\psi$
-- statement:
--   For $T$ and $m$ as above, the **reference profile** is
--   $$\psi(s)=v(s)+\phi_m(s),\qquad s\in[0,m+1].$$
--   It is the value $F_\delta$ takes on the balanced band $|u|\le\delta$, as a function of the normalized size $s$ alone.
--
--   **Formalization Note.** Defined for every real $s$; the paper uses it on $[0,m+1]$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, p.15

import Mathlib
import Definitions.Def_SharpConsist_F

namespace SharpConsist

/-- The **reference profile** `ψ(s) = v(s) + ϕ_m(s)` (for `s ∈ [0, m + 1]`). Fu–Zhang–Tao,
arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, p.15.

**Formalization Note.** Defined for every real `s`; the paper uses it on `[0, m + 1]`. -/
noncomputable def psi (T : ℝ) (m : ℕ) (s : ℝ) : ℝ := v T s + phiM m s

end SharpConsist


