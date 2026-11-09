-- Prove2me | Definitions.Def_OracleStateHSP_fracOracle
-- name    : OracleStateHSP_fracOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:45.135658+00:00
-- url     : https://prove2.me/theorems/57480272-4b8c-4580-a639-333b8ab23664
-- title:
--   Fractional oracle $O^\varepsilon_f$ (eq. (56))
-- statement:
--   For $\varepsilon \in (0, 1]$, the **fractional oracle** is, in block form with respect to the flag qubit,
--   $$
--   O^\varepsilon_f = \begin{pmatrix} \sqrt{1-\varepsilon}\, I & -\sqrt{\varepsilon}\, O_f \\ \sqrt{\varepsilon}\, O_f & \sqrt{1-\varepsilon}\, I \end{pmatrix},
--   $$
--   where $O_f$ is the Padded Simon oracle $O_{\tilde f}$ of Definition 4.8. Entrywise, the $((a, p), (b, q))$ entry is $\sqrt{1-\varepsilon}\,\delta_{pq}$ if $a = b$, $-\sqrt\varepsilon\,(O_f)_{pq}$ if $(a, b) = (0, 1)$, and $\sqrt\varepsilon\,(O_f)_{pq}$ if $(a, b) = (1, 0)$.
--
--   **Formalization Note** The flag is the outer index (rows: output flag). The definition is entrywise as printed, not the factored form of (57)–(58), which are separate statements.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (56), p.39

import Mathlib
import Definitions.Def_OracleStateHSP_FlagQ
import Definitions.Def_OracleStateHSP_paddedOracle

namespace OracleStateHSP

/-- The fractional oracle `O^ε_f` of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (56), p.39, written in block form with respect to
the flag qubit: `O^ε_f = [ √(1−ε) I , −√ε O_f ; √ε O_f , √(1−ε) I ]`, with `O_f` the Padded Simon
oracle of Definition 4.8 (eq. (52)). Entrywise, for flags `a, b` and inner indices `p, q`:
`√(1−ε) δ_pq` if `a = b`, `−√ε (O_f)_pq` if `(a, b) = (0, 1)`, `√ε (O_f)_pq` if `(a, b) = (1, 0)`.

**Formalization Note.** The flag is the outer index (row flag, column flag). `ε` is real; `√·` is
`Real.sqrt` cast to `ℂ`. The definition is entrywise as printed, not in the factored form of
eqs. (57)–(58). -/
noncomputable def fracOracle (ε : ℝ) (r : ℕ) {m : ℕ} (f : V m → V m) :
    Matrix (FlagQ r m) (FlagQ r m) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then (Real.sqrt (1 - ε) : ℂ) * (if p.2 = q.2 then 1 else 0)
    else if p.1 = 0 then -(Real.sqrt ε : ℂ) * paddedOracle r f p.2 q.2
    else (Real.sqrt ε : ℂ) * paddedOracle r f p.2 q.2

end OracleStateHSP


