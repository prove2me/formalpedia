-- Prove2me | Definitions.Def_JencovaRenyi_infNorm
-- name    : JencovaRenyi_infNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:26.222018+00:00
-- url     : https://prove2.me/theorems/9fbbce91-a9c7-4eac-a6c7-9e614e12292c
-- title:
--   The norm $\|\cdot\|_{\infty,\varphi}$ of $L_\infty(\mathcal M,\varphi)$
-- statement:
--   For a normal positive functional $\varphi$ and $k\in L_1(\mathcal M)$ put
--   $$
--   \|k\|_{\infty,\varphi} = \inf\{\|x\| : x\in\mathcal M,\ h_x = k\} \in [0,\infty],
--   $$
--   which is $\infty$ exactly when $k \notin L_\infty(\mathcal M,\varphi) = \{h_x : x\in\mathcal M\}$. For faithful $\varphi$ the embedding is injective and this is the paper's $\|h_x\|_{\infty,\varphi} := \|x\|$ (p.4); for non-faithful $\varphi$ with support $e$, $h_x = h_{exe}$ and the infimum is $\|exe\|$, the norm of $L_\infty(e\mathcal Me, \varphi|_{e\mathcal Me})$ (p.10).
--
--   It is the norm of the space $X_0$ in the interpolation couple $(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$.
--
--   **Formalization Note** Valued in `ℝ≥0∞`; the value $\infty$ encodes "not in the space".
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.1, p.4; §3, p.10

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The norm of `L_∞(M, φ) = {h_x : x ∈ M} ⊆ L_1(M)` (Jenčová, arXiv:1609.08462v4, §2.1, p.4:
`‖h_x‖_{∞,φ} := ‖x‖`), as an extended gauge on all of `L_1(M)`:
`‖k‖_{∞,φ} = inf {‖x‖ : h_x = k}`, which is `⊤` exactly when `k ∉ L_∞(M, φ)`.

**Formalization Note.** For faithful `φ` the map `x ↦ h_x` is injective and this is `‖x‖`. For a
non-faithful `φ` with support `e` (p.10), `h_x = h_y` iff `exe = eye`, so the infimum is `‖exe‖`,
the norm of `L_∞(eMe, φ|_{eMe})`. The value `⊤` encodes "not in the space". -/
noncomputable def infNorm {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A)
    (φ k : Predual A) : ℝ≥0∞ :=
  ⨅ (x : A) (_ : symmEmbed S φ x = k), (‖x‖₊ : ℝ≥0∞)

end JencovaRenyi


