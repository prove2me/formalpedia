-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_setLast
-- name    : MultiSelectPandora_Supplement_setLast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:32:27.265099+00:00
-- url     : https://prove2.me/theorems/5f15f35d-64ef-4f8c-9126-015e3d4f5ee0
-- title:
--   The state $(\alpha[1:k-1],x)$
-- statement:
--   For a vector $\alpha=(\alpha_1,\dots,\alpha_k)$ and a real $x$, $(\alpha[1:k-1],x)$ is the vector $(\alpha_1,\dots,\alpha_{k-1},x)$: the last entry $\alpha_k$ is replaced by $x$.
--
--   Theorem 4.10 compares the policy at $(U,\alpha)$ with the policy at $(U,(\alpha[1:k-1],0))$, and the phase threshold is defined through the states $(\alpha[1:k-1],x)$.
--
--   **Formalization Note** The entry $\alpha_k$ is index $k-1$ of a vector indexed by $\mathrm{Fin}\,k$; at $k=0$ the vector is returned unchanged (never used).
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.5 (PDF p.6); Definition 4.2, p.18 (PDF p.19); Theorem 4.10, p.22 (PDF p.23)

import Mathlib

namespace MultiSelectPandora.Supplement

/-- **`(α[1 : k−1], x)`: the state with its last entry `α_k` replaced by `x`.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.2, p.5
(PDF p.6) (notation `α[i : j]` and concatenation) and §4.2, p.22 (PDF p.23).

**Formalization Note.** The entry `α_k` of the page is `α ⟨k − 1, _⟩`; at `k = 0` the function is `α` itself. -/
def setLast {k : ℕ} (α : Fin k → ℝ) (x : ℝ) : Fin k → ℝ := fun j => if j.val + 1 = k then x else α j

end MultiSelectPandora.Supplement


