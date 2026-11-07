-- Prove2me | Definitions.Def_ReplicableOL_comparatorEdge
-- name    : ReplicableOL_comparatorEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:20.085319+00:00
-- url     : https://prove2.me/theorems/9ca96f67-b469-4b5e-b110-a3537f094e01
-- title:
--   The comparator's edge $X$ on a loss sequence
-- statement:
--   With $\varepsilon_t=B_t-\tfrac12-\mu_j$ for $t\in E_j$, $Z_j=\sum_{t\in E_j}\varepsilon_t$ and $x_j=L\mu_j+Z_j$, the **comparator's edge** is $X=\sum_{j\le k}x_j$. On the first $kL$ rounds expert 1 has total loss $kL/2+X$ and expert 2 has $kL/2-X$, so the best fixed expert has loss $kL/2-|X|$.
--
--   **Formalization Note** `B_t` is read as the loss `S t 0` of Lean's expert `0`. Epoch `j` is the set of rounds `t` with `t / L = j`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib

namespace ReplicableOL

/-- **The comparator's edge $X$ on a loss sequence.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `X := Σ_{j≤k} x_j`, with `x_j := Lμ_j + Z_j`, `Z_j := Σ_{t∈E_j} ε_t` and `ε_t := B_t − 1/2 − μ_j`.

**Formalization Note.** `B_t` is read as the loss `S t 0` of Lean's expert `0`. Epoch `j` is the set of rounds `t` with `t / L = j`. -/
noncomputable def comparatorEdge {T : ℕ} (k L : ℕ) (θ : Fin k → ℝ) (S : Fin T → Fin 2 → ℝ) : ℝ :=
  ∑ j : Fin k, ((L : ℝ) * θ j +
    ∑ t ∈ Finset.univ.filter (fun t : Fin T => t.val / L = j.val), (S t 0 - 1 / 2 - θ j))

end ReplicableOL


