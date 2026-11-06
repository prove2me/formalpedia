-- Prove2me | Definitions.Def_MemQueryFeas_game1Win
-- name    : MemQueryFeas_game1Win
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:44.390247+00:00
-- url     : https://prove2.me/theorems/d8b90b52-ef8e-4fb2-a26d-85300517f4cd
-- title:
--   Winning condition of Game 1
-- statement:
--   Given versions $E^{(0)},E^{(1)},\dots$, an index $i$, parameters $\beta,\gamma,\eta$ and decoder output $x_1,\dots,x_k$, let $\tilde E^{(i)}=T_{E^{(i-1)},\eta}(E^{(i)})$. The compression is **successful** if every $x_t$ is nonzero and for all $t\in[k]$
--   1. $\|P_{\tilde E^{(i)}}x_t\|\le\beta\|x_t\|$;
--   2. $\|P_{\mathrm{Span}(x_1,\dots,x_{t-1})^\perp}x_t\|\ge\gamma\|x_t\|$.
--
--   **Formalization Note** An output containing a zero vector loses (the decoder must return nonzero vectors).
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Game 1, lines 3–4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MemQueryFeas_imageProj
import Definitions.Def_MemQueryFeas_stretch

namespace MemQueryFeas

/-- **Winning condition of Game 1.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Game 1, lines 3–4, p.12 (PDF p.13): "Decoder: … return
nonzero vectors `x_1, …, x_k`"; "Letting `Ẽ^(i) := T_{E^(i−1),η}(E^(i))`, the compression is
successful if for all `t ∈ [k]`: 1. `‖Proj_{Ẽ^(i)}(x_t)‖ ≤ β‖x_t‖`; 2.
`‖Proj_{Span(x_1,…,x_{t−1})^⊥}(x_t)‖ ≥ γ‖x_t‖`."

`game1Win β γ η i c x`: for the realized versions `c 0, c 1, …` (projections) and decoder output
`x : Fin k → ℝ^d`, every `x t` is nonzero and satisfies conditions 1 and 2, with
`Ẽ^(i) = T_{c(i−1), η}(c i)`.

**Formalization Note.** Vectors are indexed `0, …, k − 1`; "`x_1, …, x_{t−1}`" are the `x s` with
`s < t`. The requirement that the output be nonzero is part of the winning event (an output with a
zero vector loses). -/
noncomputable def game1Win {d k : ℕ} (β γ η : ℝ) (i : ℕ) (c : ℕ → Op d) (x : Fin k → Vec d) :
    Prop :=
  ∀ t : Fin k, x t ≠ 0 ∧
    ‖imageProj (stretch (c (i - 1)) η) (c i) (x t)‖ ≤ β * ‖x t‖ ∧
    γ * ‖x t‖ ≤ ‖projOnto (Submodule.span ℝ (x '' {s | s < t}))ᗮ (x t)‖

end MemQueryFeas


