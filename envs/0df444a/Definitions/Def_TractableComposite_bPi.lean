-- Prove2me | Definitions.Def_TractableComposite_bPi
-- name    : TractableComposite_bPi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:52:15.381407+00:00
-- url     : https://prove2.me/theorems/e7fad8df-ac40-4eba-bc73-d951b3b89d15
-- title:
--   The constant $b^\pi$ of (15)
-- statement:
--   $$b^\pi=\phi(\mathcal V_{\cdot n}(\pi,0))-\langle\alpha^\pi,\mathcal V(\pi,0)\rangle,$$
--
--   where $\mathcal V(\pi,0)=(v_{10},\dots,v_{d0})$ and $\mathcal V_{\cdot n}(\pi,0)=(a_{10},\dots,a_{d0})$. The paper also writes $\beta^\pi$ for this constant.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (15), p.11

import Mathlib
import Definitions.Def_TractableComposite_ip
import Definitions.Def_TractableComposite_vtx
import Definitions.Def_TractableComposite_stairVtx
import Definitions.Def_TractableComposite_alphaPi

namespace TractableComposite

/-- **The constant b^π**, (15), p.11: `b^π = φ(𝒱·ₙ(π,0)) − ⟨α^π, 𝒱(π,0)⟩`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (15), p.11.

**Formalization Note.** `𝒱(π,0) = stairVtx (vtx a) π 0` is the vertex `(v₁₀, …, v_d0)`; its last
column is `(a₁₀, …, a_d0)`. The preamble of (15) writes `β^π` for the same constant. -/
noncomputable def bPi {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (φ : (Fin d → ℝ) → ℝ) (π : Fin (d * n) → Fin d) : ℝ :=
  φ (fun i => a i 0) - ip (alphaPi a φ π) (stairVtx (vtx a) π 0)

end TractableComposite


