-- Prove2me | Definitions.Def_AutoQMem_Lindblad_sectorGen
-- name    : AutoQMem_Lindblad_sectorGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:53.622926+00:00
-- url     : https://prove2.me/theorems/6efcae98-6c55-46b8-98e7-836c0b8cdd0e
-- title:
--   Backward generator of a sector process
-- statement:
--   For a parity-check matrix $H$ and rates $r_i(s)$ (flip bit $i$ at syndrome $s$), the backward generator acts on functions $h:\mathbb F_2^n\to\mathbb R$ by
--   $$(Gh)(e)=\sum_{i=1}^nr_i(He)\bigl(h(e\oplus\hat e_i)-h(e)\bigr).$$
--
--   **Formalization Note** $G$ is the real matrix with $G_{e,e'}=\sum_ir_i(He)\bigl([e'=e\oplus\hat e_i]-[e'=e]\bigr)$, so $(Gh)(e)=\sum_{e'}G_{e,e'}h(e')$. One definition serves both sectors.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.30, eqs. (48)–(49), p. 23 (PDF p. 25)

import Mathlib
open Matrix

namespace AutoQMem.Lindblad

/-- **Backward generator of a sector process.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.30, eq. (48), p. 23 (PDF 25):
`(G_X(t) h_X)(e) := Σ_{i=1}^n r^{(X)}_i(H_X e, t) (h_X(e ⊕ ê_i) − h_X(e))`.

**Formalization Note.** Written as the real matrix `G` with `(G h)(e) = Σ_{e′} G e e′ h(e′)`:
`G e e′ = Σ_i r_i(H e) ([e′ = e + ê_i] − [e′ = e])`. One definition serves both sectors
(`H = H_X` or `H_Z`); `r i s` is the rate of flipping bit `i` at syndrome `s`. -/
def sectorGen {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (r : Fin n → (Fin m → ZMod 2) → ℝ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  Matrix.of fun e e' => ∑ i, r i (H *ᵥ e) *
    ((if e' = e + Pi.single i 1 then 1 else 0) - (if e' = e then 1 else 0))

end AutoQMem.Lindblad


