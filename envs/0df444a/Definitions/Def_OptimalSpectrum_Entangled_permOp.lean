-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_permOp
-- name    : OptimalSpectrum_Entangled_permOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:10.882625+00:00
-- url     : https://prove2.me/theorems/887ade28-9cad-4cab-8825-2a1de0daa12e
-- title:
--   Permutation operator $R_\pi$ on $r$ tensor factors
-- statement:
--   For a permutation $\pi\in S_r$, the operator $R_\pi$ on $(\mathbb C^\iota)^{\otimes r}$ permutes the tensor factors:
--
--   $$R_\pi\big(|v_1\rangle\otimes\cdots\otimes|v_r\rangle\big)=|v_{\pi^{-1}(1)}\rangle\otimes\cdots\otimes|v_{\pi^{-1}(r)}\rangle .$$
--
--   These operators enter the moment observables $M_m$ (through cycles) and express permutation invariance in Lemma 7.6.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.2, p. 21 (PDF p. 23)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Permutation operator `R_π` on `r` tensor factors.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.2, printed p. 21 (PDF p. 23): "For π ∈ S_r, define the permutation operator R_π on r
tensor factors by R_π(|v₁⟩ ⊗ ⋯ ⊗ |v_r⟩) = |v_π⁻¹(1)⟩ ⊗ ⋯ ⊗ |v_π⁻¹(r)⟩".

On `(ℂ^ι)^{⊗r}` with basis `|v⟩ = |v₁⟩ ⊗ ⋯ ⊗ |v_r⟩`, `v : Fin r → ι`, the operator maps `|v⟩` to
`|v ∘ π⁻¹⟩`; as a matrix, the `(x, y)` entry is `1` if `x = y ∘ π⁻¹` and `0` otherwise.

**Formalization Note.** Factors are indexed by `Fin r` (`0`-based). The orientation `π⁻¹` is the
page's. -/
def permOp {ι : Type*} [DecidableEq ι] {r : ℕ} (π : Equiv.Perm (Fin r)) :
    Matrix (Fin r → ι) (Fin r → ι) ℂ :=
  Matrix.of fun x y => if x = y ∘ ⇑π.symm then 1 else 0

end OptimalSpectrum.Entangled


