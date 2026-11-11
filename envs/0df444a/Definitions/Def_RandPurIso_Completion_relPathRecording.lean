-- Prove2me | Definitions.Def_RandPurIso_Completion_relPathRecording
-- name    : RandPurIso_Completion_relPathRecording
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:59.340641+00:00
-- url     : https://prove2.me/theorems/d2a031a2-7a3c-4476-8b3b-358dafba63d9
-- title:
--   Relabeled exact recorder $\widetilde{PR}$
-- statement:
--   For $x,y\in M_1$, the append map with relabeled outputs is
--   $$\widetilde{\mathrm{App}}^{(t)}_{x,y}\big(|\vec x\rangle\otimes\overline{|\vec y\rangle}\big)=|\vec x,x\rangle\otimes\big(\overline{|\vec y\rangle}\otimes\overline{D^V|y\rangle}\big).$$
--   With $\widetilde\Lambda_t,\widetilde\Lambda^+_t$ the reweightings of Definition 3.13 in dimension $M-N$ (those of $PR_{M_1,T}$), the **relabeled exact recorder** is, on recording length $t<T$,
--   $$\widetilde{PR}=\sum_{x,y\in M_1}D^V|y\rangle\langle x|\otimes\widetilde\Lambda_{t+1}\Omega_{t+1}\widetilde{\mathrm{App}}^{(t)}_{x,y}\widetilde\Lambda_t^+\Omega_t .$$
--   It intuitively simulates a random unitary $\mathcal H(M_1)\to\mathrm{Im}(D^V\Pi_{M_1})$.
--
--   **Formalization Note** $\widetilde\Lambda_t$ acts on $\mathcal H(M_1)^{\otimes t}$ ($M_1\cong[M-N]$ by $x\mapsto x-N$) and is extended by zero to input words with a letter outside $M_1$; the paper applies $\widetilde{PR}$ only to inputs in $M_1$ with recordings in $\Gamma_t$. Like $PR$, $\widetilde{PR}$ is zero on recording length $T$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §5.1, p. 30

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
import Definitions.Def_RandPurIso_Completion_legalProj
import Definitions.Def_RandPurIso_Completion_lam
open Matrix

namespace RandPurIso.Completion

/-- **Append map with relabeled outputs** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §5.1, p. 30): for `x, y ∈ M1`,
`~App^{(t)}_{x,y} (|x⃗⟩ ⊗ conj|y⃗⟩) = |x⃗, x⟩ ⊗ (conj|y⃗⟩ ⊗ conj(D^V|y⟩))`, on the path register of
`H([M])`. The appended output slot carries the entries `conj((D^V)_{z y})`. -/
def relAppend {M : ℕ} (D : Matrix.unitaryGroup (Fin M) ℂ) (t : ℕ) (x y : Fin M) :
    Matrix (Rt M (t + 1)) (Rt M t) ℂ :=
  fun r' r => if r'.1 = Fin.snoc (α := fun _ => Fin M) r.1 x ∧ Fin.init r'.2 = r.2 then
      starRingEnd ℂ ((D : Matrix (Fin M) (Fin M) ℂ) (r'.2 (Fin.last t)) y) else 0

/-- An operator on `H(M1)^{⊗t}` (with `M1 ≅ [M − N]`, `x ↦ x − N`) extended by zero to
`H([M])^{⊗t}`. -/
def extendM1 {N M t : ℕ} (P : Matrix (Fin t → Fin (M - N)) (Fin t → Fin (M - N)) ℂ) :
    Matrix (Fin t → Fin M) (Fin t → Fin M) ℂ :=
  fun xs' xs =>
    if h : (∀ i, N ≤ (xs' i).val) ∧ (∀ i, N ≤ (xs i).val) then
      P (fun i => ⟨(xs' i).val - N, by have := (xs' i).isLt; have := h.1 i; omega⟩)
        (fun i => ⟨(xs i).val - N, by have := (xs i).isLt; have := h.2 i; omega⟩)
    else 0

/-- `~Λ_t`: the reweighting of Definition 3.13 in dimension `M − N` ("the reweighting operators
used by `PR_{M1,T}`", p. 30) on the input slots, identity on the output slots. -/
noncomputable def relLam (N M t : ℕ) : Matrix (Rt M t) (Rt M t) ℂ :=
  Matrix.kronecker (extendM1 (N := N) (lamIn (M - N) t)) 1

/-- `~Λ⁺_t`, as `relLam`. -/
noncomputable def relLamPlus (N M t : ℕ) : Matrix (Rt M t) (Rt M t) ℂ :=
  Matrix.kronecker (extendM1 (N := N) (lamPlusIn (M - N) t)) 1

/-- The block `~Λ_{t+1} Ω_{t+1} ~App^{(t)}_{x,y} ~Λ⁺_t Ω_t`. -/
noncomputable def relBlock (N : ℕ) {M : ℕ} (D : Matrix.unitaryGroup (Fin M) ℂ) (t : ℕ) (x y : Fin M) :
    Matrix (Rt M (t + 1)) (Rt M t) ℂ :=
  relLam N M (t + 1) * legalProj M (t + 1) * relAppend D t x y * relLamPlus N M t * legalProj M t

open Classical in
/-- **Relabeled exact recorder `~PR`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §5.1, p. 30): on recording length `t < T`,
`~PR = Σ_{x,y∈M1} D^V|y⟩⟨x| ⊗ ~Λ_{t+1} Ω_{t+1} ~App^{(t)}_{x,y} ~Λ⁺_t Ω_t`, an operator on
`H([M]) ⊗ St`, `St = ⊕_{t≤T} R_t` of `H([M])`; zero on recording length `T`.

**Formalization Note.** `~Λ_t` acts on `H(M1)^{⊗t}`; it is extended by zero to input slots outside
`M1` (the paper applies `~PR` only to inputs in `M1` with recordings whose input slots lie in `M1`).
The zero on recording length `T` is the convention of Definition 3.13 for `PR`. -/
noncomputable def relPathRecording (N : ℕ) {M : ℕ} (T : ℕ) (D : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix (Fin M × PRSt M T) (Fin M × PRSt M T) ℂ :=
  recordOp fun t z x =>
    if N ≤ x.val then
      ∑ y : Fin M, if N ≤ y.val then (D : Matrix (Fin M) (Fin M) ℂ) z y • relBlock N D t x y else 0
    else 0

end RandPurIso.Completion


