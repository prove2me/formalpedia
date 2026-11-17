-- Prove2me | Definitions.Def_PADMPriv_Supplement_stopPadmLawLap
-- name    : PADMPriv_Supplement_stopPadmLawLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:37.583211+00:00
-- url     : https://prove2.me/theorems/c97ba82c-dbbc-4746-9891-cf13d7dce6d4
-- title:
--   Output law of Stop-PADM-$L_\lambda$
-- statement:
--   Stop-PADM-$L_\lambda$ runs private PADM with independent $L_m(0_m,\lambda)$ noise vectors $z_{(1)},\dots,z_{(n)}$, draws an index $K$ uniformly from the stopping window $\{\lfloor n/2\rfloor+1,\dots,n\}$, independently of the noise, and outputs $\tilde u_{(K)}$. For a fixed data set $D$, this definition is the law of the output $\tilde u_{(K)}$. It is the mechanism of Theorem 4.4.
--
--   **Formalization Note** The image of $L_m(0_m,\lambda)^{\otimes n}\otimes\mathrm{Unif}\{\lfloor n/2\rfloor+1,\dots,n\}$ (the published `PADMPriv.stopLaw`) under $(z,K)\mapsto\tilde u_{(K)}$, with the published iterate map `PADMPriv.padmIter`. It is the Laplace analogue of the published Gaussian `PADMPriv.stopPadmLaw`.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 4.3, p.10 (stopping window as for Stop-PADM-N_σ, Section 4.2, p.10)

import Mathlib
import Definitions.Def_PADMPriv_padmIter
import Definitions.Def_PADMPriv_stopLaw
import Definitions.Def_PADMPriv_Supplement_lapNoise

namespace PADMPriv.Supplement

open MeasureTheory

/-- The output law of Stop-PADM-L_λ for a fixed data set `D` (Li–Lai–Weng, *Exact Feasibility and
Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript
(sha256 d58edbe0…0f3d), Section 4.3, p.10): the iterate `ũ₍K₎`, where the noise vectors are
independent `L_m(0_m, λ)` and `K` is uniform on `{⌊n/2⌋ + 1, …, n}`, independent of the noise
(as for Stop-PADM-N_σ, p.10). The Laplace analogue of the published `PADMPriv.stopPadmLaw`.

**Formalization Note** The image of `L_m(0_m, λ)^{⊗n} ⊗ Unif(stopWindow n)` (the published
`PADMPriv.stopLaw`) under `(z, K) ↦ ũ₍K₎`. The scale is named `s`. -/
noncomputable def stopPadmLawLap {m p l n : ℕ} {R : Type*} (β s : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin p)) (D : Fin n → R) : Measure (EuclideanSpace ℝ (Fin m)) :=
  ((Measure.pi fun _ : Fin n => lapNoise m s).prod (stopLaw n)).map
    (fun ω => padmIter β f g A B c x₀ D ω.1 ω.2)

end PADMPriv.Supplement


