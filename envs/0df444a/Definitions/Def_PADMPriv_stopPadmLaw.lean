-- Prove2me | Definitions.Def_PADMPriv_stopPadmLaw
-- name    : PADMPriv_stopPadmLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:39.311126+00:00
-- url     : https://prove2.me/theorems/e934a28a-533e-4b4d-a20e-23b1bc57cdf0
-- title:
--   Output law of Stop-PADM-$N_\sigma$ for fixed data
-- statement:
--   For a fixed data set $D$, Stop-PADM-$N_\sigma$ runs private PADM with independent $N(0_m,\sigma^2I_m)$ noise and outputs $\tilde u_{(K)}$, where $K$ is uniform on $\{\lfloor n/2\rfloor+1,\dots,n\}$ and independent of the noise. This is the law of $\tilde u_{(K)}$, i.e. the mechanism whose Rényi differential privacy is studied in Theorems 4.2, 5.2 and 5.4.
--
--   **Formalization Note** The image of the product of the Gaussian noise law and the uniform stopping law under $(z,K)\mapsto\tilde u_{(K)}$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 4.2, p.10

import Mathlib
import Definitions.Def_PADMPriv_padmIter
import Definitions.Def_PADMPriv_gaussNoise
import Definitions.Def_PADMPriv_stopLaw

namespace PADMPriv

open MeasureTheory

/-- The output law of Stop-PADM-N_σ for a fixed data set `D` (Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Section 4.2, p.10): the iterate `ũ₍K₎`, where the noise vectors are independent `N(0_m, σ²I_m)`
and `K` is uniform on `{⌊n/2⌋ + 1, …, n}`, independent of the noise (p.5).

**Formalization Note** The image of `N(0, σ²I_m)^{⊗n} ⊗ Unif(stopWindow n)` under
`(z, K) ↦ ũ₍K₎`. -/
noncomputable def stopPadmLaw {m p l n : ℕ} {R : Type*} (β σ : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin p)) (D : Fin n → R) : Measure (EuclideanSpace ℝ (Fin m)) :=
  ((Measure.pi fun _ : Fin n => gaussNoise m σ).prod (stopLaw n)).map
    (fun ω => padmIter β f g A B c x₀ D ω.1 ω.2)

end PADMPriv


