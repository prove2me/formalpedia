-- Prove2me | Definitions.Def_ZOGlobalLB_Population
-- name    : ZOGlobalLB_Population
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:50:41.267984+00:00
-- url     : https://prove2.me/theorems/3389d78d-83e9-4d4c-bce3-7deb9e1ed034
-- title:
--   The finite antithetic population $f_{j,\pm}$ and its sample moment $S_M$
-- statement:
--   Split $\mathbb R^{r+m}=\mathbb R^r\times\mathbb R^m$ (first $r$ coordinates $Z$, last $m$ coordinates $X$). Given frames $U,V$, independent noise fields $N_1,\dots,N_M$ and the scales $b,\lambda$, the $2M$ sample functions are
--   $$f_{j,\pm}(Z,X)=\lambda\bigl[F_{\mathrm{new}}(Z/b,X/b)\pm N_j(U^\top y(Z/b),X/b)\bigr],$$
--   placed on the $2M$ public labels by a permutation that hides the pairing. Their empirical moment is $S_M=(2M)^{-1}\sum_{j,\pm}\mathrm{Lip}(f_{j,\pm})^2$.
--
--   Antithetic pairs make the population mean exactly $\lambda F_{\mathrm{new}}(\cdot/b)$ for every realization of the noise.
--
--   **Formalization Note.** Labels are $\{1,\dots,2M\}$; the permutation group of a finite set carries the discrete σ-algebra.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, (39), p.21; (128), p.66; (129), p.67

import Mathlib
import Definitions.Def_ZOGlobalLB_lipConst
import Definitions.Def_ZOGlobalLB_NoiseField
import Definitions.Def_ZOGlobalLB_Params

open MeasureTheory
open scoped ENNReal

namespace ZOGlobalLB

/-! # Physical scales and the finite antithetic population

Xia, Yuan, arXiv:2610.19652, Section 3.3, (39), p.21; (46), p.26; Lemma E.1, p.66, (126),
(128), (129).

**Formalization Note.**
* The physical space `ℝᵈ` with `d = r + m` is split into chain coordinates `Z ∈ ℝʳ` and workspace
  coordinates `X ∈ ℝᵐ` by the linear isometry `splitIso` (first `r` coordinates, last `m`).
* The `2M` public labels are `Fin (M + M)`. A permutation `π` of them hides the pairing: label
  `ℓ` carries sample `f_{j,+}` if `π ℓ` is the `j`-th of the first `M` slots and `f_{j,-}` if it
  is the `j`-th of the last `M` slots.
* All tensors of the `M` base labels form one array `G : Fin M × (Fin T × Idx m) → ℝ`; base label
  `j` uses `G (j, ·)`. -/

/-- The isometry `ℝ^{r+m} ≅ ℝʳ × ℝᵐ` (Euclidean norms) splitting off the first `r`
coordinates. -/
noncomputable def splitIso (r m : ℕ) : E (r + m) ≃ₗᵢ[ℝ] WithLp 2 (E r × E m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))

/-- **The finite antithetic population** (128), p.66:
`f_{j,±}(Z, X) = λ[F_new(Z/b, X/b) ± N_j(Uᵀ y(Z/b), X/b)]`, placed on the `2M` public labels by
the permutation `π`. -/
noncomputable def population {r m T M : ℕ} (ε H σ : ℝ) (U : Fin T → E r) (V : Fin T → E m)
    (π : Equiv.Perm (Fin (M + M))) (G : Fin M × (Fin T × Idx m) → ℝ) (ℓ : Fin (M + M))
    (X : E (r + m)) : ℝ :=
  match finSumFinEquiv.symm (π ℓ) with
  | Sum.inl j => lamScale ε H * (Fnew U V ((bScale ε H)⁻¹ • splitIso r m X) +
      noiseNZ σ U V (fun k => G (j, k)) ((bScale ε H)⁻¹ • splitIso r m X))
  | Sum.inr j => lamScale ε H * (Fnew U V ((bScale ε H)⁻¹ • splitIso r m X) -
      noiseNZ σ U V (fun k => G (j, k)) ((bScale ε H)⁻¹ • splitIso r m X))

/-- The empirical second moment `S_M = (2M)⁻¹ Σ_{j,±} Lip(f_{j,±})²` (p.26; p.66), in `ℝ≥0∞`. -/
noncomputable def sampleMoment {r m T M : ℕ} (ε H σ : ℝ) (U : Fin T → E r) (V : Fin T → E m)
    (π : Equiv.Perm (Fin (M + M))) (G : Fin M × (Fin T × Idx m) → ℝ) : ℝ≥0∞ :=
  ((M + M : ℕ) : ℝ≥0∞)⁻¹ * ∑ ℓ, lipConst (population ε H σ U V π G ℓ) ^ 2

/-- Permutations of a finite label set carry the discrete σ-algebra (every set is measurable), so
that a uniformly random hidden pairing is a random element. -/
instance permMeasurableSpace (k : ℕ) : MeasurableSpace (Equiv.Perm (Fin k)) := ⊤

instance (k : ℕ) : DiscreteMeasurableSpace (Equiv.Perm (Fin k)) := ⟨fun _ => trivial⟩

end ZOGlobalLB


