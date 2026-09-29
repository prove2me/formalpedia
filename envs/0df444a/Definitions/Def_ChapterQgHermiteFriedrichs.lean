-- Prove2me | Definitions.Def_ChapterQgHermiteFriedrichs
-- name    : ChapterQgHermiteFriedrichs
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-12T08:13:25.990385+00:00
-- url     : https://prove2.me/theorems/878580a1-5af6-4b5f-8c75-60b5c0cc8775
-- title:
--   The quantum-gravity one-particle Hamiltonian on the Hermite core: symmetry, semiboundedness, and the Friedrichs extension
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgHermiteFriedrichs`, source chapter `BookProof/ChapterQgHermiteFriedrichs.lean`): The quantum-gravity one-particle Hamiltonian on the Hermite core: symmetry, semiboundedness, and the Friedrichs extension
--
--   `CONSOLIDATED_PLAN.md` §10.6.1 asks for the one-particle gauge-fixed `R + αR²` Hamiltonian `H = −Δ + W` to be realized as a genuine operator on the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)` — the basis the SIRK numerics work in — and for a self-adjoint realization of it. Target 1 (well-definedness: `H` maps the core into `L²`) is `BookProof.ChapterQgHermiteCore`. This module takes the next step:
--
--   * the kinetic term is realized **algebraically** on the core. Differentiating `pgFun p = p(x) e^{−‖x‖²/4}` in the coordinate `j` multiplies the polynomial by the *twisted derivative* `coreD j p = ∂ⱼ p − ½ xⱼ p` (`hasDerivAt_pgFun_coord`), so the Laplacian acts on the core as the polynomial map `kinPoly p = −∑ⱼ coreD j (coreD j p)` (`pgFun_kinPoly`); * `coreD j` is **antisymmetric** for the Gaussian pairing (`gaussInt_coreD`), which is the polynomial form of integration by parts — the analytic input is the project's `gaussInt_pderiv`; * consequently `H = −Δ + W` on the core (`hamCore`) is **symmetric** (`hamCore_symmetricOn`) and **bounded below by the lower bound of the potential** (`hamCore_quadForm_ge`, `hamCore_quadForm_nonneg`): the kinetic quadratic form is the sum of the squared norms of the first derivatives; * since the core is dense (`polyGaussCore_dense`), the Friedrichs machinery of `BookProof.ChapterFriedrichsExtension` yields a **semibounded self-adjoint extension** with the same lower bound (`hermiteCore_friedrichs_extension`), and a *positive* one when the potential is nonnegative (`hermiteCore_friedrichs_extension_of_nonneg`).
--
--   The named instances are the ones §10.6.1 asks for: the one-variable **scalaron** Hamiltonian `−Δ + V(φ)` (`qgOneParticleHermite_friedrichs`) — unconditional, no finite-speed hypothesis, and with the exponentially growing potential the temperate-growth theorems cannot reach — and the reduced two-variable sector `(R_c, φ)` with the conformal-mode parabola (`qgOneParticleSector_friedrichs`).
--
--   **Honest boundary.** This is the *existence and canonical choice* of a self-adjoint realization, not the *uniqueness* of one: essential self-adjointness on the core (§10.6.1 target 4) is not proved here, and no statement of this module asserts it. It is proved elsewhere for the two cases now available — the harmonic potential (`BookProof.ChapterQgHermiteOscillatorEsa`) and the potential term alone, exponential growth included (`BookProof.ChapterScalaronHermiteEsa`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

import Mathlib
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterStarobinskyPotential
-- `potLp` is only well defined because of `memLp_mul_pgFun_of_expBounded`, which
-- no Definitions bundle declares.  It is published as a platform theorem node
-- (BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded), so import that
-- module instead of restating the proof here.
import Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_pgFun_of_expBounded

/-!
# The quantum-gravity one-particle Hamiltonian on the Hermite core: symmetry,
semiboundedness, and the Friedrichs extension

`CONSOLIDATED_PLAN.md` §10.6.1 asks for the one-particle gauge-fixed `R + αR²`
Hamiltonian `H = −Δ + W` to be realized as a genuine operator on the
Gauss–polynomial (Hermite) core of `L²(ℝᵈ)` — the basis the SIRK numerics work
in — and for a self-adjoint realization of it.  Target 1 (well-definedness:
`H` maps the core into `L²`) is `BookProof.ChapterQgHermiteCore`.  This module
takes the next step:

* the kinetic term is realized **algebraically** on the core.  Differentiating
  `pgFun p = p(x) e^{−‖x‖²/4}` in the coordinate `j` multiplies the polynomial by
  the *twisted derivative* `coreD j p = ∂ⱼ p − ½ xⱼ p` (`hasDerivAt_pgFun_coord`),
  so the Laplacian acts on the core as the polynomial map
  `kinPoly p = −∑ⱼ coreD j (coreD j p)` (`pgFun_kinPoly`);
* `coreD j` is **antisymmetric** for the Gaussian pairing (`gaussInt_coreD`),
  which is the polynomial form of integration by parts — the analytic input is
  the project's `gaussInt_pderiv`;
* consequently `H = −Δ + W` on the core (`hamCore`) is **symmetric**
  (`hamCore_symmetricOn`) and **bounded below by the lower bound of the
  potential** (`hamCore_quadForm_ge`, `hamCore_quadForm_nonneg`): the kinetic
  quadratic form is the sum of the squared norms of the first derivatives;
* since the core is dense (`polyGaussCore_dense`), the Friedrichs machinery of
  `BookProof.ChapterFriedrichsExtension` yields a **semibounded self-adjoint
  extension** with the same lower bound (`hermiteCore_friedrichs_extension`),
  and a *positive* one when the potential is nonnegative
  (`hermiteCore_friedrichs_extension_of_nonneg`).

The named instances are the ones §10.6.1 asks for: the one-variable **scalaron**
Hamiltonian `−Δ + V(φ)` (`qgOneParticleHermite_friedrichs`) — unconditional, no
finite-speed hypothesis, and with the exponentially growing potential the
temperate-growth theorems cannot reach — and the reduced two-variable sector
`(R_c, φ)` with the conformal-mode parabola
(`qgOneParticleSector_friedrichs`).

**Honest boundary.**  This is the *existence and canonical choice* of a
self-adjoint realization, not the *uniqueness* of one: essential
self-adjointness on the core (§10.6.1 target 4) is not proved here, and no
statement of this module asserts it.  It is proved elsewhere for the two cases
now available — the harmonic potential (`BookProof.ChapterQgHermiteOscillatorEsa`)
and the potential term alone, exponential growth included
(`BookProof.ChapterScalaronHermiteEsa`).
-/

namespace BookProof.QgHermiteFriedrichs

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky

noncomputable section

variable {d : ℕ}

/-! ## The conjugate polynomial -/

/-- The polynomial with conjugated coefficients; on *real* points it computes the
complex conjugate of the value (`conj_pgFun`). -/
def cpoly (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  p.map (starRingEnd ℂ)















/-! ## The twisted derivative: the Laplacian on the core, algebraically -/

/-- The **twisted derivative** `coreD j p = ∂ⱼ p − ½ xⱼ p`: differentiating
`p(x) e^{−‖x‖²/4}` in the coordinate `j` replaces `p` by `coreD j p`. -/
def coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  pderiv j p - C (1 / 2 : ℂ) * (X j * p)

theorem coreD_add (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    coreD j (p + q) = coreD j p + coreD j q := by
  simp only [coreD, map_add, mul_add]
  ring

theorem coreD_smul (j : Fin d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (c • p) = c • coreD j p := by
  simp only [coreD, smul_eq_C_mul, pderiv_C_mul, mul_sub]
  ring









/-- The polynomial realization of `−Δ` on the Gauss–polynomial core. -/
def kinPoly (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  -∑ j : Fin d, coreD j (coreD j p)

theorem kinPoly_add (p q : MvPolynomial (Fin d) ℂ) :
    kinPoly (p + q) = kinPoly p + kinPoly q := by
  simp only [kinPoly, coreD_add, Finset.sum_add_distrib, neg_add]

theorem kinPoly_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    kinPoly (c • p) = c • kinPoly p := by
  simp only [kinPoly, coreD_smul, ← Finset.smul_sum, smul_neg]

/-! ## The Gaussian pairing -/

















/-! ## The potential term -/

variable (W : Vd d → ℝ)

/-- Multiplication of a core vector by the potential, as an element of `L²`
(well defined by `BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded`). -/
def potLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) : L2d d :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).toLp _



theorem potLp_add (hWc : Continuous W) (hWb : ExpBounded W) (p q : MvPolynomial (Fin d) ℂ) :
    potLp W hWc hWb (p + q) = potLp W hWc hWb p + potLp W hWc hWb q := by
  simp only [potLp]
  rw [← MemLp.toLp_add (memLp_mul_pgFun_of_expBounded hWc hWb p)
    (memLp_mul_pgFun_of_expBounded hWc hWb q)]
  congr 1
  funext x
  simp [pgFun_add, mul_add]

theorem potLp_smul (hWc : Continuous W) (hWb : ExpBounded W) (c : ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    potLp W hWc hWb (c • p) = c • potLp W hWc hWb p := by
  simp only [potLp]
  rw [← MemLp.toLp_const_smul c (memLp_mul_pgFun_of_expBounded hWc hWb p)]
  congr 1
  funext x
  simp [pgFun_smul, smul_eq_mul]
  ring

/-! ## The Hamiltonian on the core -/

/-- `H p = −Δ(p e^{−‖x‖²/4}) + W · (p e^{−‖x‖²/4})`, as an element of `L²(ℝᵈ)`. -/
def hamPoly (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) : L2d d :=
  pgLp (kinPoly p) + potLp W hWc hWb p

/-- The Hamiltonian as a linear map out of the polynomials. -/
def hamPolyMap (hWc : Continuous W) (hWb : ExpBounded W) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := hamPoly W hWc hWb
  map_add' p q := by
    simp only [hamPoly, kinPoly_add, potLp_add]
    rw [← pgMap_apply, map_add]
    simp only [pgMap_apply]
    abel
  map_smul' c p := by
    simp only [hamPoly, kinPoly_smul, potLp_smul, RingHom.id_apply]
    rw [← pgMap_apply, map_smul]
    simp only [pgMap_apply]
    rw [smul_add]

/-- The core, as the isomorphic image of the polynomial ring. -/
def coreEquiv : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] (polyGaussCore (d := d)) :=
  LinearEquiv.ofInjective (pgMap (d := d)) pgMap_injective





/-- **The one-particle Hamiltonian `−Δ + W` on the Gauss–polynomial (Hermite)
core** of `L²(ℝᵈ)`. -/
def hamCore (hWc : Continuous W) (hWb : ExpBounded W) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (hamPolyMap W hWc hWb).comp (coreEquiv (d := d)).symm.toLinearMap



/-! ## Symmetry -/













/-! ## Semiboundedness -/











/-! ## The Friedrichs extension -/





/-! ## The scalaron instances -/

/-- The one-variable scalaron potential as a function on `ℝ¹`. -/
def scalaronW (M alpha : ℝ) (x : Vd 1) : ℝ := starobinskyV M alpha (x 0)











/-! ## The kinetic term really is the Laplacian -/

/-- Moving along the `j`-th coordinate line through `x`. -/
def coordLine (x : Vd d) (j : Fin d) (s : ℝ) : Vd d :=
  WithLp.toLp 2 (Function.update x.ofLp j s)













end

end BookProof.QgHermiteFriedrichs


