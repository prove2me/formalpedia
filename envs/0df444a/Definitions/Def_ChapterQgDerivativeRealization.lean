-- Prove2me | Definitions.Def_ChapterQgDerivativeRealization
-- name    : ChapterQgDerivativeRealization
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T00:08:09.43814+00:00
-- url     : https://prove2.me/theorems/47db885e-9020-48dc-aa15-48bf72710872
-- title:
--   ChapterQgDerivativeRealization
-- statement:
--   ChapterQgDerivativeRealization

import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Theorems.Thm_BookProof_QgPhysicalSectorIdentity_L_gf_constraint_surface
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Theorems.Thm_BookProof_QgPhysicalSectorIdentity_lagrange_term_zero_of_fixing


/-!
# QG-3.2-exec (ii) — the concrete 84-dimensional derivative-variable fixing `E = ∂e`

Plan item **QG-3.2-exec (ii)** of `CONSOLIDATED_PLAN.md`: the gauge-identity
track.  `ChapterQgPhysicalSectorIdentity` formalized the *mechanism* of the
Navier–Stokes derivative-variable fixing abstractly (`gaugeField = v − dφ`,
`lagrange_term_zero_of_fixing`, `L_gf_constraint_surface`,
`int_L_gf_eq_zero_physical`) and left the *concrete* 84-dimensional instance —
"a concrete `gaugeField`, defined `v − dφ` on the actual
`ChapterQuantumGravity3DGauge` coordinate algebra, fed through those theorems
to show the coupling reduces to field values" — as the remaining work.  This
module supplies it.

## The realization

A **field configuration** is a tetrad field whose components are polynomial in
the four spacetime coordinates (`TetradConfig`), together with the `64`
*promoted* derivative fields `E_{μν}^a` (`DerivFields`) that the 84-dimensional
coordinate space of `ChapterQuantumGravity3DGauge` treats as independent
coordinates.  `configPoint T E x : Fin 84 → ℂ` is the point of the coordinate
space such a pair determines at a spacetime point `x`:

* `configPoint_idxX` — the `4` spacetime coordinates are `x^μ`;
* `configPoint_idxE` — the `16` tetrad coordinates are `e_μ^a(x)`;
* `configPoint_idxDE` — the `64` derivative coordinates are `E_{μν}^a(x)`.

`idx_cases` records that these three families exhaust `Fin 84`
(`4 + 16 + 64 = 84`), so a point of the coordinate space is *exactly* this
data.

## The fixing, concretely

`gaugeFieldPoly T E μ ν a = E_{μν}^a − ∂_μ e_ν^a` is the concrete `v − dφ` on
the 84-dimensional coordinate algebra, and `Fixed T E` is its vanishing — the
NS constraint `u_{i,j} = ∂_j u_i` (book.tex §4159–4197) in the tetrad
formalism, `E = ∂e`.  It is realized (`jetDeriv_fixed`: the derivative fields
*are* the derivatives) and it is not automatic (`exists_not_fixed`), and on the
fixing surface the coordinate point is the 1-jet of the tetrad field
(`configPoint_eq_jetPoint_of_fixed`).

## What the fixing buys — the couplings reduce to field values

* `eval_torsionPoly_jetPoint` — on the surface the torsion coordinate
  polynomial `torsionPoly μ ν a = X (idxDE μ ν a) − X (idxDE ν μ a)` of
  `ChapterQuantumGravity3DGauge` evaluates to the *actual* antisymmetrized
  tetrad derivative `∂_μ e_ν^a − ∂_ν e_μ^a`;
* `eval_crossCouplingPoly_jetPoint` — the tetrad-torsion cross coupling
  `½ Σ e_μ^a T_{μν}^a`, the coordinate-algebra shape of the `book.tex 8190`
  cross terms `½S·E + ⅓P·E − e(…)`, evaluates to an explicit expression in the
  tetrad field and its derivatives (`couplingValue`);
* `eval_eq_of_fixed_of_comp_eq` — **the "no new independent modes" statement**:
  on the fixing surface the value of *every* polynomial in the 84 coordinates
  is determined by the tetrad field alone; two configurations with the same
  tetrad field give the same value, whatever their (then equal) derivative
  fields.

## The hookup to the abstract BRST theorems

Section 4 builds a concrete `DerivativeVariableFixingSystem` whose carrier is
`2 × 2` matrices over the algebra of spacetime polynomials, with the *genuine*
exterior derivative `d = ∂_μ` acting entrywise (in the abstract matrix model of
`ChapterGaugeFixing` the exterior derivative is trivial, so `v − dφ` could not
express `E = ∂e`).  Its `φ` is a tetrad component `e_ν^a`, its `v` is the
promoted derivative field `E_{μν}^a`, and

* `qgFixing_gaugeField_eq_zero_iff` — its `gaugeField = v − dφ` vanishes
  **iff** `E_{μν}^a = ∂_μ e_ν^a`, i.e. iff the concrete fixing holds;
* `qgFixing_lagrange_term_zero`, `qgFixing_L_gf_constraint_surface` — the
  abstract theorems of `ChapterQgPhysicalSectorIdentity`, run on this concrete
  system with the hypothesis discharged by `Fixed`;
* `qgFixing_gaugeField_ne_zero_of_not_fixed`, `qgFixing_B_ne_zero` — the system
  is not degenerate: off the surface the constraint is genuinely non-zero, and
  the Nakanishi–Lautrup field is non-zero.

## Honest boundary

* The tetrad fields here are **polynomial** in the spacetime coordinates; this
  is what makes `∂_μ` an honest linear derivation of the coefficient algebra
  (and it is the class the Hermite/mode formalism of the tree uses).  Nothing
  is claimed for general smooth fields.
* In this concrete system the constraint sector is bosonic: `v` is a multiple
  of the identity matrix, so its BRST partner `c` is zero.  That is not a loss:
  on the fixing surface the ghost is BRST-trivial in *any* model (the
  contractible-pair statement `s_gaugeField_eq_c`), and the non-degenerate
  ghost sector is exactly what `BookProof.GaugeFixing.matrixModel` and
  `QgPhysicalSectorIdentity.matrixModel_c_ne_zero` provide.
* This closes the *representability* half of QG-3.2(a) — the derivative
  coordinates are realizable as actual derivatives, and on that surface the
  couplings are functions of the tetrad field.  It does **not** prove that the
  physical (BRST-closed) sector of the quantum theory is confined to that
  surface; that remains the named hypothesis recorded in
  `ChapterQgPhysicalSectorIdentity`, with QG-3.2(b) (direct ESA of the full
  operator) as the fallback.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgDerivativeRealization

open MvPolynomial
open BookProof.GaugeFixing
open BookProof.QuantumGravity3DGauge
open BookProof.QgPhysicalSectorIdentity

/-! ## 1. Polynomial tetrad fields and the 84-dimensional configuration point -/

/-- The coefficient algebra: real polynomial functions of the four spacetime
coordinates.  Polynomiality is what makes `∂_μ` an honest linear derivation. -/
abbrev SpacetimePoly : Type := MvPolynomial (Fin 4) ℝ

/-- A tetrad field: the `16` components `e_ν^a` as polynomial functions of the
spacetime coordinates. -/
structure TetradConfig where
  /-- The component `e_ν^a` of the tetrad, as a polynomial in `x`. -/
  comp : Fin 4 → Fin 4 → SpacetimePoly

/-- The `64` *promoted* derivative fields `E_{μν}^a` — the objects the
84-dimensional coordinate space treats as independent coordinates. -/
abbrev DerivFields : Type := Fin 4 → Fin 4 → Fin 4 → SpacetimePoly

/-- The actual derivative fields of a tetrad configuration, `∂_μ e_ν^a`. -/
noncomputable def jetDeriv (T : TetradConfig) : DerivFields :=
  fun mu nu a => pderiv mu (T.comp nu a)

/-- The point of the 84-dimensional coordinate space determined by a tetrad
configuration `T`, a family of promoted derivative fields `E`, and a spacetime
point `x`.  The three blocks are the `4` spacetime coordinates, the `16` tetrad
coordinates and the `64` derivative coordinates. -/
noncomputable def configPoint (T : TetradConfig) (E : DerivFields) (x : Fin 4 → ℝ) :
    Fin 84 → ℂ := fun j =>
  if h : (j : ℕ) < 4 then ((x ⟨(j : ℕ), h⟩ : ℝ) : ℂ)
  else if _ : (j : ℕ) < 20 then
    ((MvPolynomial.eval x
      (T.comp ⟨((j : ℕ) - 4) / 4, by omega⟩ ⟨((j : ℕ) - 4) % 4, by omega⟩) : ℝ) : ℂ)
  else
    ((MvPolynomial.eval x
      (E ⟨((j : ℕ) - 20) / 16, by omega⟩ ⟨(((j : ℕ) - 20) / 4) % 4, by omega⟩
        ⟨(j : ℕ) % 4, by omega⟩) : ℝ) : ℂ)

/-- The configuration point of the *realized* derivative fields: the 1-jet of
the tetrad field at `x`. -/
noncomputable def jetPoint (T : TetradConfig) (x : Fin 4 → ℝ) : Fin 84 → ℂ :=
  configPoint T (jetDeriv T) x

@[simp] theorem configPoint_idxX (T : TetradConfig) (E : DerivFields) (x : Fin 4 → ℝ)
    (mu : Fin 4) : configPoint T E x (idxX mu) = ((x mu : ℝ) : ℂ) := by
  have hv : ((idxX mu : Fin 84) : ℕ) = mu.val := rfl
  simp only [configPoint, hv, dif_pos mu.isLt]

@[simp] theorem configPoint_idxE (T : TetradConfig) (E : DerivFields) (x : Fin 4 → ℝ)
    (mu a : Fin 4) :
    configPoint T E x (idxE mu a) = ((MvPolynomial.eval x (T.comp mu a) : ℝ) : ℂ) := by
  have hv : ((idxE mu a : Fin 84) : ℕ) = 4 + 4 * mu.val + a.val := rfl
  have hmu := mu.isLt
  have ha := a.isLt
  rw [configPoint, dif_neg (by omega), dif_pos (by omega)]
  congr 3 <;> · apply Fin.ext; simp only [hv]; omega

@[simp] theorem configPoint_idxDE (T : TetradConfig) (E : DerivFields) (x : Fin 4 → ℝ)
    (mu nu a : Fin 4) :
    configPoint T E x (idxDE mu nu a) = ((MvPolynomial.eval x (E mu nu a) : ℝ) : ℂ) := by
  have hv : ((idxDE mu nu a : Fin 84) : ℕ) = 20 + 16 * mu.val + 4 * nu.val + a.val := rfl
  have hmu := mu.isLt
  have hnu := nu.isLt
  have ha := a.isLt
  rw [configPoint, dif_neg (by omega), dif_neg (by omega)]
  congr 3 <;> · apply Fin.ext; simp only [hv]; omega

theorem jetPoint_idxE (T : TetradConfig) (x : Fin 4 → ℝ) (mu a : Fin 4) :
    jetPoint T x (idxE mu a) = ((MvPolynomial.eval x (T.comp mu a) : ℝ) : ℂ) :=
  configPoint_idxE T (jetDeriv T) x mu a

theorem jetPoint_idxDE (T : TetradConfig) (x : Fin 4 → ℝ) (mu nu a : Fin 4) :
    jetPoint T x (idxDE mu nu a)
      = ((MvPolynomial.eval x (pderiv mu (T.comp nu a)) : ℝ) : ℂ) :=
  configPoint_idxDE T (jetDeriv T) x mu nu a

/-- The three index families exhaust the `84` coordinates: `4 + 16 + 64 = 84`.
A point of the coordinate space is exactly a spacetime point, a tetrad value
and a family of derivative values. -/
theorem idx_cases (j : Fin 84) :
    (∃ mu, j = idxX mu) ∨ (∃ mu a, j = idxE mu a) ∨ (∃ mu nu a, j = idxDE mu nu a) := by
  rcases lt_or_ge (j : ℕ) 4 with h | h
  · exact Or.inl ⟨⟨(j : ℕ), h⟩, Fin.ext rfl⟩
  · rcases lt_or_ge (j : ℕ) 20 with h2 | h2
    · exact Or.inr (Or.inl ⟨⟨((j : ℕ) - 4) / 4, by omega⟩, ⟨((j : ℕ) - 4) % 4, by omega⟩,
        Fin.ext (by simp only [idxE]; omega)⟩)
    · have hj := j.isLt
      exact Or.inr (Or.inr ⟨⟨((j : ℕ) - 20) / 16, by omega⟩,
        ⟨(((j : ℕ) - 20) / 4) % 4, by omega⟩, ⟨(j : ℕ) % 4, by omega⟩,
        Fin.ext (by simp only [idxDE]; omega)⟩)

/-! ## 2. The concrete gauge field `v − dφ` and its zero locus -/

/-- **The concrete 84-dimensional gauge field.**  `v − dφ` on the coordinate
algebra of `ChapterQuantumGravity3DGauge`: the promoted derivative field minus
the actual derivative of the tetrad component. -/
noncomputable def gaugeFieldPoly (T : TetradConfig) (E : DerivFields) (mu nu a : Fin 4) :
    SpacetimePoly :=
  E mu nu a - pderiv mu (T.comp nu a)

/-- The fixing surface `E = ∂e`: the NS derivative-variable constraint
(`u_{i,j} = ∂_j u_i`) in the tetrad formalism. -/
def Fixed (T : TetradConfig) (E : DerivFields) : Prop :=
  ∀ mu nu a, gaugeFieldPoly T E mu nu a = 0

/-- The fixing is realized: the actual derivative fields satisfy it, so the
surface is non-empty. -/
theorem jetDeriv_fixed (T : TetradConfig) : Fixed T (jetDeriv T) := by
  intro mu nu a
  simp [gaugeFieldPoly, jetDeriv]

/-- The fixing is equivalent to the derivative fields *being* the derivatives. -/
theorem fixed_iff (T : TetradConfig) (E : DerivFields) :
    Fixed T E ↔ ∀ mu nu a, E mu nu a = pderiv mu (T.comp nu a) := by
  constructor
  · intro h mu nu a
    have := h mu nu a
    rw [gaugeFieldPoly, sub_eq_zero] at this
    exact this
  · intro h mu nu a
    rw [gaugeFieldPoly, h, sub_self]

/-- The fixing is not automatic: for the zero tetrad and the constant
derivative field `1` the gauge field is `1 ≠ 0`. -/
theorem exists_not_fixed : ∃ (T : TetradConfig) (E : DerivFields), ¬ Fixed T E := by
  refine ⟨⟨fun _ _ => 0⟩, fun _ _ _ => 1, ?_⟩
  intro h
  have h0 := (fixed_iff _ _).1 h 0 0 0
  simp only [map_zero] at h0
  exact one_ne_zero h0

/-- On the fixing surface the coordinate point is the 1-jet of the tetrad
field: the `64` derivative coordinates carry no information beyond `e` and its
derivatives. -/
theorem configPoint_eq_jetPoint_of_fixed (T : TetradConfig) (E : DerivFields)
    (hE : Fixed T E) (x : Fin 4 → ℝ) : configPoint T E x = jetPoint T x := by
  funext j
  rcases idx_cases j with ⟨mu, rfl⟩ | ⟨mu, a, rfl⟩ | ⟨mu, nu, a, rfl⟩
  · simp [jetPoint]
  · simp [jetPoint]
  · rw [configPoint_idxDE, jetPoint_idxDE, (fixed_iff T E).1 hE mu nu a]

/-! ## 3. The couplings on the fixing surface reduce to field values -/

/-- On the fixing surface the torsion coordinate polynomial of
`ChapterQuantumGravity3DGauge` evaluates to the actual antisymmetrized tetrad
derivative. -/
theorem eval_torsionPoly_jetPoint (T : TetradConfig) (x : Fin 4 → ℝ) (mu nu a : Fin 4) :
    MvPolynomial.eval (jetPoint T x) (torsionPoly mu nu a)
      = ((MvPolynomial.eval x (pderiv mu (T.comp nu a)) : ℝ) : ℂ)
        - ((MvPolynomial.eval x (pderiv nu (T.comp mu a)) : ℝ) : ℂ) := by
  simp [torsionPoly, jetPoint_idxDE]

/-- The tetrad–torsion cross coupling on the coordinate algebra: the shape of
the `book.tex 8190` cross terms `½S·E + ⅓P·E − e(…)`, a tetrad coordinate
multiplying a derivative (torsion) coordinate. -/
noncomputable def crossCouplingPoly : MvPolynomial (Fin 84) ℂ :=
  ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin 4,
    C (1 / 2 : ℂ) * X (idxE mu a) * torsionPoly mu nu a

/-- The value the cross coupling takes on the fixing surface: an explicit
expression in the tetrad field and its derivatives, with no reference to the
derivative coordinates. -/
noncomputable def couplingValue (T : TetradConfig) (x : Fin 4 → ℝ) : ℂ :=
  ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin 4,
    (1 / 2 : ℂ) * ((MvPolynomial.eval x (T.comp mu a) : ℝ) : ℂ) *
      (((MvPolynomial.eval x (pderiv mu (T.comp nu a)) : ℝ) : ℂ)
        - ((MvPolynomial.eval x (pderiv nu (T.comp mu a)) : ℝ) : ℂ))

/-- **The coupling reduces to field values.**  On the fixing surface the cross
coupling is a function of the tetrad field and its derivatives alone. -/
theorem eval_crossCouplingPoly_jetPoint (T : TetradConfig) (x : Fin 4 → ℝ) :
    MvPolynomial.eval (jetPoint T x) crossCouplingPoly = couplingValue T x := by
  simp only [crossCouplingPoly, couplingValue, map_sum, map_mul, eval_C, eval_X,
    eval_torsionPoly_jetPoint, jetPoint_idxE]

/-- **No new independent modes.**  On the fixing surface the value of *every*
polynomial in the `84` coordinates is determined by the tetrad field: two
configurations with the same tetrad field — whatever derivative fields they
carry, as long as both are fixed — give the same value. -/
theorem eval_eq_of_fixed_of_comp_eq {T T' : TetradConfig} {E E' : DerivFields}
    (hE : Fixed T E) (hE' : Fixed T' E') (hcomp : T.comp = T'.comp) (x : Fin 4 → ℝ)
    (p : MvPolynomial (Fin 84) ℂ) :
    MvPolynomial.eval (configPoint T E x) p = MvPolynomial.eval (configPoint T' E' x) p := by
  have hT : T = T' := by cases T; cases T'; simpa using hcomp
  subst hT
  rw [configPoint_eq_jetPoint_of_fixed T E hE x, configPoint_eq_jetPoint_of_fixed T E' hE' x]

/-- The same statement for the concrete cross coupling. -/
theorem crossCoupling_eq_of_fixed {T T' : TetradConfig} {E E' : DerivFields}
    (hE : Fixed T E) (hE' : Fixed T' E') (hcomp : T.comp = T'.comp) (x : Fin 4 → ℝ) :
    MvPolynomial.eval (configPoint T E x) crossCouplingPoly
      = MvPolynomial.eval (configPoint T' E' x) crossCouplingPoly :=
  eval_eq_of_fixed_of_comp_eq hE hE' hcomp x crossCouplingPoly

/-- The cross coupling is not the zero polynomial: there is a configuration on
the fixing surface where it does not vanish, so the reduction is not vacuous.
The witness is the tetrad `e_0^a = x^1`, `e_ν^a = 0` for `ν ≠ 0`, at the point
`x = (0, 1, 0, 0)`. -/
theorem couplingValue_ne_zero :
    ∃ (T : TetradConfig) (x : Fin 4 → ℝ), couplingValue T x ≠ 0 := by
  classical
  refine ⟨⟨fun nu _ => if nu = 0 then X 1 else 0⟩, fun i => if i = 1 then 1 else 0, ?_⟩
  simp only [couplingValue, Fin.sum_univ_four]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

/-! ## 4. The concrete gauge-fixing system on the field algebra -/

/-- The carrier: `2 × 2` matrices over the algebra of spacetime polynomials. -/
abbrev Mat2R : Type := Matrix (Fin 2) (Fin 2) SpacetimePoly

/-- The nilpotent odd generator `Q = E₁₂`. -/
noncomputable def QmR : Mat2R := !![0, 1; 0, 0]

/-- The anti-ghost `c̄ = E₂₁`. -/
noncomputable def PmR : Mat2R := !![0, 0; 1, 0]

/-- The BRST differential: the super-commutator with `Q`. -/
noncomputable def sMatR (g : ℤ) (x : Mat2R) : Mat2R := QmR * x - ((-1 : ℝ) ^ g) • (x * QmR)

/-- **The exterior derivative**: the spacetime partial derivative `∂_μ`, acting
entrywise.  This is what the abstract matrix model of `ChapterGaugeFixing`
lacks (there `d = 0`), and what makes `v − dφ` express `E = ∂e`. -/
noncomputable def dMatR (mu : Fin 4) (x : Mat2R) : Mat2R := x.map (fun p => pderiv mu p)

theorem QmR_mul_QmR : QmR * QmR = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QmR, Matrix.mul_apply, Fin.sum_univ_two]

theorem QmR_PmR_add : QmR * PmR + PmR * QmR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QmR, PmR]

theorem sMatR_nilpotent (g : ℤ) (x : Mat2R) : sMatR (g + 1) (sMatR g x) = 0 := by
  have hsgn : ((-1 : ℝ) ^ (g + 1)) = -((-1 : ℝ) ^ g) := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]; ring
  simp only [sMatR, hsgn, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    neg_smul, ← mul_assoc, QmR_mul_QmR, Matrix.zero_mul]
  rw [mul_assoc x QmR QmR, QmR_mul_QmR, Matrix.mul_zero]
  simp

theorem sMatR_sub (g : ℤ) (x y : Mat2R) : sMatR g (x - y) = sMatR g x - sMatR g y := by
  simp only [sMatR, mul_sub, sub_mul, smul_sub]; abel

theorem dMatR_zero (mu : Fin 4) : dMatR mu 0 = 0 := by
  ext i j; simp [dMatR]

theorem sMatR_dMatR (mu : Fin 4) (g : ℤ) (x : Mat2R) :
    sMatR g (dMatR mu x) = dMatR mu (sMatR g x) := by
  ext i j
  simp only [sMatR, dMatR, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.mul_apply, Fin.sum_univ_two, map_sub]
  fin_cases i <;> fin_cases j <;> simp [QmR]

theorem sMatR_smul_one (f : SpacetimePoly) : sMatR 0 (f • (1 : Mat2R)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMatR, QmR]

theorem dMatR_smul_one (mu : Fin 4) (f : SpacetimePoly) :
    dMatR mu (f • (1 : Mat2R)) = (pderiv mu f) • (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMatR, Matrix.smul_apply]

theorem smul_one_eq_zero_iff (f : SpacetimePoly) : f • (1 : Mat2R) = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simpa [Matrix.smul_apply, Matrix.one_apply] using h00
  · rintro rfl; simp

theorem sMatR_PmR : sMatR (-1) PmR = 1 := by
  have hneg : ((-1 : ℝ) ^ (-1 : ℤ)) = -1 := by norm_num
  rw [sMatR, hneg]
  simp only [neg_smul, one_smul, sub_neg_eq_add]
  exact QmR_PmR_add

theorem sMatR_leibniz (Y : Mat2R) : sMatR (-1) (PmR * Y) = 1 * Y - PmR * sMatR 0 Y := by
  have hneg : ((-1 : ℝ) ^ (-1 : ℤ)) = -1 := by norm_num
  have h0 : ((-1 : ℝ) ^ (0 : ℤ)) = 1 := by norm_num
  have h3 : QmR * PmR * Y + PmR * QmR * Y = Y := by rw [← add_mul, QmR_PmR_add, one_mul]
  simp only [sMatR, hneg, h0, one_smul, neg_smul, sub_neg_eq_add]
  calc QmR * (PmR * Y) + PmR * Y * QmR
      = (QmR * PmR * Y + PmR * QmR * Y) - PmR * QmR * Y + PmR * Y * QmR := by
        rw [mul_assoc QmR PmR Y]; abel
    _ = Y - PmR * QmR * Y + PmR * Y * QmR := by rw [h3]
    _ = 1 * Y - PmR * (QmR * Y - Y * QmR) := by
        rw [one_mul, mul_sub, ← mul_assoc, ← mul_assoc]; abel

/-- **The concrete derivative-variable fixing system.**  The physical scalar is
the tetrad component `φ = e_ν^a`, the promoted gauge field is the derivative
coordinate `v = E_{μν}^a`, and the exterior derivative is the honest spacetime
derivative `∂_μ`, so that `v − dφ = E_{μν}^a − ∂_μ e_ν^a`. -/
noncomputable def qgFixingSystem (mu : Fin 4) (f w : SpacetimePoly) :
    DerivativeVariableFixingSystem (fun _ => Mat2R) where
  zero := fun _ => 0
  add := fun _ x y => x + y
  sub := fun _ x y => x - y
  mul := fun _ _ x y => x * y
  d := fun {_ _} x => dMatR mu x
  s := fun {_ g} x => sMatR g x
  d_zero := fun _ _ => dMatR_zero mu
  sub_zero := fun _ x => sub_zero x
  s_nilpotent := fun _ g x => sMatR_nilpotent g x
  s_sub := fun _ g x y => sMatR_sub g x y
  sd_commute := fun _ g x => sMatR_dMatR mu g x
  phi := f • (1 : Mat2R)
  v := w • (1 : Mat2R)
  c := 0
  c_bar := PmR
  B := 1
  def_s_v := sMatR_smul_one w
  def_s_phi := sMatR_smul_one f
  def_s_c_bar := sMatR_PmR
  s_mul_c_bar := sMatR_leibniz
  mul_zero_left := fun x => Matrix.zero_mul x
  mul_zero_right := fun x => Matrix.mul_zero x

/-- The system's gauge field is the concrete constraint `w − ∂_μ f`, times the
identity matrix. -/
theorem qgFixing_gaugeField (mu : Fin 4) (f w : SpacetimePoly) :
    gaugeField (qgFixingSystem mu f w).toGaugeFixingSystem
      = (w - pderiv mu f) • (1 : Mat2R) := by
  change (w • (1 : Mat2R)) - dMatR mu (f • (1 : Mat2R)) = _
  rw [dMatR_smul_one, sub_smul]

/-- **The concrete `v = dφ`.**  The system's gauge field vanishes exactly when
the promoted derivative field is the actual derivative. -/
theorem qgFixing_gaugeField_eq_zero_iff (mu : Fin 4) (f w : SpacetimePoly) :
    gaugeField (qgFixingSystem mu f w).toGaugeFixingSystem = 0 ↔ w = pderiv mu f := by
  rw [qgFixing_gaugeField, smul_one_eq_zero_iff, sub_eq_zero]

/-- Off the fixing surface the constraint is genuinely non-zero. -/
theorem qgFixing_gaugeField_ne_zero_of_not_fixed (mu : Fin 4) (f w : SpacetimePoly)
    (h : w ≠ pderiv mu f) :
    gaugeField (qgFixingSystem mu f w).toGaugeFixingSystem ≠ 0 := by
  rw [Ne, qgFixing_gaugeField_eq_zero_iff]
  exact h

/-- The Nakanishi–Lautrup field of the concrete system is non-zero, so the
Lagrange-multiplier term is not vacuous. -/
theorem qgFixing_B_ne_zero (mu : Fin 4) (f w : SpacetimePoly) :
    ((qgFixingSystem mu f w).B : Mat2R) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [qgFixingSystem] at h00

/-- The system attached to a tetrad configuration and its promoted derivative
fields: `φ = e_ν^a`, `v = E_{μν}^a`. -/
noncomputable def qgSystemOf (T : TetradConfig) (E : DerivFields) (mu nu a : Fin 4) :
    DerivativeVariableFixingSystem (fun _ => Mat2R) :=
  qgFixingSystem mu (T.comp nu a) (E mu nu a)

/-- On the fixing surface `E = ∂e` the concrete gauge field vanishes: the
hypothesis of the abstract theorems of `ChapterQgPhysicalSectorIdentity` is
*discharged*, not assumed. -/
theorem qgSystemOf_gaugeField_eq_zero (T : TetradConfig) (E : DerivFields)
    (hE : Fixed T E) (mu nu a : Fin 4) :
    gaugeField (qgSystemOf T E mu nu a).toGaugeFixingSystem
      = (qgSystemOf T E mu nu a).toGaugeFixingSystem.zero (1, 0) := by
  change gaugeField (qgFixingSystem mu (T.comp nu a) (E mu nu a)).toGaugeFixingSystem = 0
  rw [qgFixing_gaugeField_eq_zero_iff]
  exact (fixed_iff T E).1 hE mu nu a

/-- **The Lagrange-multiplier term vanishes on the concrete fixing surface** —
`lagrange_term_zero_of_fixing` of `ChapterQgPhysicalSectorIdentity`, run on the
concrete 84-dimensional data with the hypothesis proved. -/
theorem qgFixing_lagrange_term_zero (T : TetradConfig) (E : DerivFields)
    (hE : Fixed T E) (mu nu a : Fin 4) :
    (qgSystemOf T E mu nu a).mul (1, 0) (1, 0) (qgSystemOf T E mu nu a).B
        (gaugeField (qgSystemOf T E mu nu a).toGaugeFixingSystem)
      = (qgSystemOf T E mu nu a).zero (2, 0) :=
  lagrange_term_zero_of_fixing (qgSystemOf T E mu nu a)
    (qgSystemOf_gaugeField_eq_zero T E hE mu nu a)

/-- **The gauge-fixing Lagrangian on the concrete fixing surface** reduces to
the ghost term alone — `L_gf_constraint_surface`, run on the concrete data. -/
theorem qgFixing_L_gf_constraint_surface (T : TetradConfig) (E : DerivFields)
    (hE : Fixed T E) (mu nu a : Fin 4) :
    (qgSystemOf T E mu nu a).s (p := 2) (g := -1)
        (Psi (qgSystemOf T E mu nu a).toGaugeFixingSystem)
      = (qgSystemOf T E mu nu a).sub (2, 0) ((qgSystemOf T E mu nu a).zero (2, 0))
          ((qgSystemOf T E mu nu a).mul (1, -1) (1, 1) (qgSystemOf T E mu nu a).c_bar
            (qgSystemOf T E mu nu a).c) :=
  L_gf_constraint_surface (qgSystemOf T E mu nu a)
    (qgSystemOf_gaugeField_eq_zero T E hE mu nu a)

end BookProof.QgDerivativeRealization


