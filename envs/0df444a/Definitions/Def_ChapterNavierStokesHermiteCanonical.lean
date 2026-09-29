-- Prove2me | Definitions.Def_ChapterNavierStokesHermiteCanonical
-- name    : ChapterNavierStokesHermiteCanonical
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T10:48:26.747159+00:00
-- url     : https://prove2.me/theorems/d43d07cf-3a99-4023-be72-4f41e4b7e99e
-- title:
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities for a concrete operator `nsH` ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesHermiteCanonical`, source chapter `BookProof/ChapterNavierStokesHermiteCanonical.lean`).
--
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities for a concrete operator `nsH` on `ℓ²(ℕ)` — the `±2`-shift with amplitudes `w(n) = (κ/2)√((n+1)(n+2))` — and for the diagonal comparison operator `diagMax (oscSymbol κ)`. This module verifies that these two operators really *are* the Navier–Stokes objects they are advertised to be, namely
--
--   * `H = ½(π V + V π)`, the symmetrised first-order transport operator, and * `N = π² + V² + I`, the comparison operator built from the squares of the individual non-commuting pieces,
--
--   for the canonical pair `π = -i ∂/∂u`, `u` of the fiber and the *linear* advection field `V(u) = κ u`. Everything is checked on the finite-mode core `lpFiniteModes ℕ`, which the Hermite functions span.
--
--   * `ann`, `cre` — the annihilation and creation operators of the Hermite basis, with `[a, a†] = I` (`comm_ann_cre`); * `mom κ = i√(κ/2)(a† - a)`, `pos κ = (2κ)^{-1/2}(a + a†)`, `drift κ = κ · pos κ` — the momentum, the fiber coordinate and the advection field; * `comm_mom_pos` — **`[π, u] = -i`**: the two are genuinely non-commuting, which is the whole point of the Faris–Lavine mechanism; * `comparison_eq` — **`π² + V² + I = N`**, the diagonal comparison operator of the Faris–Lavine chapter; * `hamiltonian_eq` — **`½(πV + Vπ) = H`**, the `±2`-shift operator of the Faris–Lavine chapter; * `canonical_essentiallySelfAdjointOn_core` — hence the *canonically written* Navier–Stokes fiber Hamiltonian `½(πV + Vπ)` is essentially self-adjoint on the finite-mode core.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesHermiteCanonical.lean

import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Mathlib

import Mathlib

/-!
# The canonical pair behind the Navier–Stokes fiber Hamiltonian

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities for a concrete operator `nsH` on `ℓ²(ℕ)` — the `±2`-shift with
amplitudes `w(n) = (κ/2)√((n+1)(n+2))` — and for the diagonal comparison operator
`diagMax (oscSymbol κ)`.  This module verifies that these two operators really
*are* the Navier–Stokes objects they are advertised to be, namely

* `H = ½(π V + V π)`, the symmetrised first-order transport operator, and
* `N = π² + V² + I`, the comparison operator built from the squares of the
  individual non-commuting pieces,

for the canonical pair `π = -i ∂/∂u`, `u` of the fiber and the *linear* advection
field `V(u) = κ u`.  Everything is checked on the finite-mode core
`lpFiniteModes ℕ`, which the Hermite functions span.

## Contents

* `ann`, `cre` — the annihilation and creation operators of the Hermite basis,
  with `[a, a†] = I` (`comm_ann_cre`);
* `mom κ = i√(κ/2)(a† - a)`, `pos κ = (2κ)^{-1/2}(a + a†)`, `drift κ = κ · pos κ`
  — the momentum, the fiber coordinate and the advection field;
* `comm_mom_pos` — **`[π, u] = -i`**: the two are genuinely non-commuting, which
  is the whole point of the Faris–Lavine mechanism;
* `comparison_eq` — **`π² + V² + I = N`**, the diagonal comparison operator of
  the Faris–Lavine chapter;
* `hamiltonian_eq` — **`½(πV + Vπ) = H`**, the `±2`-shift operator of the
  Faris–Lavine chapter;
* `canonical_essentiallySelfAdjointOn_core` — hence the *canonically written*
  Navier–Stokes fiber Hamiltonian `½(πV + Vπ)` is essentially self-adjoint on the
  finite-mode core.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace HermiteCanonical

open LpNat FarisLavine IkebeKato HermiteFarisLavine

/-! ## The core, and states given by their coordinates -/

/-- A finitely supported coordinate sequence as a state of the finite-mode
core. -/
noncomputable def mkCore {X : ℕ → ℂ} (h : (Function.support X).Finite) : lpFiniteModes ℕ :=
  ⟨⟨X, memLpTwo_of_finite_support h⟩, h⟩
@[simp] theorem mkCore_coe {X : ℕ → ℂ} (h : (Function.support X).Finite) (n : ℕ) :
    (((mkCore h : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n = X n := rfl



theorem support_finite (x : lpFiniteModes ℕ) :
    (Function.support (((x : L2I ℕ) : ℕ → ℂ))).Finite := x.2

/-! ## Annihilation and creation -/

/-- `a x` has coordinates `√(n+1) xₙ₊₁`. -/
noncomputable def annFun (X : ℕ → ℂ) : ℕ → ℂ := fun n => (Real.sqrt (n + 1) : ℂ) * X (n + 1)

/-- `a† x` has coordinates `√n xₙ₋₁` (and `0` at `n = 0`, since `√0 = 0`). -/
noncomputable def creFun (X : ℕ → ℂ) : ℕ → ℂ := fun n => (Real.sqrt n : ℂ) * X (n - 1)

theorem support_annFun {X : ℕ → ℂ} (h : (Function.support X).Finite) :
    (Function.support (annFun X)).Finite := by
  refine Set.Finite.subset (h.preimage (f := fun n : ℕ => n + 1) (Set.injOn_of_injective
    (fun a b hab => by omega))) ?_
  intro n hn
  simp only [Function.mem_support, annFun] at hn
  simp only [Set.mem_preimage, Function.mem_support]
  intro h0
  exact hn (by rw [h0, mul_zero])

theorem support_creFun {X : ℕ → ℂ} (h : (Function.support X).Finite) :
    (Function.support (creFun X)).Finite := by
  refine Set.Finite.subset (h.image (fun n : ℕ => n + 1)) ?_
  intro n hn
  simp only [Function.mem_support, creFun] at hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hn
    simp [h0]
  refine ⟨n - 1, ?_, by simp only []; omega⟩
  simp only [Function.mem_support]
  intro h0
  exact hn (by rw [h0, mul_zero])

/-- **The annihilation operator** of the Hermite basis. -/
noncomputable def ann : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ where
  toFun x := mkCore (support_annFun (support_finite x))
  map_add' x y := by
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    simp only [mkCore_coe, annFun, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    simp only [mkCore_coe, annFun, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- **The creation operator** of the Hermite basis. -/
noncomputable def cre : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ where
  toFun x := mkCore (support_creFun (support_finite x))
  map_add' x y := by
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    simp only [mkCore_coe, creFun, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    simp only [mkCore_coe, creFun, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring







/-! ### Coordinates of the quadratic expressions -/















/-! ## The canonical pair and the advection field -/

variable {κ : ℝ}

/-- The momentum `π = i√(κ/2)(a† - a) = -i ∂/∂u`. -/
noncomputable def mom (κ : ℝ) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  (Complex.I * (Real.sqrt (κ / 2) : ℂ)) • (cre - ann)

/-- The fiber coordinate `u = (2κ)^(-1/2)(a + a†)`. -/
noncomputable def pos (κ : ℝ) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) • (cre + ann)

/-- The linear advection field `V(u) = κ u = √(κ/2)(a + a†)`. -/
noncomputable def drift (κ : ℝ) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  ((Real.sqrt (κ / 2) : ℝ) : ℂ) • (cre + ann)

/-! ### The three algebraic identities of the canonical pair -/







/-! ### Scalars -/

















end HermiteCanonical

end BookProof.NavierStokesFlow


