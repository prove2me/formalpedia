-- Prove2me | Definitions.Def_ChapterQgContinuumModeInstance
-- name    : ChapterQgContinuumModeInstance
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T03:05:22.258932+00:00
-- url     : https://prove2.me/theorems/754b8275-69a9-4ba0-8b30-27c9d8aa3bd6
-- title:
--   The Lean 4 theorem `momSq_nonneg` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgContinuumModeInstance`, source chapter `BookProof/ChapterQgContinuumModeInstance.lean`): The continuum (non-lattice) mode instance of the outer-Fock quantum-gravity Hamiltonian What is proved
--
--   `BookProof.ChapterQgVielbeinModeInstance` supplies the mode data of the gauge-fixed quantum-gravity Hamiltonian on a **finite** mode set — the lattice truncation, in which the spatial derivatives `∂_μ e_ν^a` are finite differences between neighbouring sites and only finitely many modes are kept. This module removes both approximations.
--
--   The modes are the exact Fourier modes of the vielbein on the periodic spatial box: a momentum `k ∈ ℤ³` together with a spatial index `ν` and an internal index `i`. There are **infinitely many** of them — no truncation to a finite mode set — and the spatial derivative is the exact Fourier multiplier `∂_μ ↦ i k_μ`, not a finite difference. The torsion `T_{μν}^i = ∂_μ e_ν^i − ∂_ν e_μ^i` is therefore the *exact* linear form `k_μ e_ν^i − k_ν e_μ^i` on the modes (`torsionCoef`), and the vielbein self-interaction `½ Σ T²` is its Gram matrix (`contTorsionGram`).
--
--   The mode matrices are banded because momentum is conserved: only the nine components at one and the same momentum are coupled, so each band has exactly nine elements (`card_cNbr`). Across a band the vielbein energy `σ_k = 1 + |k|²` is constant, and the torsion Gram entry at momentum `k` is bounded by `108 |k|² ≤ 108 σ_k`; this is what makes the Faris–Lavine bounds of `QgModeData` hold **uniformly in the momentum**, with the single constant `κ = 108 + |g|` and band size `9`, however large the momenta.
--
--   * `contTorsionGram_herm`, `contCoupling_herm` — the mode matrices are Hermitian. * `norm_contTorsionGram_le`, `norm_contCoupling_le` — the uniform entrywise bounds. * `qgContinuumModes` — the mode data of the continuum model. * **`qgContinuum_essentiallySelfAdjointOn`**, `qgContinuum_ext_core` and **`starobinsky_qgContinuum_esa`** — the resulting quantum-gravity Hamiltonian on the outer Fock space `ℓ²(modes; L²(ℝ_φ))`, with all torsion self-interactions, the scalaron–vielbein coupling at arbitrary coupling constant `g` and the full exponential Einstein-frame Starobinsky wall, is essentially self-adjoint on the domain of the lifted Friedrichs extension of the positive one-particle operator.
--
--   Scope of *this* module: the spatial manifold is a periodic box (three-torus), so the momenta are `ℤ³`; the mode expansion is exact — infinitely many modes, exact derivative symbol. The box is not a limitation of the analysis: `BookProof.ChapterQgManifoldModeInstance` carries the same construction over a **general** spatial manifold, where in the vielbein variables the mode data is an arbitrary Laplace-type spectrum together with the Hodge-diagonal torsion eigenvalues. No continuum limit of the box size, no spectral information and no mass gap is claimed here.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgContinuumModeInstance.lean

import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib


/-!
# The continuum (non-lattice) mode instance of the outer-Fock quantum-gravity Hamiltonian

`BookProof.ChapterQgVielbeinModeInstance` supplies the mode data of the gauge-fixed
quantum-gravity Hamiltonian on a **finite** mode set — the lattice truncation, in which the
spatial derivatives `∂_μ e_ν^a` are finite differences between neighbouring sites and only
finitely many modes are kept.  This module removes both approximations.

The modes are the exact Fourier modes of the vielbein on the periodic spatial box: a
momentum `k ∈ ℤ³` together with a spatial index `ν` and an internal index `i`.  There are
**infinitely many** of them — no truncation to a finite mode set — and the spatial
derivative is the exact Fourier multiplier `∂_μ ↦ i k_μ`, not a finite difference.  The
torsion `T_{μν}^i = ∂_μ e_ν^i − ∂_ν e_μ^i` is therefore the *exact* linear form
`k_μ e_ν^i − k_ν e_μ^i` on the modes (`torsionCoef`), and the vielbein self-interaction
`½ Σ T²` is its Gram matrix (`contTorsionGram`).

The mode matrices are banded because momentum is conserved: only the nine components at one
and the same momentum are coupled, so each band has exactly nine elements
(`card_cNbr`).  Across a band the vielbein energy `σ_k = 1 + |k|²` is constant, and the
torsion Gram entry at momentum `k` is bounded by `108 |k|² ≤ 108 σ_k`; this is what makes
the Faris–Lavine bounds of `QgModeData` hold **uniformly in the momentum**, with the single
constant `κ = 108 + |g|` and band size `9`, however large the momenta.

## What is proved

* `contTorsionGram_herm`, `contCoupling_herm` — the mode matrices are Hermitian.
* `norm_contTorsionGram_le`, `norm_contCoupling_le` — the uniform entrywise bounds.
* `qgContinuumModes` — the mode data of the continuum model.
* **`qgContinuum_essentiallySelfAdjointOn`**, `qgContinuum_ext_core` and
  **`starobinsky_qgContinuum_esa`** — the resulting quantum-gravity Hamiltonian on the outer
  Fock space `ℓ²(modes; L²(ℝ_φ))`, with all torsion self-interactions, the
  scalaron–vielbein coupling at arbitrary coupling constant `g` and the full exponential
  Einstein-frame Starobinsky wall, is essentially self-adjoint on the domain of the lifted
  Friedrichs extension of the positive one-particle operator.

Scope of *this* module: the spatial manifold is a periodic box (three-torus), so the momenta
are `ℤ³`; the mode expansion is exact — infinitely many modes, exact derivative symbol.  The
box is not a limitation of the analysis: `BookProof.ChapterQgManifoldModeInstance` carries
the same construction over a **general** spatial manifold, where in the vielbein variables
the mode data is an arbitrary Laplace-type spectrum together with the Hodge-diagonal torsion
eigenvalues.  No continuum limit of the box size, no spectral information and no mass gap is
claimed here.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgContinuumModeInstance

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

/-! ## 1. The continuum modes -/

/-- A spatial momentum on the periodic box. -/
abbrev Mom := Fin 3 → ℤ

/-- A continuum vielbein mode: a momentum together with the spatial index `ν` and the
internal index `i` of the component `e_ν^i`. -/
abbrev CMode := Mom × Fin 3 × Fin 3

/-- `|k|²`. -/
def momSq (k : Mom) : ℝ := ∑ mu : Fin 3, ((k mu : ℝ)) ^ 2

theorem momSq_nonneg (k : Mom) : 0 ≤ momSq k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_le_momSq (k : Mom) (mu : Fin 3) : ((k mu : ℝ)) ^ 2 ≤ momSq k :=
  Finset.single_le_sum (f := fun m : Fin 3 => ((k m : ℝ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ mu)

/-- The vielbein energy of a mode: `σ_k = 1 + |k|²`, the exact free symbol. -/
def cSig (x : CMode) : ℝ := 1 + momSq x.1

theorem one_le_cSig (x : CMode) : 1 ≤ cSig x := by
  have := momSq_nonneg x.1
  simp only [cSig]
  linarith

theorem cSig_nonneg (x : CMode) : 0 ≤ cSig x :=
  le_trans zero_le_one (one_le_cSig x)

/-- The band of a mode: the nine components at the same momentum.  Momentum conservation is
what makes the mode matrices banded. -/
def cNbr (x : CMode) : Finset CMode :=
  ({x.1} : Finset Mom) ×ˢ (Finset.univ : Finset (Fin 3 × Fin 3))

theorem mem_cNbr {x y : CMode} : y ∈ cNbr x ↔ y.1 = x.1 := by
  constructor
  · intro h
    simp only [cNbr, Finset.mem_product, Finset.mem_singleton] at h
    exact h.1
  · intro h
    simp only [cNbr, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
    exact h

theorem card_cNbr (x : CMode) : ((cNbr x).card : ℝ) = 9 := by
  simp [cNbr]

/-! ## 2. The exact torsion and its Gram matrix -/

/-- The exact Fourier coefficient of the torsion `T_{μν}^i = ∂_μ e_ν^i − ∂_ν e_μ^i` at
momentum `k`, as a linear form on the modes: `k_μ e_ν^i − k_ν e_μ^i`.  The overall factor
`i` of the derivative symbol is a phase and is omitted; it cancels in the Gram matrix. -/
def torsionCoef (k : Mom) (mu nu i : Fin 3) (z : CMode) : ℂ :=
  (if z.2 = (nu, i) then ((k mu : ℤ) : ℂ) else 0) - (if z.2 = (mu, i) then ((k nu : ℤ) : ℂ) else 0)

theorem torsionCoef_conj (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    (starRingEnd ℂ) (torsionCoef k mu nu i z) = torsionCoef k mu nu i z := by
  simp only [torsionCoef, map_sub]
  congr 1 <;> split <;> simp

theorem norm_torsionCoef_le (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    ‖torsionCoef k mu nu i z‖ ≤ |((k mu : ℝ))| + |((k nu : ℝ))| := by
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_) <;> split
  · simp
  · simp only [norm_zero]; positivity
  · simp
  · simp only [norm_zero]; positivity

theorem norm_torsionCoef_mul_le (k : Mom) (mu nu i : Fin 3) (z w : CMode) :
    ‖(starRingEnd ℂ) (torsionCoef k mu nu i z) * torsionCoef k mu nu i w‖ ≤ 4 * momSq k := by
  have h1 := norm_torsionCoef_le k mu nu i z
  have h2 := norm_torsionCoef_le k mu nu i w
  have ha := sq_le_momSq k mu
  have hb := sq_le_momSq k nu
  have hsa : |((k mu : ℝ))| ^ 2 = ((k mu : ℝ)) ^ 2 := sq_abs _
  have hsb : |((k nu : ℝ))| ^ 2 = ((k nu : ℝ)) ^ 2 := sq_abs _
  have hn1 : (0 : ℝ) ≤ ‖torsionCoef k mu nu i z‖ := norm_nonneg _
  have hn2 : (0 : ℝ) ≤ ‖torsionCoef k mu nu i w‖ := norm_nonneg _
  rw [norm_mul, RCLike.norm_conj]
  nlinarith [abs_nonneg ((k mu : ℝ)), abs_nonneg ((k nu : ℝ)),
    sq_nonneg (|((k mu : ℝ))| - |((k nu : ℝ))|)]

/-- **The complete vielbein self-interaction in the continuum mode basis**: the Gram matrix
of all exact torsion forms.  It is diagonal in the momentum — momentum conservation — and a
full `9 × 9` matrix in the component indices at each momentum. -/
def contTorsionGram (x y : CMode) : ℂ :=
  if x.1 = y.1 then
    ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
      (starRingEnd ℂ) (torsionCoef x.1 mu nu i x) * torsionCoef x.1 mu nu i y
  else 0

theorem contTorsionGram_herm (x y : CMode) :
    contTorsionGram y x = (starRingEnd ℂ) (contTorsionGram x y) := by
  by_cases h : x.1 = y.1
  · have hy : y.1 = x.1 := h.symm
    simp only [contTorsionGram]
    rw [if_pos hy, if_pos h, hy, map_sum]
    refine Finset.sum_congr rfl fun mu _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, torsionCoef_conj]
    ring
  · simp only [contTorsionGram, if_neg h, if_neg (Ne.symm h), map_zero]

theorem contTorsionGram_off {x y : CMode} (h : y ∉ cNbr x) : contTorsionGram x y = 0 := by
  have hne : ¬ x.1 = y.1 := fun hh => h (mem_cNbr.mpr hh.symm)
  simp only [contTorsionGram, if_neg hne]

/-- The uniform entrywise bound: the torsion Gram entry at momentum `k` is at most
`108 |k|²`, hence at most `108 σ_k`. -/
theorem norm_contTorsionGram_le (x y : CMode) :
    ‖contTorsionGram x y‖ ≤ 108 * momSq x.1 := by
  by_cases h : x.1 = y.1
  · simp only [contTorsionGram, if_pos h]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ mu ∈ (Finset.univ : Finset (Fin 3)),
        ‖∑ nu : Fin 3, ∑ i : Fin 3,
            (starRingEnd ℂ) (torsionCoef x.1 mu nu i x) * torsionCoef x.1 mu nu i y‖
          ≤ 36 * momSq x.1 := by
      intro mu _
      refine le_trans (norm_sum_le _ _) ?_
      have hterm2 : ∀ nu ∈ (Finset.univ : Finset (Fin 3)),
          ‖∑ i : Fin 3,
              (starRingEnd ℂ) (torsionCoef x.1 mu nu i x) * torsionCoef x.1 mu nu i y‖
            ≤ 12 * momSq x.1 := by
        intro nu _
        refine le_trans (norm_sum_le _ _) ?_
        have hterm3 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
            ‖(starRingEnd ℂ) (torsionCoef x.1 mu nu i x) * torsionCoef x.1 mu nu i y‖
              ≤ 4 * momSq x.1 := fun i _ => norm_torsionCoef_mul_le _ _ _ _ _ _
        calc ∑ i : Fin 3, ‖(starRingEnd ℂ) (torsionCoef x.1 mu nu i x)
                * torsionCoef x.1 mu nu i y‖
            ≤ ∑ _i : Fin 3, 4 * momSq x.1 := Finset.sum_le_sum hterm3
          _ = 12 * momSq x.1 := by simp [Finset.sum_const]; ring
      calc ∑ nu : Fin 3, ‖∑ i : Fin 3,
              (starRingEnd ℂ) (torsionCoef x.1 mu nu i x) * torsionCoef x.1 mu nu i y‖
          ≤ ∑ _nu : Fin 3, 12 * momSq x.1 := Finset.sum_le_sum hterm2
        _ = 36 * momSq x.1 := by simp [Finset.sum_const]; ring
    calc ∑ mu : Fin 3, ‖∑ nu : Fin 3, ∑ i : Fin 3,
            (starRingEnd ℂ) (torsionCoef x.1 mu nu i x) * torsionCoef x.1 mu nu i y‖
        ≤ ∑ _mu : Fin 3, 36 * momSq x.1 := Finset.sum_le_sum hterm
      _ = 108 * momSq x.1 := by simp [Finset.sum_const]; ring
  · have hnn := momSq_nonneg x.1
    simp only [contTorsionGram, if_neg h, norm_zero]
    linarith

/-! ## 3. The scalaron–vielbein coupling -/

/-- The trace part of the vielbein, the combination the scalaron couples to. -/
def cTrace (x : CMode) : ℝ := if x.2.1 = x.2.2 then 1 else 0

theorem abs_cTrace_le (x : CMode) : |cTrace x| ≤ 1 := by
  simp only [cTrace]; split <;> simp

/-- **The scalaron–vielbein coupling** at coupling constant `g`: the scalaron field `φ` of a
mode multiplied by the trace of the vielbein, at equal momentum (momentum conservation). -/
def contCoupling (g : ℝ) (x y : CMode) : ℂ :=
  if x.1 = y.1 then ((g * cTrace x * cTrace y : ℝ) : ℂ) else 0

theorem contCoupling_herm (g : ℝ) (x y : CMode) :
    contCoupling g y x = (starRingEnd ℂ) (contCoupling g x y) := by
  by_cases h : x.1 = y.1
  · have hy : y.1 = x.1 := h.symm
    simp only [contCoupling]
    rw [if_pos hy, if_pos h, Complex.conj_ofReal]
    norm_cast
    ring
  · simp only [contCoupling, if_neg h, if_neg (Ne.symm h), map_zero]

theorem contCoupling_off (g : ℝ) {x y : CMode} (h : y ∉ cNbr x) : contCoupling g x y = 0 := by
  have hne : ¬ x.1 = y.1 := fun hh => h (mem_cNbr.mpr hh.symm)
  simp only [contCoupling, if_neg hne]

theorem norm_contCoupling_le (g : ℝ) (x y : CMode) : ‖contCoupling g x y‖ ≤ |g| := by
  by_cases h : x.1 = y.1
  · simp only [contCoupling, if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 := abs_cTrace_le x
    have h2 := abs_cTrace_le y
    have hg := abs_nonneg g
    calc |g| * |cTrace x| * |cTrace y| ≤ |g| * 1 * 1 := by gcongr
      _ = |g| := by ring
  · simp only [contCoupling, if_neg h, norm_zero]
    exact abs_nonneg g

/-! ## 4. The mode data and essential self-adjointness -/

/-- **The mode data of the continuum (non-lattice) gauge-fixed quantum-gravity model**: the
exact free symbol `σ_k = 1 + |k|²`, the Gram matrix of all exact torsion forms and the
scalaron–vielbein coupling, on the infinite set of Fourier modes.  All the Faris–Lavine
bounds hold with the single constant `κ = 108 + |g|` and band size `9`, uniformly in the
momentum. -/
def qgContinuumModes (g : ℝ) : QgModeData CMode :=
  ofBounds cSig one_le_cSig contTorsionGram (contCoupling g) cNbr
    (fun a b => by rw [mem_cNbr, mem_cNbr, eq_comm])
    (fun _ _ hb => contTorsionGram_off hb) (fun _ _ hb => contCoupling_off g hb)
    contTorsionGram_herm (contCoupling_herm g)
    (108 + |g|) 9 (by positivity) (by norm_num)
    (fun a => le_of_eq (card_cNbr a))
    (fun a b => by
      by_cases h : a.1 = b.1
      · have hmin : min (cSig a) (cSig b) = cSig a := by
          simp only [cSig]
          rw [h]
          exact min_self _
        have hb := norm_contTorsionGram_le a b
        have hnn := momSq_nonneg a.1
        have hg := abs_nonneg g
        rw [hmin]
        simp only [cSig]
        nlinarith
      · have hz : contTorsionGram a b = 0 := by simp only [contTorsionGram, if_neg h]
        have h1 : (1 : ℝ) ≤ min (cSig a) (cSig b) := le_min (one_le_cSig a) (one_le_cSig b)
        have hg := abs_nonneg g
        rw [hz, norm_zero]
        nlinarith)
    (fun a b => le_trans (norm_contCoupling_le g a b) (by have := abs_nonneg g; linarith))
    (fun a b hb => by
      have h : b.1 = a.1 := mem_cNbr.mp hb
      have hcs : cSig a = cSig b := by simp only [cSig, h]
      have hg := abs_nonneg g
      rw [hcs, sub_self, abs_zero]
      linarith)

/-- **Essential self-adjointness of the continuum quantum-gravity Hamiltonian on the outer
Fock space.**  Infinitely many exact Fourier modes, no lattice discretization of the spatial
derivatives, the complete torsion self-interaction of the vielbein, the scalaron–vielbein
coupling at arbitrary coupling constant `g` and an arbitrary smooth non-negative wall for
the scalaron. -/
theorem qgContinuum_essentiallySelfAdjointOn (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (secN W (qgContinuumModes g)).dom
      (secData W (qgContinuumModes g)).ext :=
  secHam_essentiallySelfAdjointOn W _

/-- The self-adjoint realization restricts to the Hamiltonian on the finite-particle core. -/
theorem qgContinuum_ext_core (W : WallPot) (g : ℝ) (p : secCore (ι := CMode)) :
    (secData W (qgContinuumModes g)).ext
        ⟨(p : Sec CMode), (secData W (qgContinuumModes g)).gc.le p.2⟩
      = secHam W (qgContinuumModes g) p :=
  secData_ext_core W _ p

/-! ## 5. Non-vacuity -/

/-- The mode set is infinite: no truncation to finitely many modes. -/
theorem infinite_cmode : Infinite CMode := inferInstance

/-- A unit momentum in the first spatial direction. -/
def unitMom : Mom := fun j => if j = 0 then 1 else 0

/-- The torsion self-interaction really is present: its Gram matrix is not the zero
matrix. -/
theorem contTorsionGram_ne_zero :
    contTorsionGram ((unitMom, 1, 0) : CMode) (unitMom, 1, 0) ≠ 0 := by
  simp only [contTorsionGram, torsionCoef, Fin.sum_univ_three, unitMom]
  norm_num [Fin.ext_iff]

/-- The scalaron–vielbein coupling really is present whenever the coupling constant is
non-zero. -/
theorem contCoupling_ne_zero (g : ℝ) (hg : g ≠ 0) (k : Mom) :
    contCoupling g ((k, 0, 0) : CMode) (k, 0, 0) ≠ 0 := by
  simp only [contCoupling, cTrace]
  norm_num [hg]



end

end BookProof.QgContinuumModeInstance


