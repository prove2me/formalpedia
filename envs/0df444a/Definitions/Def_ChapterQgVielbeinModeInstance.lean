-- Prove2me | Definitions.Def_ChapterQgVielbeinModeInstance
-- name    : ChapterQgVielbeinModeInstance
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T02:59:57.265575+00:00
-- url     : https://prove2.me/theorems/c24ec102-3f83-490c-b3d0-7c52fa338537
-- title:
--   The Lean 4 theorem `is` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgVielbeinModeInstance`, source chapter `BookProof/ChapterQgVielbeinModeInstance.lean`): A concrete gauge-fixed vielbein instance of the outer-Fock quantum-gravity Hamiltonian What is proved
--
--   `BookProof.ChapterScalaronOuterFockFL` proves essential self-adjointness of the full quantum-gravity Hamiltonian on the outer Fock space `⊕_a L²(ℝ)` — the scalaron in vielbein variables, with the full exponential Starobinsky wall and *all* interaction and coupling terms — for an arbitrary `QgModeData`. This module supplies the mode data, so that the theorem is not conditional on an unmet hypothesis.
--
--   * `ofBounds` — the mode data assembled from elementary, checkable bounds: a Hermitian banded vielbein self-interaction `A` with `‖A a b‖ ≤ κ·min(σ_a, σ_b)`, a Hermitian banded scalaron–vielbein coupling `B` with `‖B a b‖ ≤ κ`, an energy spread `|σ_a − σ_b| ≤ κ` across the band and a bound `deg` on the band size; the Faris–Lavine constant is `K = deg·κ·(1 + κ)`. * `ofFintype` — for a **finite** mode set (the gauge-fixed lattice truncation) *every* Hermitian pair `A`, `B` is admissible, with no smallness assumption whatsoever. * `torsionForm`, `torsionGram` — the discrete torsion `∂_μ e_ν^a − ∂_ν e_μ^a` on the periodic three-dimensional spatial lattice, and the Gram matrix of all torsion terms: the complete vielbein self-interaction of the 3D gauge-fixed gravity Hamiltonian. * `traceForm`, `scalaronCoupling` — the coupling of the scalaron to the trace of the vielbein. * `qgLatticeModes` — the mode data of the 3D gauge-fixed vielbein lattice model. * **`qgLattice_essentiallySelfAdjointOn`**, **`starobinsky_qgLattice_esa`** — essential self-adjointness of the resulting outer-Fock quantum-gravity Hamiltonian, the second with the Einstein-frame Starobinsky wall in its full exponential form.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgVielbeinModeInstance.lean

import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Mathlib


/-!
# A concrete gauge-fixed vielbein instance of the outer-Fock quantum-gravity Hamiltonian

`BookProof.ChapterScalaronOuterFockFL` proves essential self-adjointness of the full
quantum-gravity Hamiltonian on the outer Fock space `⊕_a L²(ℝ)` — the scalaron in vielbein
variables, with the full exponential Starobinsky wall and *all* interaction and coupling
terms — for an arbitrary `QgModeData`.  This module supplies the mode data, so that the
theorem is not conditional on an unmet hypothesis.

## What is proved

* `ofBounds` — the mode data assembled from elementary, checkable bounds: a Hermitian
  banded vielbein self-interaction `A` with `‖A a b‖ ≤ κ·min(σ_a, σ_b)`, a Hermitian banded
  scalaron–vielbein coupling `B` with `‖B a b‖ ≤ κ`, an energy spread `|σ_a − σ_b| ≤ κ`
  across the band and a bound `deg` on the band size; the Faris–Lavine constant is
  `K = deg·κ·(1 + κ)`.
* `ofFintype` — for a **finite** mode set (the gauge-fixed lattice truncation) *every*
  Hermitian pair `A`, `B` is admissible, with no smallness assumption whatsoever.
* `torsionForm`, `torsionGram` — the discrete torsion `∂_μ e_ν^a − ∂_ν e_μ^a` on the
  periodic three-dimensional spatial lattice, and the Gram matrix of all torsion terms:
  the complete vielbein self-interaction of the 3D gauge-fixed gravity Hamiltonian.
* `traceForm`, `scalaronCoupling` — the coupling of the scalaron to the trace of the
  vielbein.
* `qgLatticeModes` — the mode data of the 3D gauge-fixed vielbein lattice model.
* **`qgLattice_essentiallySelfAdjointOn`**, **`starobinsky_qgLattice_esa`** — essential
  self-adjointness of the resulting outer-Fock quantum-gravity Hamiltonian, the second with
  the Einstein-frame Starobinsky wall in its full exponential form.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgVielbeinModeInstance

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

variable {ι : Type*}

/-! ## 1. Mode data from elementary bounds -/

private theorem sum_le_deg {nbr : Finset ι} {deg c : ℝ} (hdeg : ((nbr.card : ℝ)) ≤ deg)
    (hc : 0 ≤ c) (f : ι → ℝ) (hf : ∀ b ∈ nbr, f b ≤ c) : ∑ b ∈ nbr, f b ≤ deg * c :=
  calc ∑ b ∈ nbr, f b ≤ ∑ _b ∈ nbr, c := Finset.sum_le_sum hf
    _ = (nbr.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ deg * c := mul_le_mul_of_nonneg_right hdeg hc

/-- **The mode data of a banded gauge-fixed quantum-gravity Hamiltonian.**  All five
Faris–Lavine bounds follow from the entrywise bounds on the vielbein self-interaction `A`
and the scalaron coupling `B`, from the energy spread across the band, and from a bound on
the band size. -/
def ofBounds (sig : ι → ℝ) (one_le_sig : ∀ a, 1 ≤ sig a) (A B : ι → ι → ℂ)
    (nbr : ι → Finset ι) (mem_nbr_comm : ∀ a b, b ∈ nbr a ↔ a ∈ nbr b)
    (A_off : ∀ a b, b ∉ nbr a → A a b = 0) (B_off : ∀ a b, b ∉ nbr a → B a b = 0)
    (A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b))
    (B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b))
    (kap deg : ℝ) (kap_nonneg : 0 ≤ kap) (deg_nonneg : 0 ≤ deg)
    (hdeg : ∀ a, ((nbr a).card : ℝ) ≤ deg)
    (hA : ∀ a b, ‖A a b‖ ≤ kap * min (sig a) (sig b)) (hB : ∀ a b, ‖B a b‖ ≤ kap)
    (hgap : ∀ a b, b ∈ nbr a → |sig a - sig b| ≤ kap) :
    QgModeData ι where
  sig := sig
  one_le_sig := one_le_sig
  A := A
  B := B
  nbr := nbr
  mem_nbr_comm := mem_nbr_comm
  A_off := A_off
  B_off := B_off
  A_herm := A_herm
  B_herm := B_herm
  K := deg * kap * (1 + kap)
  K_nonneg := by positivity
  A_rel_row := by
    intro a
    have hterm : ∀ b ∈ nbr a, ‖A a b‖ / sig b ≤ kap := by
      intro b _
      have hpos : (0 : ℝ) < sig b := lt_of_lt_of_le zero_lt_one (one_le_sig b)
      rw [div_le_iff₀ hpos]
      exact le_trans (hA a b) (mul_le_mul_of_nonneg_left (min_le_right _ _) kap_nonneg)
    have := sum_le_deg (hdeg a) kap_nonneg _ hterm
    nlinarith [mul_nonneg deg_nonneg kap_nonneg]
  A_rel_col := by
    intro a
    have hsa : (0 : ℝ) ≤ sig a := le_trans zero_le_one (one_le_sig a)
    have hterm : ∀ b ∈ nbr a, ‖A a b‖ ≤ kap * sig a := by
      intro b _
      exact le_trans (hA a b) (mul_le_mul_of_nonneg_left (min_le_left _ _) kap_nonneg)
    have := sum_le_deg (hdeg a) (mul_nonneg kap_nonneg hsa) _ hterm
    nlinarith [mul_nonneg (mul_nonneg deg_nonneg kap_nonneg) hsa]
  A_comm := by
    intro a
    have hsa : (0 : ℝ) ≤ sig a := le_trans zero_le_one (one_le_sig a)
    have hterm : ∀ b ∈ nbr a, |sig a - sig b| * ‖A a b‖ ≤ kap * (kap * sig a) := by
      intro b hb
      have h1 : |sig a - sig b| ≤ kap := hgap a b hb
      have h2 : ‖A a b‖ ≤ kap * sig a :=
        le_trans (hA a b) (mul_le_mul_of_nonneg_left (min_le_left _ _) kap_nonneg)
      have h3 : (0 : ℝ) ≤ ‖A a b‖ := norm_nonneg _
      nlinarith [abs_nonneg (sig a - sig b)]
    have := sum_le_deg (hdeg a) (mul_nonneg kap_nonneg (mul_nonneg kap_nonneg hsa)) _ hterm
    nlinarith [mul_nonneg (mul_nonneg deg_nonneg kap_nonneg) hsa]
  B_rel := by
    intro a
    have := sum_le_deg (hdeg a) kap_nonneg _ (fun b _ => hB a b)
    nlinarith [mul_nonneg deg_nonneg kap_nonneg]
  B_comm := by
    intro a
    have hterm : ∀ b ∈ nbr a, |sig a - sig b| * ‖B a b‖ ≤ kap * kap := by
      intro b hb
      have h1 : |sig a - sig b| ≤ kap := hgap a b hb
      have h3 : (0 : ℝ) ≤ ‖B a b‖ := norm_nonneg _
      nlinarith [abs_nonneg (sig a - sig b), hB a b]
    have := sum_le_deg (hdeg a) (mul_nonneg kap_nonneg kap_nonneg) _ hterm
    nlinarith [mul_nonneg deg_nonneg kap_nonneg]

/-! ## 2. Finitely many modes: no smallness assumption at all -/

section Fintype

variable [Fintype ι] [DecidableEq ι]

/-- The bound used for a finite mode set: large enough for every entry of `A` and `B` and
for the energy spread. -/
def finKap (sig : ι → ℝ) (A B : ι → ι → ℂ) : ℝ :=
  ∑ a : ι, ∑ b : ι, (‖A a b‖ + ‖B a b‖ + |sig a - sig b|)

omit [DecidableEq ι] in
theorem finKap_nonneg (sig : ι → ℝ) (A B : ι → ι → ℂ) : 0 ≤ finKap sig A B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq ι] in
theorem le_finKap (sig : ι → ℝ) (A B : ι → ι → ℂ) (a b : ι) :
    ‖A a b‖ + ‖B a b‖ + |sig a - sig b| ≤ finKap sig A B := by
  refine le_trans (Finset.single_le_sum (f := fun c => ‖A a c‖ + ‖B a c‖ + |sig a - sig c|)
    (fun c _ => by positivity) (Finset.mem_univ b)) ?_
  exact Finset.single_le_sum
    (f := fun c => ∑ b : ι, (‖A c b‖ + ‖B c b‖ + |sig c - sig b|))
    (fun c _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)

/-- **Every Hermitian pair of mode matrices on a finite mode set is admissible.**  For the
gauge-fixed lattice truncation of quantum gravity there is no smallness, band or decay
assumption: the vielbein self-interaction and the scalaron coupling may be arbitrary
Hermitian matrices. -/
def ofFintype (sig : ι → ℝ) (one_le_sig : ∀ a, 1 ≤ sig a) (A B : ι → ι → ℂ)
    (A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b))
    (B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b)) : QgModeData ι :=
  ofBounds sig one_le_sig A B (fun _ => Finset.univ) (fun _ _ => by simp)
    (fun a b hb => absurd (Finset.mem_univ b) hb) (fun a b hb => absurd (Finset.mem_univ b) hb)
    A_herm B_herm (finKap sig A B) (Fintype.card ι : ℝ) (finKap_nonneg sig A B)
    (by positivity) (fun _ => by simp [Finset.card_univ])
    (fun a b => by
      have h := le_finKap sig A B a b
      have h1 : (1 : ℝ) ≤ min (sig a) (sig b) := le_min (one_le_sig a) (one_le_sig b)
      have h2 : ‖A a b‖ ≤ finKap sig A B := by
        have := abs_nonneg (sig a - sig b); have := norm_nonneg (B a b); linarith
      nlinarith [finKap_nonneg sig A B])
    (fun a b => by
      have h := le_finKap sig A B a b
      have := abs_nonneg (sig a - sig b); have := norm_nonneg (A a b); linarith)
    (fun a b _ => by
      have h := le_finKap sig A B a b
      have := norm_nonneg (A a b); have := norm_nonneg (B a b); linarith)

omit [DecidableEq ι] in
@[simp] theorem ofFintype_sig (sig : ι → ℝ) (one_le_sig : ∀ a, 1 ≤ sig a) (A B : ι → ι → ℂ)
    (A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b))
    (B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b)) :
    (ofFintype sig one_le_sig A B A_herm B_herm).sig = sig := rfl

omit [DecidableEq ι] in
@[simp] theorem ofFintype_A (sig : ι → ℝ) (one_le_sig : ∀ a, 1 ≤ sig a) (A B : ι → ι → ℂ)
    (A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b))
    (B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b)) :
    (ofFintype sig one_le_sig A B A_herm B_herm).A = A := rfl

omit [DecidableEq ι] in
@[simp] theorem ofFintype_B (sig : ι → ℝ) (one_le_sig : ∀ a, 1 ≤ sig a) (A B : ι → ι → ℂ)
    (A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b))
    (B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b)) :
    (ofFintype sig one_le_sig A B A_herm B_herm).B = B := rfl

end Fintype

/-! ## 3. The three-dimensional gauge-fixed vielbein lattice -/

section Lattice

variable (L : ℕ) [NeZero L]

/-- The sites of the periodic three-dimensional spatial lattice with `L` sites per
direction. -/
abbrev Site := Fin 3 → ZMod L

/-- The vielbein modes: a site together with a spatial index `μ` and an internal index `a`,
that is, the nine gauge-fixed components `e_μ^a` at each site. -/
abbrev VMode := Site L × Fin 3 × Fin 3

/-- The unit shift of a site in the direction `mu` (periodic boundary conditions). -/
def shift (mu : Fin 3) (s : Site L) : Site L := Function.update s mu (s mu + 1)

/-- The discrete torsion `∂_μ e_ν^a − ∂_ν e_μ^a` at the site `s`, as a linear form on the
vielbein modes. -/
def torsionForm (s : Site L) (mu nu i : Fin 3) : VMode L → ℂ := fun x =>
  ((if x = (shift L mu s, nu, i) then 1 else 0) - (if x = (s, nu, i) then 1 else 0))
    - ((if x = (shift L nu s, mu, i) then 1 else 0) - (if x = (s, mu, i) then 1 else 0))

/-- **The complete vielbein self-interaction** of the 3D gauge-fixed gravity Hamiltonian in
the mode basis: the Gram matrix `Σ_m v_m v_m^*` of all discrete torsion terms, which is the
mode matrix of the torsion potential `½ Σ_m T_m²`. -/
def torsionGram (x y : VMode L) : ℂ :=
  ∑ s : Site L, ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
    (starRingEnd ℂ) (torsionForm L s mu nu i x) * torsionForm L s mu nu i y

theorem torsionGram_herm (x y : VMode L) :
    torsionGram L y x = (starRingEnd ℂ) (torsionGram L x y) := by
  simp only [torsionGram, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun mu _ =>
    Finset.sum_congr rfl fun nu _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The trace of the vielbein perturbation, the combination the scalaron couples to. -/
def traceForm (x : VMode L) : ℝ := if x.2.1 = x.2.2 then 1 else 0

/-- **The scalaron–vielbein coupling** with coupling constant `g`: the scalaron field `φ`
multiplied by the trace of the vielbein. -/
def scalaronCoupling (g : ℝ) (x y : VMode L) : ℂ :=
  ((g * traceForm L x * traceForm L y : ℝ) : ℂ)

omit [NeZero L] in
theorem scalaronCoupling_herm (g : ℝ) (x y : VMode L) :
    scalaronCoupling L g y x = (starRingEnd ℂ) (scalaronCoupling L g x y) := by
  simp only [scalaronCoupling, Complex.conj_ofReal]
  norm_cast
  ring

/-- **The mode data of the 3D gauge-fixed vielbein lattice model**: the vielbein energies
`sig`, the full torsion self-interaction and the scalaron–vielbein coupling.  No smallness
assumption is imposed on the coupling constant `g` or on the energies. -/
def qgLatticeModes (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) :
    QgModeData (VMode L) :=
  ofFintype sig hsig (torsionGram L) (scalaronCoupling L g) (torsionGram_herm L)
    (scalaronCoupling_herm L g)







end Lattice

end

end BookProof.QgVielbeinModeInstance


