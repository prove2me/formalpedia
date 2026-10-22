-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_InterleavedFiltrations_Defs
-- name    : LPCA_Solutions_LPCA_InterleavedFiltrations_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:22:15.428641+00:00
-- url     : https://prove2.me/theorems/71718278-5240-4388-9850-fddbeda6ffea
-- title:
--   Shifted sublevel inclusions at the finite-face discrepancy
-- statement:
--   This bundle supplies shifted sublevel inclusions at the finite-face discrepancy. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Supremum distance on the actual finite face family. Including zero makes the same definition valid for the void complex, with distance zero.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_InterleavedFiltrations.lean, selected declarations in lines 12–52; source SHA-256 89bafb162a6593c6826d02f5afdd798b89f182af4570e2260b6f1cc533479a57; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]

/-- Supremum distance on the actual finite face family. Including zero
makes the same definition valid for the void complex, with distance zero. -/
noncomputable def filtrationDiscrepancy (K : Complex V) (f g : Finset V → ℝ) : ℝ :=
  (insert 0 (K.faces.image (fun F => |f F - g F|))).sup' (Finset.insert_nonempty _ _) id

theorem filtrationDiscrepancy_nonneg (K : Complex V) (f g : Finset V → ℝ) :
    0 ≤ filtrationDiscrepancy K f g := by
  exact Finset.le_sup' id (Finset.mem_insert_self 0 _)

theorem abs_face_difference_le_discrepancy (K : Complex V) (f g : Finset V → ℝ)
    (F : Finset V) (hF : F ∈ K.faces) :
    |f F - g F| ≤ filtrationDiscrepancy K f g := by
  have hm : |f F - g F| ∈ insert (0 : ℝ) (K.faces.image (fun G => |f G - g G|)) :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨F, hF, rfl⟩)
  exact Finset.le_sup' id hm





theorem level_shift_subset_of_abs_le (K : Complex V) (f g : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (hg : FiltrationMonotone K g)
    (ε : ℝ) (hfg : ∀ F ∈ K.faces, |f F - g F| ≤ ε) (t : ℝ) :
    (level K f hf t).faces ⊆ (level K g hg (t + ε)).faces := by
  intro F hF
  obtain ⟨hFK, hFt⟩ := Finset.mem_filter.mp hF
  refine Finset.mem_filter.mpr ⟨hFK, ?_⟩
  have hdiff : g F - f F ≤ |f F - g F| := by
    simpa only [abs_sub_comm] using le_abs_self (g F - f F)
  have hb := hfg F hFK
  linarith







end LPCA


