-- Prove2me | Definitions.Def_ChapterScalaronOuterFockFL
-- name    : ChapterScalaronOuterFockFL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T02:55:15.870469+00:00
-- url     : https://prove2.me/theorems/af31003d-25b0-4780-862c-60fac2419983
-- title:
--   The Lean 4 theorem `norm_shift_sq` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ScalaronOuterFockFL`, source chapter `BookProof/ChapterScalaronOuterFockFL.lean`): The scalaron–vielbein quantum-gravity Hamiltonian on the outer Fock space
--
--   This module assembles the Faris–Lavine proof of essential self-adjointness of the full quantum-gravity Hamiltonian in the representation the *scalaron* forces on us: the vielbein sector in the occupation-number (mode) representation, the scalaron in position representation carrying the **full exponential** Einstein-frame potential, with no Taylor expansion and no relative-boundedness hypothesis on the wall.
--
--   The Hilbert space is the outer Fock space of the vielbein modes with values in the scalaron line,
--
--   `𝓕 = ℓ²(ι ; L²(ℝ_φ))`,
--
--   `ι` the set of occupation-number configurations of the vielbein modes. The comparison operator is the `ℓ²`-lift of the Friedrichs extension of the positive one-particle operator
--
--   `N_a = −d²/dφ² + φ²/4 + V(φ) + σ_a`
--
--   on the fibre `a`, `σ_a ≥ 1` the vielbein energy of the configuration.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronOuterFockFL.lean

import Mathlib
-- Import list canonicalized 2026-10-23 (server-side empty-import failure,
-- §2.68): `Mathlib` moved to the front; otherwise the set is unchanged.
import Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_core_le_dom
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
import Theorems.Thm_BookProof_ScalaronFiberFL_norm_xCc_sq_le
import Theorems.Thm_BookProof_ScalaronFiberFL_cc_integrable
import Theorems.Thm_BookProof_WallEsaSemibounded_ccEquiv_norm_sq
import Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_comparison_core
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_ham_esa
import Theorems.Thm_BookProof_ScalaronFiberFL_isGraphCore_of_esa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
-- QgOuterFockCoreFL stubs are selective: the *published* Def bundle (mirror
-- olean) already declares ext_core, so that stub redeclares; but it predates
-- commForm_congr / quadForm_congr / ext_essentiallySelfAdjointOn, so those
-- stubs are required.
import Theorems.Thm_BookProof_QgOuterFockCoreFL_commForm_congr
import Theorems.Thm_BookProof_QgOuterFockCoreFL_quadForm_congr
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_essentiallySelfAdjointOn
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
import Theorems.Thm_BookProof_ScalaronFiberFL_norm_sq_le_quadForm
import Theorems.Thm_BookProof_ScalaronFiberFL_norm_derivL2_sq_le
import Theorems.Thm_BookProof_ScalaronFiberFL_ham_x_comm
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
import Theorems.Thm_BookProof_ScalaronFiberFL_hamS_apply


/-!
# The scalaron–vielbein quantum-gravity Hamiltonian on the outer Fock space

This module assembles the Faris–Lavine proof of essential self-adjointness of the full
quantum-gravity Hamiltonian in the representation the *scalaron* forces on us: the vielbein
sector in the occupation-number (mode) representation, the scalaron in position
representation carrying the **full exponential** Einstein-frame potential, with no Taylor
expansion and no relative-boundedness hypothesis on the wall.

The Hilbert space is the outer Fock space of the vielbein modes with values in the scalaron
line,

`𝓕 = ℓ²(ι ; L²(ℝ_φ))`,

`ι` the set of occupation-number configurations of the vielbein modes.  The comparison
operator is the `ℓ²`-lift of the Friedrichs extension of the positive one-particle operator

`N_a = −d²/dφ² + φ²/4 + V(φ) + σ_a`

on the fibre `a`, `σ_a ≥ 1` the vielbein energy of the configuration.

Everything is `sorry`-free and `axiom`-free.
-/

open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL
open BookProof.WallEsaSemibounded

namespace BookProof.ScalaronFiberFL
open BookProof.ScalaronWallEsa
open BookProof.StrichartzWave

/-- `ham_eq_toLp` — the fibre Hamiltonian on the core agrees with the `L²` image of the
Schwartz-space form.  The published `Def_ChapterScalaronFiberFL` text predates this
lemma, so it is restated here for the consumer. -/
theorem ham_eq_toLp (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) :
    W.ham s (ccEquiv ℝ f) = (hamS W s f).toLp 2 (volume : Measure ℝ) := by
  have hincl : Submodule.inclusion (ccDomain_le_schwartzDomain (E := ℝ)) (ccEquiv ℝ f)
      = schwartzEquiv ℝ (f : 𝓢(ℝ, ℂ)) := Subtype.ext rfl
  have hkin : kinCcR (ccEquiv ℝ f) = (kinOpR (f : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ) := by
    simp only [kinCcR, LinearMap.coe_comp, Function.comp_apply, hincl, opL2_apply]
  have hpot : opCc (W.pot s) (W.pot_smooth s) (ccEquiv ℝ f)
      = (mulCc (W.pot s) (W.pot_smooth s) f).toLp 2 (volume : Measure ℝ) := opCc_apply _ _ _
  change (kinCcR + opCc (W.pot s) (W.pot_smooth s)) (ccEquiv ℝ f) = _
  rw [LinearMap.add_apply, hkin, hpot, hamS]
  exact (map_add (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) _ _).symm

end BookProof.ScalaronFiberFL

namespace BookProof.ScalaronOuterFockFL

noncomputable section

/-! ## 0. Generic estimates for a positive symmetric operator and its shift -/

section Shift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- The shift identity `‖Nu + u‖² = ‖Nu‖² + 2q(u) + ‖u‖²`. -/
theorem norm_shift_sq (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N) (u : D) :
    ‖N u + (u : F)‖ ^ 2 = ‖N u‖ ^ 2 + 2 * quadForm N u + ‖(u : F)‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (N u) ((u : F))
  have hq : (inner ℂ (N u) (u : F) : ℂ).re = quadForm N u := by
    rw [quadForm, hsym u u]
  rw [h]
  simp only [RCLike.re_to_complex] at *
  rw [hq]

/-- The graph norm of the shift dominates the norm of the image. -/
theorem norm_op_le_shift (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N)
    (hpos : ∀ x : D, 0 ≤ quadForm N x) (u : D) : ‖N u‖ ≤ ‖N u + (u : F)‖ := by
  have h := norm_shift_sq N hsym u
  have h1 := hpos u
  have h2 : (0 : ℝ) ≤ ‖(u : F)‖ ^ 2 := by positivity
  nlinarith [norm_nonneg (N u), norm_nonneg (N u + (u : F))]

/-- The quadratic form is dominated by the graph norm of the shift. -/
theorem two_quadForm_le_shift_sq (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N) (u : D) :
    2 * quadForm N u ≤ ‖N u + (u : F)‖ ^ 2 := by
  have h := norm_shift_sq N hsym u
  nlinarith [norm_nonneg (N u), sq_nonneg ‖N u‖, sq_nonneg ‖(u : F)‖]

theorem quadForm_le_mul_norm (N : D →ₗ[ℂ] F) (u : D) :
    quadForm N u ≤ ‖(u : F)‖ * ‖N u‖ := by
  calc quadForm N u ≤ ‖(inner ℂ (u : F) (N u) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ‖(u : F)‖ * ‖N u‖ := norm_inner_le_norm _ _

/-- A lower form bound `σ‖u‖² ≤ q(u)` upgrades to the operator bound `σ‖u‖ ≤ ‖(N+1)u‖`. -/
theorem mul_norm_le_shift (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N)
    (hpos : ∀ x : D, 0 ≤ quadForm N x) {sg : ℝ} (u : D)
    (h : sg * ‖(u : F)‖ ^ 2 ≤ quadForm N u) : sg * ‖(u : F)‖ ≤ ‖N u + (u : F)‖ := by
  have hcs := quadForm_le_mul_norm N u
  have hop := norm_op_le_shift N hsym hpos u
  rcases eq_or_lt_of_le (norm_nonneg (u : F)) with h0 | h0
  · have hz : sg * ‖(u : F)‖ = 0 := by rw [← h0]; ring
    rw [hz]
    exact norm_nonneg _
  · have hle : sg * ‖(u : F)‖ ≤ ‖N u‖ := by
      have hm : sg * ‖(u : F)‖ * ‖(u : F)‖ ≤ ‖N u‖ * ‖(u : F)‖ := by nlinarith
      exact le_of_mul_le_mul_right hm h0
    linarith

end Shift

/-! ## 0b. The fibre estimates, in terms of core vectors -/

section Fibre

variable (W : WallPot) (s : ℝ)

theorem le_pot (x : ℝ) : s ≤ W.pot s x := by
  have h1 := W.nonneg x
  have h2 : (0 : ℝ) ≤ x ^ 2 / 4 := by positivity
  simp only [WallPot.pot]
  linarith

/-- Splitting off the vielbein energy: `h_s = h_0 + s`. -/
theorem ham_eq_ham_zero_add (u : ccDomain ℝ) :
    W.ham s u = W.ham 0 u + (s : ℂ) • (u : L2R) := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [ham_eq_toLp, ham_eq_toLp, ccEquiv_coe]
  have hS : hamS W s f = hamS W 0 f + (s : ℂ) • (f : 𝓢(ℝ, ℂ)) := by
    refine SchwartzMap.ext fun x => ?_
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, hamS_apply, smul_eq_mul,
      WallPot.pot]
    push_cast
    ring
  rw [hS]
  have h1 := map_add (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) (hamS W 0 f)
    ((s : ℂ) • (f : 𝓢(ℝ, ℂ)))
  have h2 := map_smul (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) ((s : ℂ)) (f : 𝓢(ℝ, ℂ))
  rw [show ((hamS W 0 f + (s : ℂ) • (f : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ))
      = toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (hamS W 0 f + (s : ℂ) • (f : 𝓢(ℝ, ℂ))) from rfl,
    h1, h2]
  rfl

/-- The vielbein energy is a lower bound for the fibre quadratic form. -/
theorem sig_mul_norm_sq_le_quadForm (u : ccDomain ℝ) :
    s * ‖(u : L2R)‖ ^ 2 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [ccEquiv_norm_sq, ham_quadForm]
  have hmono : (∫ x, s * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2) ≤ ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
    refine integral_mono (cc_integrable f (W := fun _ => s) continuous_const)
      (cc_integrable f (W.pot_smooth s).continuous) fun x => ?_
    have h1 := le_pot W s x
    nlinarith [sq_nonneg ‖(f : 𝓢(ℝ, ℂ)) x‖]
  have hsplit : (∫ x, s * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2) = s * ∫ x, ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 :=
    integral_const_mul _ _
  have h1 := integral_deriv_nonneg f
  linarith

theorem norm_sq_le_quadForm_cc (hs : 1 ≤ s) (u : ccDomain ℝ) :
    ‖(u : L2R)‖ ^ 2 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  exact norm_sq_le_quadForm W s hs f

theorem norm_xCc_sq_le_cc (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖xCc u‖ ^ 2 ≤ 4 * quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  exact norm_xCc_sq_le W s hs f

/-- The derivative of a core vector. -/
def dCc (u : ccDomain ℝ) : L2R := derivL2 ((ccEquiv ℝ).symm u)

theorem dCc_eq (f : ccSchwartz ℝ) : dCc (ccEquiv ℝ f) = derivL2 f := by
  rw [dCc, LinearEquiv.symm_apply_apply]

theorem norm_dCc_sq_le_cc (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖dCc u‖ ^ 2 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [dCc_eq]
  exact norm_derivL2_sq_le W s hs f

/-- The commutator identity `[h_s, φ] = -2 d/dφ`, for core vectors. -/
theorem ham_x_comm_cc (u v : ccDomain ℝ) :
    (starRingEnd ℂ) (inner ℂ (xCc v) (W.ham s u) : ℂ) - (inner ℂ (xCc u) (W.ham s v) : ℂ)
      = -2 * (inner ℂ (u : L2R) (dCc v) : ℂ) := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  obtain ⟨g, rfl⟩ := (ccEquiv ℝ).surjective v
  rw [dCc_eq]
  exact ham_x_comm W s f g

/-! The three relative bounds against the shift `h_s + 1`, uniform in `s`. -/

theorem norm_ham_le_shift (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖W.ham s u‖ ≤ ‖W.ham s u + (u : L2R)‖ :=
  norm_op_le_shift _ (W.ham_symmetricOn s) (ham_quadForm_nonneg W s hs) u

theorem two_quadForm_le_shift (u : ccDomain ℝ) :
    2 * quadForm (W.ham s) u ≤ ‖W.ham s u + (u : L2R)‖ ^ 2 :=
  two_quadForm_le_shift_sq _ (W.ham_symmetricOn s) u

theorem sig_norm_le_shift (hs : 0 ≤ s) (u : ccDomain ℝ) :
    s * ‖(u : L2R)‖ ≤ ‖W.ham s u + (u : L2R)‖ :=
  mul_norm_le_shift _ (W.ham_symmetricOn s) (ham_quadForm_nonneg W s hs) u
    (sig_mul_norm_sq_le_quadForm W s u)

theorem norm_xCc_sq_le_shift (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖xCc u‖ ^ 2 ≤ 2 * ‖W.ham s u + (u : L2R)‖ ^ 2 := by
  have h1 := norm_xCc_sq_le_cc W s hs u
  have h2 := two_quadForm_le_shift W s u
  linarith

end Fibre

variable {ι : Type*}

/-- The outer Fock space of the vielbein modes with values in the scalaron line. -/
abbrev Sec (ι : Type*) := lp (fun _ : ι => L2R) 2

/-- **The mode data of the gauge-fixed quantum-gravity Hamiltonian.**

`sig` is the vielbein energy of an occupation configuration, `A` the (Hermitian) mode matrix
of all vielbein self-interactions — it acts as a scalar on the scalaron fibre — and `B` the
(Hermitian) mode matrix of the scalaron–vielbein coupling, which acts by multiplication by
the scalaron field `φ`.  The band structure `nbr` makes every row and column finite, and the
five bounds are the Faris–Lavine input: the vielbein matrix is allowed to grow like the mode
energy (as the second quantization of a quadratic Hamiltonian does), the coupling matrix is
required to be Schur-bounded. -/
structure QgModeData (ι : Type*) where
  /-- The vielbein energy of a mode configuration. -/
  sig : ι → ℝ
  /-- The energies are at least one. -/
  one_le_sig : ∀ a, 1 ≤ sig a
  /-- The vielbein self-interaction matrix. -/
  A : ι → ι → ℂ
  /-- The scalaron–vielbein coupling matrix. -/
  B : ι → ι → ℂ
  /-- The band. -/
  nbr : ι → Finset ι
  /-- The band is symmetric. -/
  mem_nbr_comm : ∀ a b, b ∈ nbr a ↔ a ∈ nbr b
  /-- `A` vanishes outside the band. -/
  A_off : ∀ a b, b ∉ nbr a → A a b = 0
  /-- `B` vanishes outside the band. -/
  B_off : ∀ a b, b ∉ nbr a → B a b = 0
  /-- `A` is Hermitian. -/
  A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b)
  /-- `B` is Hermitian. -/
  B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b)
  /-- The uniform bound. -/
  K : ℝ
  /-- The uniform bound is non-negative. -/
  K_nonneg : 0 ≤ K
  /-- Row bound for `A`, weighted by the mode energy. -/
  A_rel_row : ∀ a, ∑ b ∈ nbr a, ‖A a b‖ / sig b ≤ K
  /-- Column bound for `A`. -/
  A_rel_col : ∀ a, ∑ b ∈ nbr a, ‖A a b‖ ≤ K * sig a
  /-- Commutator bound for `A`. -/
  A_comm : ∀ a, ∑ b ∈ nbr a, |sig a - sig b| * ‖A a b‖ ≤ K * sig a
  /-- Schur bound for the coupling `B`. -/
  B_rel : ∀ a, ∑ b ∈ nbr a, ‖B a b‖ ≤ K
  /-- Commutator bound for the coupling `B`. -/
  B_comm : ∀ a, ∑ b ∈ nbr a, |sig a - sig b| * ‖B a b‖ ≤ K

namespace QgModeData

variable (Q : QgModeData ι)

theorem sig_nonneg (a : ι) : (0 : ℝ) ≤ Q.sig a := le_trans zero_le_one (Q.one_le_sig a)

theorem sig_pos (a : ι) : (0 : ℝ) < Q.sig a := lt_of_lt_of_le zero_lt_one (Q.one_le_sig a)

end QgModeData

variable (W : WallPot) (Q : QgModeData ι)

/-- The fibre comparison operator: the Friedrichs extension of
`−d²/dφ² + φ²/4 + V(φ) + σ_a`. -/
def fibCompar (a : ι) : Comparison L2R := W.comparison (Q.sig a) (Q.sig_nonneg a)

/-- **The comparison operator on the outer Fock space**: the `ℓ²`-lift of the fibre
Friedrichs extensions. -/
def secN : Comparison (Sec ι) := dsComparison (fibCompar W Q)

/-- The algebraic direct sum of the compactly supported smooth cores. -/
def secCore : Submodule ℂ (Sec ι) := dsCore (fun _ : ι => ccDomain ℝ)

/-- The fibrewise Hamiltonian on the core. -/
def secDiag : secCore (ι := ι) →ₗ[ℂ] Sec ι := dsOp (fun a => W.ham (Q.sig a))

theorem secCore_le_dom : secCore (ι := ι) ≤ (secN W Q).dom := by
  rintro x ⟨hfin, hmem⟩
  refine ⟨fun a => W.core_le_dom (Q.sig a) (Q.sig_nonneg a) (hmem a), ?_⟩
  refine memLp_of_finite_support (Set.Finite.subset hfin fun a ha => ?_)
  simp only [Set.mem_setOf_eq] at ha ⊢
  intro h0
  refine ha ?_
  rw [h0]
  simp only [opTot, dif_pos (zero_mem _)]
  show (fibCompar W Q a).op 0 = 0
  exact map_zero _

theorem secN_core (p : secCore (ι := ι)) :
    (secN W Q).op ⟨(p : Sec ι), secCore_le_dom W Q p.2⟩ = secDiag W Q p := by
  refine lp.ext (funext fun a => ?_)
  have hcc : (p : ∀ _ : ι, L2R) a ∈ ccDomain ℝ := p.2.2 a
  have hd : (p : ∀ _ : ι, L2R) a ∈ (fibCompar W Q a).dom :=
    W.core_le_dom (Q.sig a) (Q.sig_nonneg a) hcc
  change opTot (fibCompar W Q a).op ((p : Sec ι) a) = _
  rw [opTot_of_mem _ hd]
  exact W.comparison_core (Q.sig a) (Q.sig_nonneg a) ⟨_, hcc⟩ hd

/-- **The algebraic direct sum of the compactly supported smooth cores is a graph core** for
the lifted Friedrichs extension.  Fibrewise essential self-adjointness of the scalaron
operator with the full exponential wall glues to the direct sum, and essential
self-adjointness on a subspace is exactly what makes it a graph core. -/
theorem secN_isGraphCore : IsGraphCore (secN W Q) (secCore (ι := ι)) :=
  isGraphCore_of_esa (secN W Q) (secCore (ι := ι)) (secCore_le_dom W Q) (secDiag W Q)
    (secN_core W Q)
    (dsOp_essentiallySelfAdjointOn _ fun a => W.ham_esa (Q.sig a) (Q.sig_nonneg a))

/-! ## 2. The mode operators -/

/-- The fibre of a core vector, as an element of the compactly supported smooth core. -/
def fibOf (x : secCore (ι := ι)) (a : ι) : ccDomain ℝ := ⟨(x : Sec ι) a, x.2.2 a⟩

@[simp] theorem fibOf_coe (x : secCore (ι := ι)) (a : ι) :
    ((fibOf x a : ccDomain ℝ) : L2R) = (x : Sec ι) a := rfl

theorem fibOf_eq_zero {x : secCore (ι := ι)} {a : ι} (h : (x : Sec ι) a = 0) :
    fibOf x a = 0 := Subtype.ext h

theorem fibOf_add (x y : secCore (ι := ι)) (a : ι) :
    fibOf (x + y) a = fibOf x a + fibOf y a := by
  refine Subtype.ext ?_
  change ((x : Sec ι) + (y : Sec ι)) a = ((fibOf x a : L2R) + (fibOf y a : L2R))
  rw [lp.coeFn_add]
  rfl

theorem fibOf_smul (c : ℂ) (x : secCore (ι := ι)) (a : ι) :
    fibOf (c • x) a = c • fibOf x a := by
  refine Subtype.ext ?_
  change (c • (x : Sec ι)) a = c • ((fibOf x a : L2R))
  rw [lp.coeFn_smul]
  rfl

/-- **A mode operator**: a banded mode matrix `M` acting on the vielbein modes, combined
with a fibre operator `Φ` acting on the scalaron line. -/
def modeOp (Φ : ccDomain ℝ →ₗ[ℂ] L2R) (M : ι → ι → ℂ) : secCore (ι := ι) →ₗ[ℂ] Sec ι where
  toFun x := ⟨fun a => ∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b), by
    refine memLp_of_finite_support (Set.Finite.subset
      (Set.Finite.biUnion x.2.1 (fun b _ => (Q.nbr b).finite_toSet)) ?_)
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    by_contra hcon
    refine ha (Finset.sum_eq_zero fun b hb => ?_)
    have hb' : a ∈ Q.nbr b := (Q.mem_nbr_comm a b).mp hb
    have hxb : (x : Sec ι) b = 0 := by
      by_contra hne
      exact hcon (Set.mem_biUnion hne hb')
    rw [fibOf_eq_zero hxb, map_zero, smul_zero]⟩
  map_add' x y := by
    refine lp.ext (funext fun a => ?_)
    simp only [lp.coeFn_add, Pi.add_apply]
    change (∑ b ∈ Q.nbr a, M a b • Φ (fibOf (x + y) b))
      = (∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b)) + ∑ b ∈ Q.nbr a, M a b • Φ (fibOf y b)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [fibOf_add, map_add, smul_add]
  map_smul' c x := by
    refine lp.ext (funext fun a => ?_)
    simp only [RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply]
    change (∑ b ∈ Q.nbr a, M a b • Φ (fibOf (c • x) b))
      = c • ∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [fibOf_smul, map_smul, smul_comm]

@[simp] theorem modeOp_apply (Φ : ccDomain ℝ →ₗ[ℂ] L2R) (M : ι → ι → ℂ)
    (x : secCore (ι := ι)) (a : ι) :
    (modeOp Q Φ M x : Sec ι) a = ∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b) := rfl

/-- The vielbein self-interaction term: all quadratic mode couplings of the gauge-fixed
gravity Hamiltonian, acting as a scalar on the scalaron fibre. -/
def secA : secCore (ι := ι) →ₗ[ℂ] Sec ι := modeOp Q ((ccDomain ℝ).subtype) Q.A

/-- The scalaron–vielbein coupling term: the mode matrix `B` acting together with
multiplication by the scalaron field `φ`. -/
def secB : secCore (ι := ι) →ₗ[ℂ] Sec ι := modeOp Q xCc Q.B

/-- **The full gauge-fixed quantum-gravity Hamiltonian on the outer Fock space**: the
fibrewise scalaron Hamiltonian with the full exponential wall, the vielbein
self-interaction and the scalaron–vielbein coupling. -/
def secHam : secCore (ι := ι) →ₗ[ℂ] Sec ι := secDiag W Q + secA Q + secB Q

@[simp] theorem secDiag_apply (x : secCore (ι := ι)) (a : ι) :
    (secDiag W Q x : Sec ι) a = W.ham (Q.sig a) (fibOf x a) := rfl

theorem secHam_apply (x : secCore (ι := ι)) (a : ι) :
    (secHam W Q x : Sec ι) a = W.ham (Q.sig a) (fibOf x a)
      + (∑ b ∈ Q.nbr a, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R))
      + ∑ b ∈ Q.nbr a, Q.B a b • xCc (fibOf x b) := by
  change ((secDiag W Q x + secA Q x + secB Q x : Sec ι)) a = _
  rw [lp.coeFn_add, lp.coeFn_add]
  rfl

/-! ### Finite bands -/

/-- Every core vector has a finite band: a finite set outside of which the vector and all
its neighbours vanish. -/
theorem exists_band (x : secCore (ι := ι)) :
    ∃ P : Finset ι, (∀ a, a ∉ P → (x : Sec ι) a = 0) ∧
      (∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) := by
  classical
  refine ⟨x.2.1.toFinset ∪ x.2.1.toFinset.biUnion Q.nbr, ?_, ?_⟩
  · intro a ha
    by_contra hne
    exact ha (Finset.mem_union_left _ (Set.Finite.mem_toFinset _ |>.mpr hne))
  · intro a ha b hb
    by_contra hne
    refine ha (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, ?_, ?_⟩))
    · exact (Set.Finite.mem_toFinset _).mpr hne
    · exact (Q.mem_nbr_comm a b).mp hb

/-- A sum over the band and a sum over a finite set agree as soon as the summand vanishes
outside each of them. -/
theorem sum_band_eq_sum {M : Type*} [AddCommMonoid M] (N P : Finset ι) (g : ι → M)
    (h1 : ∀ b, b ∉ N → g b = 0) (h2 : ∀ b, b ∉ P → g b = 0) :
    ∑ b ∈ N, g b = ∑ b ∈ P, g b := by
  classical
  have hN : ∑ b ∈ N ∩ P, g b = ∑ b ∈ N, g b :=
    Finset.sum_subset Finset.inter_subset_left fun b hb hnb =>
      h2 b fun hbP => hnb (Finset.mem_inter.mpr ⟨hb, hbP⟩)
  have hP : ∑ b ∈ N ∩ P, g b = ∑ b ∈ P, g b :=
    Finset.sum_subset Finset.inter_subset_right fun b hb hnb =>
      h1 b fun hbN => hnb (Finset.mem_inter.mpr ⟨hbN, hb⟩)
  rw [← hN, hP]

/-! ### Inner products and norms as finite sums -/

theorem inner_eq_sum_of_supp (P : Finset ι) (y z : Sec ι)
    (hy : ∀ a, a ∉ P → (y : ∀ _ : ι, L2R) a = 0) :
    (inner ℂ y z : ℂ) = ∑ a ∈ P, (inner ℂ ((y : ∀ _ : ι, L2R) a) ((z : ∀ _ : ι, L2R) a) : ℂ) := by
  rw [lp.inner_eq_tsum]
  exact tsum_eq_sum fun a ha => by rw [hy a ha, inner_zero_left]

theorem norm_sq_eq_sum_of_supp (P : Finset ι) (y : Sec ι)
    (hy : ∀ a, a ∉ P → (y : ∀ _ : ι, L2R) a = 0) :
    ‖y‖ ^ 2 = ∑ a ∈ P, ‖(y : ∀ _ : ι, L2R) a‖ ^ 2 := by
  have h2 : (inner ℂ y y : ℂ).re = ‖y‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) y
  rw [← h2, inner_eq_sum_of_supp P y y hy, Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((y : ∀ _ : ι, L2R) a)

/-! ## 3. The relative bound -/

theorem le_of_sq_le_sq_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by nlinarith

/-- A sum over an arbitrary finite set is at most the sum over the band, for a non-negative
summand supported in the band. -/
theorem sum_le_sum_band (P N : Finset ι) (g : ι → ℝ) (hg : ∀ b, 0 ≤ g b)
    (h0 : ∀ b, b ∉ N → g b = 0) : ∑ b ∈ P, g b ≤ ∑ b ∈ N, g b := by
  classical
  have h1 : ∑ b ∈ P ∩ N, g b = ∑ b ∈ P, g b :=
    Finset.sum_subset Finset.inter_subset_left fun b hb hnb =>
      h0 b fun hbN => hnb (Finset.mem_inter.mpr ⟨hb, hbN⟩)
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun b _ _ => hg b

/-- **The Schur test**, in the weighted form the mode matrices satisfy. -/
theorem schur_sq_le (P : Finset ι) (c : ι → ι → ℝ) (v w : ι → ℝ) (K : ℝ)
    (hc : ∀ a b, 0 ≤ c a b) (hw : ∀ b, 0 < w b) (hK : 0 ≤ K)
    (hrow : ∀ a, ∑ b ∈ P, c a b / w b ≤ K)
    (hcol : ∀ b, ∑ a ∈ P, c a b ≤ K * w b) :
    ∑ a ∈ P, (∑ b ∈ P, c a b * v b) ^ 2 ≤ K ^ 2 * ∑ b ∈ P, (w b * v b) ^ 2 := by
  have step : ∀ a ∈ P, (∑ b ∈ P, c a b * v b) ^ 2
      ≤ K * ∑ b ∈ P, c a b * (w b * v b ^ 2) := by
    intro a _
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul P
      (r := fun b => c a b * v b) (f := fun b => c a b / w b)
      (g := fun b => c a b * (w b * v b ^ 2))
      (fun i _ => div_nonneg (hc a i) (hw i).le)
      (fun i _ => mul_nonneg (hc a i) (mul_nonneg (hw i).le (sq_nonneg _)))
      (fun i _ => by
        have hwi := (hw i).ne'
        field_simp)
    have hg0 : 0 ≤ ∑ b ∈ P, c a b * (w b * v b ^ 2) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hc a i) (mul_nonneg (hw i).le (sq_nonneg _))
    exact hCS.trans (mul_le_mul_of_nonneg_right (hrow a) hg0)
  calc ∑ a ∈ P, (∑ b ∈ P, c a b * v b) ^ 2
      ≤ ∑ a ∈ P, K * ∑ b ∈ P, c a b * (w b * v b ^ 2) := Finset.sum_le_sum step
    _ = K * ∑ b ∈ P, (∑ a ∈ P, c a b) * (w b * v b ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
    _ ≤ K * ∑ b ∈ P, (K * w b) * (w b * v b ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) hK
        exact mul_le_mul_of_nonneg_right (hcol b) (mul_nonneg (hw b).le (sq_nonneg _))
    _ = K ^ 2 * ∑ b ∈ P, (w b * v b) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

/-- The Schur test for a banded mode matrix acting on a family of scalaron states. -/
theorem sum_norm_sq_mode_le (P : Finset ι) (M : ι → ι → ℂ) (y : ι → L2R) (w : ι → ℝ) (K : ℝ)
    (hw : ∀ b, 0 < w b) (hK : 0 ≤ K)
    (hrow : ∀ a, ∑ b ∈ P, ‖M a b‖ / w b ≤ K)
    (hcol : ∀ b, ∑ a ∈ P, ‖M a b‖ ≤ K * w b) :
    ∑ a ∈ P, ‖∑ b ∈ P, M a b • y b‖ ^ 2 ≤ K ^ 2 * ∑ b ∈ P, (w b * ‖y b‖) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun a _ => ?_)
    (schur_sq_le P (fun a b => ‖M a b‖) (fun b => ‖y b‖) w K
      (fun a b => norm_nonneg _) hw hK hrow hcol)
  have h1 : ‖∑ b ∈ P, M a b • y b‖ ≤ ∑ b ∈ P, ‖M a b‖ * ‖y b‖ := by
    calc ‖∑ b ∈ P, M a b • y b‖ ≤ ∑ b ∈ P, ‖M a b • y b‖ := norm_sum_le _ _
      _ = ∑ b ∈ P, ‖M a b‖ * ‖y b‖ := Finset.sum_congr rfl fun b _ => norm_smul _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-! ### The three pieces of the Hamiltonian against the shift -/

theorem shift_fib (x : secCore (ι := ι)) (a : ι) :
    ((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) a
      = W.ham (Q.sig a) (fibOf x a) + ((fibOf x a : ccDomain ℝ) : L2R) := by
  rw [lp.coeFn_add]
  rfl

theorem shift_supp {P : Finset ι} {x : secCore (ι := ι)}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) (a : ι) (ha : a ∉ P) :
    ((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) a = 0 := by
  rw [shift_fib, fibOf_eq_zero (hP1 a ha), map_zero]
  simp

theorem secDiag_supp {P : Finset ι} {x : secCore (ι := ι)}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) (a : ι) (ha : a ∉ P) :
    (secDiag W Q x : Sec ι) a = 0 := by
  rw [secDiag_apply, fibOf_eq_zero (hP1 a ha), map_zero]

theorem modeOp_supp {P : Finset ι} {x : secCore (ι := ι)} (Φ : ccDomain ℝ →ₗ[ℂ] L2R)
    (M : ι → ι → ℂ) (hP2 : ∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0)
    (a : ι) (ha : a ∉ P) : (modeOp Q Φ M x : Sec ι) a = 0 := by
  rw [modeOp_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [fibOf_eq_zero (hP2 a ha b hb), map_zero, smul_zero]

/-- On the band, the sum over the neighbours of `a` may be taken over the band. -/
theorem modeOp_eq_sum_band {P : Finset ι} {x : secCore (ι := ι)} (Φ : ccDomain ℝ →ₗ[ℂ] L2R)
    (M : ι → ι → ℂ) (hM : ∀ a b, b ∉ Q.nbr a → M a b = 0)
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) (a : ι) :
    (modeOp Q Φ M x : Sec ι) a = ∑ b ∈ P, M a b • Φ (fibOf x b) := by
  rw [modeOp_apply]
  refine sum_band_eq_sum _ _ _ (fun b hb => ?_) (fun b hb => ?_)
  · rw [hM a b hb, zero_smul]
  · rw [fibOf_eq_zero (hP1 b hb), map_zero, smul_zero]

theorem norm_secDiag_le (x : secCore (ι := ι)) :
    ‖secDiag W Q x‖ ≤ ‖secDiag W Q x + (x : Sec ι)‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  refine le_of_sq_le_sq_nonneg (norm_nonneg _) ?_
  rw [norm_sq_eq_sum_of_supp P _ (secDiag_supp W Q hP1),
    norm_sq_eq_sum_of_supp P _ (shift_supp W Q hP1)]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [shift_fib, secDiag_apply]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_ham_le_shift W (Q.sig a) (Q.sig_nonneg a) (fibOf x a)) 2

theorem norm_secA_le (x : secCore (ι := ι)) :
    ‖secA Q x‖ ≤ Q.K * ‖secDiag W Q x + (x : Sec ι)‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  have hKT : 0 ≤ Q.K * ‖secDiag W Q x + (x : Sec ι)‖ :=
    mul_nonneg Q.K_nonneg (norm_nonneg _)
  refine le_of_sq_le_sq_nonneg hKT ?_
  have hsupp : ∀ a, a ∉ P → (secA Q x : Sec ι) a = 0 :=
    modeOp_supp Q _ _ hP2
  rw [norm_sq_eq_sum_of_supp P _ hsupp]
  have hval : ∀ a, (secA Q x : Sec ι) a
      = ∑ b ∈ P, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) :=
    modeOp_eq_sum_band Q _ _ Q.A_off hP1
  have hrow : ∀ a, ∑ b ∈ P, ‖Q.A a b‖ / Q.sig b ≤ Q.K := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _
      (fun b => div_nonneg (norm_nonneg _) (Q.sig_nonneg b)) fun b hb => ?_) (Q.A_rel_row a)
    rw [Q.A_off a b hb, norm_zero, zero_div]
  have hcol : ∀ b, ∑ a ∈ P, ‖Q.A a b‖ ≤ Q.K * Q.sig b := by
    intro b
    refine le_trans (sum_le_sum_band P (Q.nbr b) _ (fun a => norm_nonneg _) fun a ha => ?_) ?_
    · rw [Q.A_off a b fun hba => ha ((Q.mem_nbr_comm b a).mpr hba), norm_zero]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (Q.A_rel_col b)
      rw [Q.A_herm b a]
      exact RCLike.norm_conj _
  have hschur := sum_norm_sq_mode_le P Q.A (fun b => ((fibOf x b : ccDomain ℝ) : L2R)) Q.sig Q.K
    Q.sig_pos Q.K_nonneg hrow hcol
  have hfib : ∑ b ∈ P, (Q.sig b * ‖((fibOf x b : ccDomain ℝ) : L2R)‖) ^ 2
      ≤ ∑ b ∈ P, ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 := by
    refine Finset.sum_le_sum fun b _ => ?_
    rw [shift_fib]
    exact pow_le_pow_left₀ (mul_nonneg (Q.sig_nonneg b) (norm_nonneg _))
      (sig_norm_le_shift W (Q.sig b) (Q.sig_nonneg b) (fibOf x b)) 2
  rw [mul_pow, norm_sq_eq_sum_of_supp P _ (shift_supp W Q hP1)]
  calc ∑ a ∈ P, ‖(secA Q x : Sec ι) a‖ ^ 2
      = ∑ a ∈ P, ‖∑ b ∈ P, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R)‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hval a]
    _ ≤ Q.K ^ 2 * ∑ b ∈ P, (Q.sig b * ‖((fibOf x b : ccDomain ℝ) : L2R)‖) ^ 2 := hschur
    _ ≤ Q.K ^ 2 * ∑ b ∈ P, ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hfib (by positivity)

theorem norm_secB_le (x : secCore (ι := ι)) :
    ‖secB Q x‖ ≤ 2 * Q.K * ‖secDiag W Q x + (x : Sec ι)‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  have hKT : 0 ≤ 2 * Q.K * ‖secDiag W Q x + (x : Sec ι)‖ :=
    mul_nonneg (by linarith [Q.K_nonneg]) (norm_nonneg _)
  refine le_of_sq_le_sq_nonneg hKT ?_
  have hsupp : ∀ a, a ∉ P → (secB Q x : Sec ι) a = 0 := modeOp_supp Q _ _ hP2
  rw [norm_sq_eq_sum_of_supp P _ hsupp]
  have hval : ∀ a, (secB Q x : Sec ι) a = ∑ b ∈ P, Q.B a b • xCc (fibOf x b) :=
    modeOp_eq_sum_band Q _ _ Q.B_off hP1
  have hrow : ∀ a, ∑ b ∈ P, ‖Q.B a b‖ / (1 : ℝ) ≤ Q.K := by
    intro a
    simp only [div_one]
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => norm_nonneg _) fun b hb => ?_)
      (Q.B_rel a)
    rw [Q.B_off a b hb, norm_zero]
  have hcol : ∀ b, ∑ a ∈ P, ‖Q.B a b‖ ≤ Q.K * 1 := by
    intro b
    rw [mul_one]
    refine le_trans (sum_le_sum_band P (Q.nbr b) _ (fun a => norm_nonneg _) fun a ha => ?_) ?_
    · rw [Q.B_off a b fun hba => ha ((Q.mem_nbr_comm b a).mpr hba), norm_zero]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (Q.B_rel b)
      rw [Q.B_herm b a]
      exact RCLike.norm_conj _
  have hschur := sum_norm_sq_mode_le P Q.B (fun b => xCc (fibOf x b)) (fun _ => (1 : ℝ)) Q.K
    (fun _ => one_pos) Q.K_nonneg hrow hcol
  have hfib : ∑ b ∈ P, ((1 : ℝ) * ‖xCc (fibOf x b)‖) ^ 2
      ≤ 2 * ∑ b ∈ P, ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [shift_fib, one_mul]
    exact norm_xCc_sq_le_shift W (Q.sig b) (Q.sig_nonneg b) (fibOf x b)
  rw [mul_pow, norm_sq_eq_sum_of_supp P _ (shift_supp W Q hP1)]
  have hK2 : (0 : ℝ) ≤ Q.K ^ 2 := sq_nonneg _
  calc ∑ a ∈ P, ‖(secB Q x : Sec ι) a‖ ^ 2
      = ∑ a ∈ P, ‖∑ b ∈ P, Q.B a b • xCc (fibOf x b)‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hval a]
    _ ≤ Q.K ^ 2 * ∑ b ∈ P, ((1 : ℝ) * ‖xCc (fibOf x b)‖) ^ 2 := hschur
    _ ≤ Q.K ^ 2 * (2 * ∑ b ∈ P,
          ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hfib hK2
    _ ≤ (2 * Q.K) ^ 2 * ∑ b ∈ P,
          ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 := by
        have hs : (0 : ℝ) ≤ ∑ b ∈ P,
            ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 :=
          Finset.sum_nonneg fun b _ => sq_nonneg _
        nlinarith

/-- **The Faris–Lavine relative bound** for the full quantum-gravity Hamiltonian: the
Hamiltonian is bounded by the shift of the comparison operator, with constant `1 + 3K`. -/
theorem secHam_rel (x : secCore (ι := ι)) :
    ‖secHam W Q x‖ ≤ (1 + 3 * Q.K) * ‖secDiag W Q x + (x : Sec ι)‖ := by
  have hsplit : secHam W Q x = secDiag W Q x + secA Q x + secB Q x := rfl
  have h1 := norm_secDiag_le W Q x
  have h2 := norm_secA_le W Q x
  have h3 := norm_secB_le W Q x
  calc ‖secHam W Q x‖ = ‖secDiag W Q x + secA Q x + secB Q x‖ := by rw [hsplit]
    _ ≤ ‖secDiag W Q x + secA Q x‖ + ‖secB Q x‖ := norm_add_le _ _
    _ ≤ ‖secDiag W Q x‖ + ‖secA Q x‖ + ‖secB Q x‖ := by
        have := norm_add_le (secDiag W Q x) (secA Q x)
        linarith
    _ ≤ (1 + 3 * Q.K) * ‖secDiag W Q x + (x : Sec ι)‖ := by linarith

/-! ## 4. Symmetry -/

theorem xCc_symmetricOn : SymmetricOn (ccDomain ℝ) xCc :=
  smoothPotential_symmetric (fun x : ℝ => x) contDiff_id

/-- Two core vectors share a finite band. -/
theorem exists_band₂ (x y : secCore (ι := ι)) :
    ∃ P : Finset ι, (∀ a, a ∉ P → (x : Sec ι) a = 0) ∧
      (∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) ∧
      (∀ a, a ∉ P → (y : Sec ι) a = 0) ∧
      (∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (y : Sec ι) b = 0) := by
  classical
  obtain ⟨Px, hx1, hx2⟩ := exists_band Q x
  obtain ⟨Py, hy1, hy2⟩ := exists_band Q y
  refine ⟨Px ∪ Py, ?_, ?_, ?_, ?_⟩ <;> intro a ha
  · exact hx1 a fun h => ha (Finset.mem_union_left _ h)
  · exact hx2 a fun h => ha (Finset.mem_union_left _ h)
  · exact hy1 a fun h => ha (Finset.mem_union_right _ h)
  · exact hy2 a fun h => ha (Finset.mem_union_right _ h)

theorem secHam_supp {P : Finset ι} {x : secCore (ι := ι)}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0)
    (hP2 : ∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) (a : ι) (ha : a ∉ P) :
    (secHam W Q x : Sec ι) a = 0 := by
  rw [secHam_apply]
  have h1 : W.ham (Q.sig a) (fibOf x a) = 0 := by
    rw [fibOf_eq_zero (hP1 a ha), map_zero]
  have h2 : ∑ b ∈ Q.nbr a, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) = 0 :=
    Finset.sum_eq_zero fun b hb => by rw [fibOf_eq_zero (hP2 a ha b hb)]; simp
  have h3 : ∑ b ∈ Q.nbr a, Q.B a b • xCc (fibOf x b) = 0 :=
    Finset.sum_eq_zero fun b hb => by
      rw [fibOf_eq_zero (hP2 a ha b hb), map_zero, smul_zero]
  rw [h1, h2, h3]
  simp

/-- **The expansion of the Hamiltonian against an arbitrary vector**, as a finite sum over
the band. -/
theorem inner_secHam_expand (x : secCore (ι := ι)) (z : Sec ι) {P : Finset ι}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0)
    (hP2 : ∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) :
    (inner ℂ (secHam W Q x) z : ℂ)
      = (∑ a ∈ P, (inner ℂ (W.ham (Q.sig a) (fibOf x a)) ((z : ∀ _ : ι, L2R) a) : ℂ))
        + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
            (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) ((z : ∀ _ : ι, L2R) a) : ℂ))
        + ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
            (inner ℂ (xCc (fibOf x b)) ((z : ∀ _ : ι, L2R) a) : ℂ) := by
  rw [inner_eq_sum_of_supp P _ z (secHam_supp W Q hP1 hP2)]
  have hterm : ∀ a ∈ P, (inner ℂ ((secHam W Q x : Sec ι) a) ((z : ∀ _ : ι, L2R) a) : ℂ)
      = (inner ℂ (W.ham (Q.sig a) (fibOf x a)) ((z : ∀ _ : ι, L2R) a) : ℂ)
        + (∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
            (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) ((z : ∀ _ : ι, L2R) a) : ℂ))
        + ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
            (inner ℂ (xCc (fibOf x b)) ((z : ∀ _ : ι, L2R) a) : ℂ) := by
    intro a _
    have hA : (secA Q x : Sec ι) a = ∑ b ∈ P, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) :=
      modeOp_eq_sum_band Q _ _ Q.A_off hP1 a
    have hB : (secB Q x : Sec ι) a = ∑ b ∈ P, Q.B a b • xCc (fibOf x b) :=
      modeOp_eq_sum_band Q _ _ Q.B_off hP1 a
    have hsplit : (secHam W Q x : Sec ι) a
        = W.ham (Q.sig a) (fibOf x a) + (secA Q x : Sec ι) a + (secB Q x : Sec ι) a := by
      change ((secDiag W Q x + secA Q x + secB Q x : Sec ι)) a = _
      rw [lp.coeFn_add, lp.coeFn_add]
      rfl
    rw [hsplit, hA, hB, inner_add_left, inner_add_left, sum_inner, sum_inner]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun b _ => inner_smul_left _ _ _
    · exact Finset.sum_congr rfl fun b _ => inner_smul_left _ _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- **The full quantum-gravity Hamiltonian is symmetric on the finite-particle core.** -/
theorem secHam_symmetricOn : SymmetricOn (secCore (ι := ι)) (secHam W Q) := by
  intro x y
  obtain ⟨P, hx1, hx2, hy1, hy2⟩ := exists_band₂ Q x y
  have hL := inner_secHam_expand W Q x (y : Sec ι) hx1 hx2
  have hR := inner_secHam_expand W Q y (x : Sec ι) hy1 hy2
  have hconj : (inner ℂ ((x : Sec ι)) (secHam W Q y) : ℂ)
      = (starRingEnd ℂ) (inner ℂ (secHam W Q y) ((x : Sec ι)) : ℂ) :=
    (inner_conj_symm _ _).symm
  rw [hL, hconj, hR]
  simp only [map_add, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun a _ => by
        rw [← fibOf_coe y a, ← fibOf_coe x a,
          W.ham_symmetricOn (Q.sig a) (fibOf x a) (fibOf y a), inner_conj_symm]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Q.A_herm b a, inner_conj_symm]
      simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← fibOf_coe y b, ← fibOf_coe x a, Q.B_herm b a, inner_conj_symm,
      xCc_symmetricOn (fibOf x a) (fibOf y b)]

/-! ## 5. The commutator bound -/

/-- The arithmetic–geometric mean bound for a symmetric double sum with row and column
sums bounded by `r`. -/
theorem double_sum_amgm (P : Finset ι) (w : ι → ι → ℝ) (f g r : ι → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hrow : ∀ a, ∑ b ∈ P, w a b ≤ r a) (hcol : ∀ b, ∑ a ∈ P, w a b ≤ r b) :
    ∑ a ∈ P, ∑ b ∈ P, w a b * (f a * g b)
      ≤ (1 / 2) * ((∑ a ∈ P, r a * f a ^ 2) + ∑ b ∈ P, r b * g b ^ 2) := by
  have step1 : ∑ a ∈ P, ∑ b ∈ P, w a b * (f a * g b)
      ≤ ∑ a ∈ P, ∑ b ∈ P, ((w a b * f a ^ 2) / 2 + (w a b * g b ^ 2) / 2) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    nlinarith [sq_nonneg (f a - g b), hw a b]
  have step2 : ∀ a, ∑ b ∈ P, ((w a b * f a ^ 2) / 2 + (w a b * g b ^ 2) / 2)
      = ((∑ b ∈ P, w a b) * f a ^ 2) / 2 + (∑ b ∈ P, w a b * g b ^ 2) / 2 := by
    intro a
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul]
  have step3 : ∑ a ∈ P, ∑ b ∈ P, ((w a b * f a ^ 2) / 2 + (w a b * g b ^ 2) / 2)
      = (∑ a ∈ P, (∑ b ∈ P, w a b) * f a ^ 2) / 2
        + (∑ b ∈ P, (∑ a ∈ P, w a b) * g b ^ 2) / 2 := by
    rw [Finset.sum_congr rfl fun a _ => step2 a, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div]
    congr 2
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
  have step4 : (∑ a ∈ P, (∑ b ∈ P, w a b) * f a ^ 2) ≤ ∑ a ∈ P, r a * f a ^ 2 :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hrow a) (sq_nonneg _)
  have step5 : (∑ b ∈ P, (∑ a ∈ P, w a b) * g b ^ 2) ≤ ∑ b ∈ P, r b * g b ^ 2 :=
    Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hcol b) (sq_nonneg _)
  rw [step3] at step1
  linarith

theorem norm_sub_conj_eq (z : ℂ) : ‖z - (starRingEnd ℂ) z‖ = 2 * |z.im| := by
  rw [Complex.sub_conj]
  simp

/-- The vielbein self-interaction contributes at most `½K` times the quadratic form to the
commutator. -/
theorem imA_le (x : secCore (ι := ι)) (P : Finset ι) :
    |(∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im|
      ≤ (1 / 2) * Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := by
  classical
  set u : ι → ccDomain ℝ := fun a => fibOf x a with hu
  set T1 : ℂ := ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
    (inner ℂ ((u b : ccDomain ℝ) : L2R) (W.ham 0 (u a)) : ℂ) with hT1def
  set T2 : ℂ := ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
    (((Q.sig a : ℝ) : ℂ) * (inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ))
    with hT2def
  have hsplit : (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
      (inner ℂ ((u b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (u a)) : ℂ)) = T1 + T2 := by
    rw [hT1def, hT2def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ham_eq_ham_zero_add W (Q.sig a) (u a), inner_add_right, inner_smul_right]
    ring
  -- the `h₀` part is real
  have hT1real : (starRingEnd ℂ) T1 = T1 := by
    rw [hT1def]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Q.A_herm a b, inner_conj_symm, W.ham_symmetricOn 0 (u b) (u a)]
  have hT1im : T1.im = 0 := Complex.conj_eq_iff_im.mp hT1real
  -- the shift part is controlled by the commutator hypothesis on `A`
  have hconjT2 : (starRingEnd ℂ) T2 = ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
      (((Q.sig b : ℝ) : ℂ) *
        (inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ)) := by
    rw [hT2def]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      Complex.conj_ofReal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Q.A_herm a b, inner_conj_symm]
  have hdiff : T2 - (starRingEnd ℂ) T2 = ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
      ((((Q.sig a - Q.sig b : ℝ)) : ℂ) *
        (inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ)) := by
    rw [hT2def, hconjT2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hbound : ‖T2 - (starRingEnd ℂ) T2‖
      ≤ ∑ a ∈ P, ∑ b ∈ P, (‖Q.A a b‖ * |Q.sig a - Q.sig b|) *
        (‖((u a : ccDomain ℝ) : L2R)‖ * ‖((u b : ccDomain ℝ) : L2R)‖) := by
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun a _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun b _ => ?_)
    have hcs : ‖(inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ)‖
        ≤ ‖((u a : ccDomain ℝ) : L2R)‖ * ‖((u b : ccDomain ℝ) : L2R)‖ := by
      rw [mul_comm]
      exact norm_inner_le_norm _ _
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs (abs_nonneg _))
      (norm_nonneg _)
  -- the Schur bounds for the weight
  have hwnn : ∀ a b, 0 ≤ ‖Q.A a b‖ * |Q.sig a - Q.sig b| := fun a b =>
    mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hwsymm : ∀ a b, ‖Q.A a b‖ * |Q.sig a - Q.sig b| = ‖Q.A b a‖ * |Q.sig b - Q.sig a| := by
    intro a b
    rw [Q.A_herm a b, RCLike.norm_conj, abs_sub_comm]
  have hrow : ∀ a, ∑ b ∈ P, ‖Q.A a b‖ * |Q.sig a - Q.sig b| ≤ Q.K * Q.sig a := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => hwnn a b) fun b hb => ?_) ?_
    · rw [Q.A_off a b hb, norm_zero, zero_mul]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => mul_comm _ _)) (Q.A_comm a)
  have hcol : ∀ b, ∑ a ∈ P, ‖Q.A a b‖ * |Q.sig a - Q.sig b| ≤ Q.K * Q.sig b := by
    intro b
    rw [Finset.sum_congr rfl fun a _ => hwsymm a b]
    exact hrow b
  have hamgm := double_sum_amgm P (fun a b => ‖Q.A a b‖ * |Q.sig a - Q.sig b|)
    (fun a => ‖((u a : ccDomain ℝ) : L2R)‖) (fun b => ‖((u b : ccDomain ℝ) : L2R)‖)
    (fun a => Q.K * Q.sig a) hwnn hrow hcol
  have hq : ∀ a, Q.K * Q.sig a * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2
      ≤ Q.K * quadForm (W.ham (Q.sig a)) (u a) := by
    intro a
    have h := sig_mul_norm_sq_le_quadForm W (Q.sig a) (u a)
    have : Q.K * (Q.sig a * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2)
        ≤ Q.K * quadForm (W.ham (Q.sig a)) (u a) :=
      mul_le_mul_of_nonneg_left h Q.K_nonneg
    linarith [this]
  have hsum : ∑ a ∈ P, Q.K * Q.sig a * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2
      ≤ Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (u a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hq a
  have hfinal : ‖T2 - (starRingEnd ℂ) T2‖ ≤ Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (u a) := by
    refine le_trans hbound (le_trans hamgm ?_)
    linarith [hsum]
  rw [hsplit]
  have him : (T1 + T2).im = T2.im := by
    rw [Complex.add_im, hT1im, zero_add]
  rw [him]
  have h2 := norm_sub_conj_eq T2
  rw [h2] at hfinal
  linarith

/-- The scalaron–vielbein coupling contributes at most `9K/4` times the quadratic form to
the commutator.  The scalaron Hamiltonian and the coupling do **not** commute: the
commutator identity `[h_s, φ] = -2 d/dφ` produces the derivative term, which the quadratic
form controls uniformly in the wall. -/
theorem imB_le (x : secCore (ι := ι)) (P : Finset ι) :
    |(∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im|
      ≤ (9 / 4) * Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := by
  classical
  set u : ι → ccDomain ℝ := fun a => fibOf x a with hu
  set U : ℂ := ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
    (inner ℂ (xCc (u b)) (W.ham (Q.sig a) (u a)) : ℂ) with hUdef
  set S : ℝ := ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (u a) with hSdef
  have hUswap : U = ∑ a ∈ P, ∑ b ∈ P, Q.B a b *
      (inner ℂ (xCc (u a)) (W.ham (Q.sig b) (u b)) : ℂ) := by
    rw [hUdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Q.B_herm a b]
    simp
  have hconjU : (starRingEnd ℂ) U = ∑ a ∈ P, ∑ b ∈ P, Q.B a b *
      ((inner ℂ (xCc (u a)) (W.ham (Q.sig a) (u b)) : ℂ)
        - 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)) := by
    rw [hUdef]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    have h := ham_x_comm_cc W (Q.sig a) (u a) (u b)
    linear_combination h
  have hfibdiff : ∀ a b, (inner ℂ (xCc (u a)) (W.ham (Q.sig b) (u b)) : ℂ)
      - (inner ℂ (xCc (u a)) (W.ham (Q.sig a) (u b)) : ℂ)
      = (((Q.sig b - Q.sig a : ℝ)) : ℂ) *
        (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ) := by
    intro a b
    rw [ham_eq_ham_zero_add W (Q.sig b) (u b), ham_eq_ham_zero_add W (Q.sig a) (u b),
      inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    push_cast
    ring
  have hdiff : U - (starRingEnd ℂ) U = ∑ a ∈ P, ∑ b ∈ P, Q.B a b *
      ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
          (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
        + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)) := by
    rw [hconjU, hUswap, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    linear_combination (Q.B a b) * hfibdiff a b
  -- termwise bound
  have hterm : ∀ a b, ‖Q.B a b *
      ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
          (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
        + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ))‖
      ≤ (‖Q.B a b‖ * |Q.sig a - Q.sig b|) * (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
        + 2 * (‖Q.B a b‖ * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖)) := by
    intro a b
    have h1 : ‖(((Q.sig b - Q.sig a : ℝ)) : ℂ) *
        (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)‖
        ≤ |Q.sig a - Q.sig b| * (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
    have h2 : ‖(2 : ℂ) * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)‖
        ≤ 2 * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖) := by
      rw [norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    calc ‖Q.B a b * ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
            (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
          + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ))‖
        = ‖Q.B a b‖ * ‖(((Q.sig b - Q.sig a : ℝ)) : ℂ) *
            (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
          + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖Q.B a b‖ * (|Q.sig a - Q.sig b| * (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
            + 2 * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact le_trans (norm_add_le _ _) (by linarith)
      _ = (‖Q.B a b‖ * |Q.sig a - Q.sig b|) *
            (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
          + 2 * (‖Q.B a b‖ * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖)) := by ring
  have hnormsum : ‖U - (starRingEnd ℂ) U‖
      ≤ (∑ a ∈ P, ∑ b ∈ P, (‖Q.B a b‖ * |Q.sig a - Q.sig b|) *
            (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖))
        + 2 * ∑ a ∈ P, ∑ b ∈ P, ‖Q.B a b‖ *
            (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖) := by
    rw [hdiff]
    refine le_trans (le_trans (norm_sum_le _ _)
      (Finset.sum_le_sum fun a _ => norm_sum_le _ _)) ?_
    have hstep : ∑ a ∈ P, ∑ b ∈ P, ‖Q.B a b *
        ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
            (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
          + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ))‖
        ≤ ∑ a ∈ P, ∑ b ∈ P, ((‖Q.B a b‖ * |Q.sig a - Q.sig b|) *
              (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
            + 2 * (‖Q.B a b‖ * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖))) :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    refine le_trans hstep (le_of_eq ?_)
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  -- the two Schur bounds
  have hBnn : ∀ a b, 0 ≤ ‖Q.B a b‖ := fun a b => norm_nonneg _
  have hBsymm : ∀ a b, ‖Q.B a b‖ = ‖Q.B b a‖ := by
    intro a b
    rw [Q.B_herm a b, RCLike.norm_conj]
  have hw1nn : ∀ a b, 0 ≤ ‖Q.B a b‖ * |Q.sig a - Q.sig b| := fun a b =>
    mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hw1symm : ∀ a b, ‖Q.B a b‖ * |Q.sig a - Q.sig b| = ‖Q.B b a‖ * |Q.sig b - Q.sig a| := by
    intro a b
    rw [← hBsymm a b, abs_sub_comm]
  have hrow1 : ∀ a, ∑ b ∈ P, ‖Q.B a b‖ * |Q.sig a - Q.sig b| ≤ Q.K := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => hw1nn a b) fun b hb => ?_) ?_
    · rw [Q.B_off a b hb, norm_zero, zero_mul]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => mul_comm _ _)) (Q.B_comm a)
  have hcol1 : ∀ b, ∑ a ∈ P, ‖Q.B a b‖ * |Q.sig a - Q.sig b| ≤ Q.K := by
    intro b
    rw [Finset.sum_congr rfl fun a _ => hw1symm a b]
    exact hrow1 b
  have hrow2 : ∀ a, ∑ b ∈ P, ‖Q.B a b‖ ≤ Q.K := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => hBnn a b) fun b hb => ?_)
      (Q.B_rel a)
    rw [Q.B_off a b hb, norm_zero]
  have hcol2 : ∀ b, ∑ a ∈ P, ‖Q.B a b‖ ≤ Q.K := by
    intro b
    rw [Finset.sum_congr rfl fun a _ => hBsymm a b]
    exact hrow2 b
  have hS1 := double_sum_amgm P (fun a b => ‖Q.B a b‖ * |Q.sig a - Q.sig b|)
    (fun a => ‖xCc (u a)‖) (fun b => ‖((u b : ccDomain ℝ) : L2R)‖) (fun _ => Q.K)
    hw1nn hrow1 hcol1
  have hS2 := double_sum_amgm P (fun a b => ‖Q.B a b‖)
    (fun a => ‖((u a : ccDomain ℝ) : L2R)‖) (fun b => ‖dCc (u b)‖) (fun _ => Q.K)
    hBnn hrow2 hcol2
  -- the fibre estimates
  have hxc : ∑ a ∈ P, Q.K * ‖xCc (u a)‖ ^ 2 ≤ 4 * Q.K * S := by
    rw [hSdef, mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := norm_xCc_sq_le_cc W (Q.sig a) (Q.sig_nonneg a) (u a)
    have hk := mul_le_mul_of_nonneg_left h Q.K_nonneg
    linarith
  have hnrm : ∑ a ∈ P, Q.K * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2 ≤ Q.K * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := norm_sq_le_quadForm_cc W (Q.sig a) (Q.one_le_sig a) (u a)
    exact mul_le_mul_of_nonneg_left h Q.K_nonneg
  have hder : ∑ a ∈ P, Q.K * ‖dCc (u a)‖ ^ 2 ≤ Q.K * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := norm_dCc_sq_le_cc W (Q.sig a) (Q.sig_nonneg a) (u a)
    exact mul_le_mul_of_nonneg_left h Q.K_nonneg
  have hfinal : ‖U - (starRingEnd ℂ) U‖ ≤ (9 / 2) * Q.K * S := by
    refine le_trans hnormsum ?_
    have e1 := hS1
    have e2 := hS2
    linarith
  have h2 := norm_sub_conj_eq U
  rw [h2] at hfinal
  linarith

/-! ## 6. The Faris–Lavine commutator bound -/

/-- The quadratic form of the fibrewise Hamiltonian is the sum of the fibre quadratic
forms over any band of the core vector. -/
theorem quadForm_secDiag_eq (x : secCore (ι := ι)) {P : Finset ι}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) :
    quadForm (secDiag W Q) x = ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := by
  rw [quadForm, inner_eq_sum_of_supp P (x : Sec ι) (secDiag W Q x) hP1, Complex.re_sum]
  rfl

theorem quadForm_secDiag_nonneg (x : secCore (ι := ι)) : 0 ≤ quadForm (secDiag W Q) x := by
  obtain ⟨P, hP1, _⟩ := exists_band Q x
  rw [quadForm_secDiag_eq W Q x hP1]
  exact Finset.sum_nonneg fun a _ => ham_quadForm_nonneg W (Q.sig a) (Q.sig_nonneg a) _

/-- **The Faris–Lavine commutator bound for the full quantum-gravity Hamiltonian.**  The
fibrewise scalaron Hamiltonian commutes with itself, the vielbein self-interaction
contributes at most `½K` and the scalaron–vielbein coupling at most `9/4 K` times the
quadratic form; the total is bounded by `6K` times the quadratic form of the comparison
operator. -/
theorem secHam_commForm_le (x : secCore (ι := ι)) :
    |commForm (secHam W Q) (secDiag W Q) x| ≤ (6 * Q.K) * quadForm (secDiag W Q) x := by
  classical
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  have hSq : quadForm (secDiag W Q) x
      = ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := quadForm_secDiag_eq W Q x hP1
  have hSnn : (0 : ℝ) ≤ ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) :=
    Finset.sum_nonneg fun a _ => ham_quadForm_nonneg W (Q.sig a) (Q.sig_nonneg a) _
  have hexp := inner_secHam_expand W Q x (secDiag W Q x : Sec ι) hP1 hP2
  simp only [secDiag_apply] at hexp
  have h1 : (∑ a ∈ P, (inner ℂ (W.ham (Q.sig a) (fibOf x a))
      (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im = 0 := by
    rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun a _ => by simpa using inner_self_im (𝕜 := ℂ) _
  have h2 := imA_le W Q x P
  have h3 := imB_le W Q x P
  have him : (inner ℂ (secHam W Q x) (secDiag W Q x : Sec ι) : ℂ).im
      = (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
            (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im
        + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
            (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im := by
    rw [hexp, Complex.add_im, Complex.add_im, h1, zero_add]
  have hKS : 0 ≤ Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) :=
    mul_nonneg Q.K_nonneg hSnn
  rw [commForm_eq, him, hSq]
  have habs : |(-2 : ℝ) * ((∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im
      + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im)|
      = 2 * |(∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im
      + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im| := by
    rw [abs_mul]
    norm_num
  rw [habs]
  have htri := abs_add_le ((∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im)
      ((∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im)
  linarith

/-! ## 7. Essential self-adjointness of the full quantum-gravity Hamiltonian -/

/-- **The Faris–Lavine core data of the gauge-fixed quantum-gravity Hamiltonian.**  The
comparison operator is the `ℓ²`-lift of the fibrewise Friedrichs extensions, the graph core
is the algebraic direct sum of the compactly supported smooth scalaron cores, and the
operator is the full Hamiltonian: fibrewise scalaron with the exponential Starobinsky wall,
vielbein self-interaction and scalaron–vielbein coupling. -/
def secData : CoreData (Sec ι) where
  C := secN W Q
  C₀ := secCore
  gc := secN_isGraphCore W Q
  H₀ := secHam W Q
  K := 1 + 3 * Q.K
  hK := by have := Q.K_nonneg; linarith
  rel := by
    intro p
    rw [secN_core W Q p]
    exact secHam_rel W Q p

@[simp] theorem secData_C : (secData W Q).C = secN W Q := rfl

@[simp] theorem secData_coreN (p : secCore (ι := ι)) :
    (secData W Q).coreN p = secDiag W Q p := secN_core W Q p

/-- The extension of the Hamiltonian from the finite-particle core to the whole domain of
the comparison operator restricts back to the Hamiltonian on the core. -/
theorem secData_ext_core (p : secCore (ι := ι)) :
    (secData W Q).ext ⟨(p : Sec ι), (secData W Q).gc.le p.2⟩ = secHam W Q p :=
  (secData W Q).ext_core p

/-- **Essential self-adjointness of the full gauge-fixed quantum-gravity Hamiltonian on the
outer Fock space.**

The Hamiltonian consists of the fibrewise scalaron operator `−∂²_φ + φ²/4 + V(φ) + σ_a`
with the *full exponential* Starobinsky wall (no Taylor truncation), the complete vielbein
self-interaction `A` and the scalaron–vielbein coupling `B`, all in the 3-dimensional
gauge-fixed formulation.  It is defined on the finite-particle core of the outer Fock space
`⊕_a L²(ℝ)` and extended, by its relative bound, to the whole domain of the lifted
Friedrichs extension `N`, where it is essentially self-adjoint by the Faris–Lavine
criterion: it is symmetric, relatively bounded by `N + 1`, and its commutator form with `N`
is dominated by `6K` times the quadratic form of `N`. -/
theorem secHam_essentiallySelfAdjointOn :
    EssentiallySelfAdjointOn (secN W Q).dom (secData W Q).ext := by
  refine (secData W Q).ext_essentiallySelfAdjointOn (secHam_symmetricOn W Q)
    (c := 6 * Q.K) (by have := Q.K_nonneg; linarith) ?_
  intro p
  have hc : commForm (secData W Q).H₀ (secData W Q).coreN p
      = commForm (secHam W Q) (secDiag W Q) p :=
    commForm_congr _ _ _ _ _ _ rfl (secData_coreN W Q p)
  have hq : quadForm (secData W Q).coreN p = quadForm (secDiag W Q) p :=
    quadForm_congr _ _ _ _ rfl (secData_coreN W Q p)
  rw [hc, hq]
  exact secHam_commForm_le W Q p

end

end BookProof.ScalaronOuterFockFL


