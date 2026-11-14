-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCMain
-- name    : RPLib_S4_AlgGrpCMain
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:07:16.767+00:00
-- url     : https://prove2.me/theorems/1141b0a6-191b-4058-a352-8f018840e0de
-- title:
--   Larsen's alternative library: the trace form is nondegenerate on `Lie H` (Engel + replicas)
-- statement:
--   Let `K` be algebraically closed of characteristic 0, `G ≤ GL_n K` act irreducibly on `n → K`,
--   and `H ≤ GL_n K` a subgroup whose tangent space `L = lieS H` is `Ad(G)`-stable. Then the trace
--   form `(X, Y) ↦ trace (X * Y)` is nondegenerate on `L` (`trace_form_nondegenerate`).
--
--   Proof: the radical `R = {X ∈ L | ∀ Y ∈ L, trace (X * Y) = 0}` is a Lie subalgebra
--   (`lieS_bracket`), consists of nilpotent matrices (`exists_trace_ne_zero`), hence (Engel) has a
--   nonzero common kernel, which is `G`-stable, hence everything; so `R = 0`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCTrace

/-!
# S4-AlgGrpC, file Main: the trace form is nondegenerate on `Lie H` (Engel + replicas)

Let `K` be algebraically closed of characteristic 0, `G ≤ GL_n K` act irreducibly on `n → K`,
and `H ≤ GL_n K` a subgroup whose tangent space `L = lieS H` is `Ad(G)`-stable. Then the trace
form `(X, Y) ↦ trace (X * Y)` is nondegenerate on `L` (`trace_form_nondegenerate`).

Proof: the radical `R = {X ∈ L | ∀ Y ∈ L, trace (X * Y) = 0}` is a Lie subalgebra
(`lieS_bracket`), consists of nilpotent matrices (`exists_trace_ne_zero`), hence (Engel) has a
nonzero common kernel, which is `G`-stable, hence everything; so `R = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial
open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `A` lies in the trace-radical of `L`. -/
def IsTrRad (L : Submodule K (Matrix n n K)) (A : Matrix n n K) : Prop :=
  A ∈ L ∧ ∀ Y ∈ L, (A * Y).trace = 0

/-- The trace-radical of `Lie H`, as a Lie subalgebra of `End (n → K)`. -/
def radL (H : Subgroup (Matrix.GeneralLinearGroup n K)) : LieSubalgebra K (Module.End K (n → K)) where
  carrier := {f | IsTrRad (lieS (H : Set (Matrix.GeneralLinearGroup n K))) (LinearMap.toMatrix' f)}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨by rw [map_add]; exact add_mem hf1 hg1, fun Y hY => ?_⟩
    rw [map_add, Matrix.add_mul, Matrix.trace_add, hf2 Y hY, hg2 Y hY, add_zero]
  zero_mem' := ⟨by rw [map_zero]; exact zero_mem _, fun Y _ => by
    rw [map_zero, Matrix.zero_mul, Matrix.trace_zero]⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨by rw [map_smul]; exact Submodule.smul_mem _ c hf1, fun Y hY => ?_⟩
    rw [map_smul, Matrix.smul_mul, Matrix.trace_smul, hf2 Y hY, smul_zero]
  lie_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    have e : LinearMap.toMatrix' ⁅f, g⁆ =
        LinearMap.toMatrix' f * LinearMap.toMatrix' g - LinearMap.toMatrix' g * LinearMap.toMatrix' f := by
      rw [LieRing.of_associative_ring_bracket, map_sub, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul]
    refine ⟨by rw [e]; exact lieS_bracket hf1 hg1, fun Y hY => ?_⟩
    set A := LinearMap.toMatrix' f
    set B := LinearMap.toMatrix' g
    have h1 : (B * A * Y).trace = (A * (Y * B)).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle A Y B]
    rw [e, Matrix.sub_mul, Matrix.trace_sub, h1, ← Matrix.trace_sub, Matrix.mul_assoc, ← Matrix.mul_sub]
    exact hf2 _ (lieS_bracket hg1 hY)

/-- The trace-radical is stable under conjugation by `G` when `Lie H` is. -/
theorem isTrRad_conj {G H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hL : ∀ g ∈ G, ∀ X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)),
      (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
        lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ G) {A : Matrix n n K}
    (hA : IsTrRad (lieS (H : Set (Matrix.GeneralLinearGroup n K))) A) :
    IsTrRad (lieS (H : Set (Matrix.GeneralLinearGroup n K)))
      (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * A * (g : Matrix n n K)) := by
  refine ⟨?_, fun Y hY => ?_⟩
  · have := hL g⁻¹ (inv_mem hg) A hA.1
    rwa [inv_inv] at this
  · have : (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * A * (g : Matrix n n K) * Y).trace =
        (A * ((g : Matrix n n K) * Y * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K))).trace := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this]
    exact hA.2 _ (hL g hg Y hY)

/-- **Nondegeneracy of the trace form on `Lie H`** (K algebraically closed, char 0, `G` irreducible,
`Lie H` stable under `Ad(G)`). -/
theorem trace_form_nondegenerate [IsAlgClosed K] [CharZero K]
    {G H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hL : ∀ g ∈ G, ∀ X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)),
      (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
        lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {X : Matrix n n K} (hX : X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (hXY : ∀ Y ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)), (X * Y).trace = 0) : X = 0 := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · ext i; exact isEmptyElim i
  set L := lieS (H : Set (Matrix.GeneralLinearGroup n K))
  let R := radL H
  have hnil : ∀ f : R, IsNilpotent (LieModule.toEnd K R (n → K) f) := by
    intro f
    rw [LieSubalgebra.toEnd_eq, LieModule.toEnd_module_end, LieHom.id_apply]
    obtain ⟨hf1, hf2⟩ := f.2
    by_contra hfn
    have hfn' : ¬ IsNilpotent (LinearMap.toMatrix' (f : Module.End K (n → K))) := fun h => by
      have := h.map (Matrix.toLinAlgEquiv' (R := K) (n := n))
      rw [show LinearMap.toMatrix' (f : Module.End K (n → K)) =
        LinearMap.toMatrixAlgEquiv' (f : Module.End K (n → K)) from rfl,
        Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'] at this
      exact hfn this
    obtain ⟨Y, hY, hne⟩ := exists_trace_ne_zero hf1 hfn'
    exact hne (hf2 Y hY)
  have : LieModule.IsNilpotent R (n → K) := (LieModule.isNilpotent_iff_forall' (R := K)).2 hnil
  have hnt := LieModule.nontrivial_max_triv_of_isNilpotent K R (n → K)
  obtain ⟨⟨m, hm⟩, hm0⟩ := exists_ne (0 : LieModule.maxTrivSubmodule K R (n → K))
  have hm0' : m ≠ 0 := fun h => hm0 (by subst h; rfl)
  rw [LieModule.mem_maxTrivSubmodule] at hm
  let W : Submodule K (n → K) := ⨅ (A : Matrix n n K) (_ : IsTrRad L A), LinearMap.ker (Matrix.toLin' A)
  have memW : ∀ v, v ∈ W ↔ ∀ A, IsTrRad L A → A *ᵥ v = 0 := fun v => by
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hmW : m ∈ W := (memW m).2 fun A hA => by
    have := hm ⟨Matrix.toLin' A, by
      show IsTrRad L (LinearMap.toMatrix' (Matrix.toLin' A))
      rwa [LinearMap.toMatrix'_toLin']⟩
    rw [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply] at this
    rwa [Matrix.toLin'_apply] at this
  have hWG : ∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W := by
    intro g hg v hv
    refine (memW _).2 fun A hA => ?_
    have h1 := (memW v).1 hv _ (isTrRad_conj hL hg hA)
    have h2 : (g : Matrix n n K) * (((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * A *
        (g : Matrix n n K)) = A * (g : Matrix n n K) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rcases hG W hWG with hW | hW
  · exact absurd (hW ▸ hmW : m ∈ (⊥ : Submodule K (n → K))) (by simpa using hm0')
  · have hv : ∀ v, X *ᵥ v = 0 := fun v =>
      (memW v).1 (hW ▸ Submodule.mem_top) X ⟨hX, hXY⟩
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hv v)

end RamanujanPetersson.AlgGrpC


