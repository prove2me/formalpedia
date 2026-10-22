-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
-- name    : LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:34:35.60034+00:00
-- url     : https://prove2.me/theorems/6e09168e-b972-46a9-84c7-8b572fa1a5ac
-- title:
--   Signed subset and augmented reduced-cochain complexes
-- statement:
--   This bundle supplies signed subset and augmented reduced-cochain complexes. These selected declarations concern field-valued signed cochains on finite vertex types, with integer cardinality offsets and ordinary restriction maps. The signed complex assumes a convex family. Restriction commutes with its differential under the stated relative downward-closure hypothesis, not for an arbitrary subfamily. Offset minus one retains the empty face in degree minus one, and offset changes introduce no categorical-shift sign.
--
--   The included constructions and necessary compatibility results are:
--
--   - Basis index set of the signed subset complex in degree `n`: members of `𝓕` of size `n - m`.
--   - The differential `(d f)(J') = Σ_J inc J J' · f J`, i.e. `d(e_J) = Σ_{j∉J} (-1)^{ν_J(j)} e_{J∪{j}}`.
--   - The signed subset complex of a convex family `𝓕` with degree offset `m`.
--   - Restriction to a subfamily `𝓕' ⊆ 𝓕`: `e_J ↦ e_J` if `J ∈ 𝓕'`, else `0`. On functions: precomposition with the inclusion of index sets.
--   - Changing the degree offset: `Idx 𝓕 m n ≃ Idx 𝓕 m' n'` when `n - m = n' - m'` (same sets).
--   - Reduced cochains of `K` with degree offset `m`: degree `n` has basis the faces with `n - m` elements. The standard reduced cochain complex `C̃^•(K)` is `redCochain k K (-1)`; `redCochain k K G.card` is `C̃^{• - |G| - 1}(K)`.
--   - Restriction of reduced cochains along `K' ≤ K`.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/BassStatic/Common.lean, selected declarations in lines 34–111; source SHA-256 48fe82ff2f579f399600c00029956a4811096c4544b73a24d4c6f90c5c01d6c9; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs

namespace Proofs.BassLyubeznik.BassStatic

open Finset CategoryTheory Proofs.BassLyubeznik.SignedCore Proofs.BassLyubeznik.SrFamily

universe u v

variable {V : Type u} [LinearOrder V] [Fintype V] (k : Type v) [Field k]

namespace Signed

/-- Basis index set of the signed subset complex in degree `n`: members of `𝓕` of size `n - m`. -/
abbrev Idx (𝓕 : Finset V → Prop) [DecidablePred 𝓕] (m n : ℤ) : Type u :=
  {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n - m}

/-- The differential `(d f)(J') = Σ_J inc J J' · f J`, i.e. `d(e_J) = Σ_{j∉J} (-1)^{ν_J(j)} e_{J∪{j}}`. -/
noncomputable def dLin (𝓕 : Finset V → Prop) [DecidablePred 𝓕] (m n : ℤ) :
    (Idx 𝓕 m n → k) →ₗ[k] (Idx 𝓕 m (n + 1) → k) where
  toFun f J' := ∑ J, inc k J.1 J'.1 * f J
  map_add' f g := by
    funext J'
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext J'
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- The signed subset complex of a convex family `𝓕` with degree offset `m`. -/
noncomputable def complex (𝓕 : Finset V → Prop) [DecidablePred 𝓕] (m : ℤ) (hconv : IsConvex 𝓕) :
    CochainComplex (ModuleCat.{max u v} k) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of k (Idx 𝓕 m n → k))
    (fun n => ModuleCat.ofHom (dLin k 𝓕 m n))
    (fun n => by
      refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun J'' => ?_)
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
      exact dd_sum hconv m n f J'')



/-- Restriction to a subfamily `𝓕' ⊆ 𝓕`: `e_J ↦ e_J` if `J ∈ 𝓕'`, else `0`. On functions:
precomposition with the inclusion of index sets. -/
noncomputable def restrictLin (𝓕 : Finset V → Prop) [DecidablePred 𝓕] (m : ℤ)
    {𝓕' : Finset V → Prop} [DecidablePred 𝓕'] (h𝓕 : ∀ J, 𝓕' J → 𝓕 J) (n : ℤ) :
    (Idx 𝓕 m n → k) →ₗ[k] (Idx 𝓕' m n → k) :=
  LinearMap.funLeft k k (fun J => ⟨J.1, h𝓕 J.1 J.2.1, J.2.2⟩)

/-- Changing the degree offset: `Idx 𝓕 m n ≃ Idx 𝓕 m' n'` when `n - m = n' - m'` (same sets). -/
def idxCongr (𝓕 : Finset V → Prop) [DecidablePred 𝓕] {m m' n n' : ℤ} (h : n - m = n' - m') :
    Idx 𝓕 m n ≃ Idx 𝓕 m' n' :=
  Equiv.subtypeEquivRight (fun J => by rw [h])

end Signed



/-- Reduced cochains of `K` with degree offset `m`: degree `n` has basis the faces with `n - m`
elements. The standard reduced cochain complex `C̃^•(K)` is `redCochain k K (-1)`;
`redCochain k K G.card` is `C̃^{• - |G| - 1}(K)`. -/
noncomputable abbrev redCochain (K : SComplex V) (m : ℤ) : CochainComplex (ModuleCat.{max u v} k) ℤ :=
  Signed.complex k (faceFamily K) m (faceFamily_convex K)





/-- Restriction of reduced cochains along `K' ≤ K`. -/
noncomputable abbrev redRestrictLin {K' K : SComplex V} (h : K' ≤ K) (m n : ℤ) :
    (Signed.Idx (faceFamily K) m n → k) →ₗ[k] (Signed.Idx (faceFamily K') m n → k) :=
  Signed.restrictLin k (faceFamily K) m (faceFamily_mono h) n







end Proofs.BassLyubeznik.BassStatic


