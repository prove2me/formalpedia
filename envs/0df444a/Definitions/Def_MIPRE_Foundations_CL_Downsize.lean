-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Downsize
-- name    : MIPRE_Foundations_CL_Downsize
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:48.813425+00:00
-- url     : https://prove2.me/theorems/4fe01969-2504-49bb-b188-7f76cf01420c
-- title:
--   Definitions of Downsize: Downsizing conditionally linear functions, and reindexing Paper `linear.tex`, `def:cl-downsize`, `lem:cl-downsize` and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Downsize` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Downsizing conditionally linear functions, and reindexing. Paper `linear.tex`, `def:cl-downsize`, `lem:cl-downsize` and `lem:downsize-cl-dist`; blueprint `lem:cl-downsize`. The CL functions of the pipeline are native to `𝔽_{2^t}` (the low-degree tests, the introspection sampler), while samplers of normal form verifiers are over `𝔽₂` (`def:sampler`). *Downsizing* bridges the two: a basis `b` of a field `F` over a subfield `K` gives the `K`-linear bijection `↓ : F^ι ≃ K^{ι × κ}` reading off coordinates entry by entry (`downsizeEquiv`), and `L ↦ ↓ ∘ L ∘ ↓⁻¹` carries `ℓ`-level CL functions on…
--
--   **Definitions** (6): `MIPRE.CL.CLFun.downsize` (The downsized presentation `L^↓` (paper `def:cl-downsize`): register subspaces `S` become `S × κ`, the linear maps are conjugated by the…); `MIPRE.CL.CLFun.reindex` (A presentation, transported along a bijection of coordinates.); `MIPRE.CL.RegLinear.downsize` (The downsized linear map `↓ ∘ L ∘ ↓⁻¹` of a map on `V_S`: a map on `V_{S × κ}` over `K`.); `MIPRE.CL.RegLinear.reindex` (A map on `V_S`, transported along `e`.); `MIPRE.CL.downsizeEquiv` (The downsize map of a basis `b` of `F` over `K`, on vectors: `F^ι ≃ K^{ι × κ}`, sending `v` to the coordinates of its entries, `↓v (i, j) =…); `MIPRE.CL.reindexEquiv` (Transport of vectors along a bijection of coordinates, `x ↦ x ∘ e.symm`: the identification `K^{ι} = K^{ι'}` (for instance `K^{ι × κ} =…).
--
--   **Embedded lemmas** (15): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `downsize_cons`, `downsize_zero`, `reindex_cons`, `reindex_zero`, `downsize_apply`, `downsize_zero`, `reindex_apply`, `reindex_zero`, `downsizeEquiv_apply`, `downsizeEquiv_proj`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Downsize` (`MIPRE/Foundations/CL/Downsize.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Downsize.lean; blueprint lem:cl-downsize

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Downsize.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B

/-!
# Downsizing conditionally linear functions, and reindexing

Paper `linear.tex`, `def:cl-downsize`, `lem:cl-downsize` and `lem:downsize-cl-dist`; blueprint
`lem:cl-downsize`. The CL functions of the pipeline are native to `𝔽_{2^t}` (the low-degree
tests, the introspection sampler), while samplers of normal form verifiers are over `𝔽₂`
(`def:sampler`). *Downsizing* bridges the two: a basis `b` of a field `F` over a subfield `K`
gives the `K`-linear bijection `↓ : F^ι ≃ K^{ι × κ}` reading off coordinates entry by entry
(`downsizeEquiv`), and `L ↦ ↓ ∘ L ∘ ↓⁻¹` carries `ℓ`-level CL functions on `F^ι` to `ℓ`-level CL
functions on `K^{ι × κ}` — on presentations, `CLFun.downsize`, whose decomposition data are
the downsized data of the original: register subspaces `S` become `S × κ`, stage maps are
conjugated by `↓`, and the marginals, factor spaces and stage maps of `lem:cl-kth` correspond
(`eval_truncate_downsize`, `factorOfPrefix_downsize`, `mapOfPrefix_downsize`). Exactness is
preserved, and the CL distribution is pushed forward along `↓` (`clDist_downsize`).

The paper states this for admissible field sizes `q = 2^t`, `t` odd, with the self-dual
normal basis of blueprint `lem:self-dual-basis`. Nothing here depends on the choice of basis:
the self-duality matters for the *arithmetic* of `𝔽_{2^t}` to be computable from `𝔽₂`-data
by the programs that use it, which is a matter for the efficient-computability toolkit. The
paper's downsized *sampler* (`def:downsize_sampler`), a machine wrapping a sampler over
`𝔽_{2^t}`, has no counterpart: samplers are over `𝔽₂` by definition, and a construction native
to `𝔽_{2^t}` is to present the downsized CL functions directly.

The second half of the file is the transport of presentations along a bijection of
coordinates `e : ι ≃ ι'` (`reindexEquiv`, `CLFun.reindex`), with the same list of lemmas; it is
the identification `K^{ι × κ} = K^{|ι| · |κ|}` the paper leaves implicit, and it is what puts a
downsized presentation on the coordinates `Fin (s · t)` of a sampler.
-/

namespace MIPRE.CL

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]

/-! ## The downsize map, and the transport along a bijection of coordinates -/

/-- The downsize map of a basis `b` of `F` over `K`, on vectors: `F^ι ≃ K^{ι × κ}`, sending
`v` to the coordinates of its entries, `↓v (i, j) = (b.repr (v i)) j`. -/
noncomputable def downsizeEquiv (b : Module.Basis κ K F) : (ι → F) ≃ₗ[K] (ι × κ → K) where
  toFun x p := b.repr (x p.1) p.2
  invFun y i := b.repr.symm (Finsupp.equivFunOnFinite.symm fun j => y (i, j))
  map_add' x y := by ext p; simp
  map_smul' c x := by ext p; simp
  left_inv x := by
    funext i
    simp only
    rw [Finsupp.equivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply]
  right_inv y := by
    funext p
    simp only
    rw [LinearEquiv.apply_symm_apply]
    rfl

@[simp] theorem downsizeEquiv_apply (b : Module.Basis κ K F) (x : ι → F) (p : ι × κ) :
    downsizeEquiv b x p = b.repr (x p.1) p.2 := rfl

/-- Transport of vectors along a bijection of coordinates, `x ↦ x ∘ e.symm`: the identification
`K^{ι} = K^{ι'}` (for instance `K^{ι × κ} = K^{|ι| · |κ|}`, the paper's `𝔽_2^{nt}`). -/
def reindexEquiv (e : ι ≃ ι') : (ι → F) ≃ₗ[F] (ι' → F) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp

@[simp] theorem reindexEquiv_apply (e : ι ≃ ι') (x : ι → F) (i : ι') :
    reindexEquiv e x i = x (e.symm i) := rfl

@[simp] theorem reindexEquiv_symm_apply (e : ι ≃ ι') (y : ι' → F) (i : ι) :
    (reindexEquiv e).symm y i = y (e i) := rfl

variable [DecidableEq ι] [DecidableEq κ]

theorem downsizeEquiv_proj (b : Module.Basis κ K F) (S : Finset ι) (x : ι → F) :
    downsizeEquiv b (proj S x) = proj (S ×ˢ Finset.univ) (downsizeEquiv b x) := by
  ext ⟨i, j⟩
  simp only [downsizeEquiv_apply, proj_apply, Finset.mem_product, Finset.mem_univ, and_true]
  split_ifs <;> simp

theorem downsizeEquiv_symm_proj (b : Module.Basis κ K F) (S : Finset ι) (y : ι × κ → K) :
    (downsizeEquiv b).symm (proj (S ×ˢ Finset.univ) y) = proj S ((downsizeEquiv b).symm y) := by
  conv_lhs => rw [← (downsizeEquiv b).apply_symm_apply y]
  rw [← downsizeEquiv_proj, LinearEquiv.symm_apply_apply]

namespace RegLinear

variable {S : Finset ι}

/-- The downsized linear map `↓ ∘ L ∘ ↓⁻¹` of a map on `V_S`: a map on `V_{S × κ}` over `K`. -/
noncomputable def downsize (b : Module.Basis κ K F) (L : RegLinear F S) :
    RegLinear K (S ×ˢ (Finset.univ : Finset κ)) where
  toLinearMap := (downsizeEquiv (ι := ι) b).toLinearMap ∘ₗ
    (L.toLinearMap.restrictScalars K) ∘ₗ (downsizeEquiv (ι := ι) b).symm.toLinearMap
  proj_comp_proj' y := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.restrictScalars_apply,
      toLinearMap_apply, downsizeEquiv_symm_proj, apply_proj, ← downsizeEquiv_proj, proj_apply]

@[simp] theorem downsize_apply (b : Module.Basis κ K F) (L : RegLinear F S) (y : ι × κ → K) :
    L.downsize b y = downsizeEquiv b (L ((downsizeEquiv b).symm y)) := rfl

@[simp] theorem downsize_zero (b : Module.Basis κ K F) :
    (0 : RegLinear F S).downsize b = 0 := by
  ext y; simp

end RegLinear

namespace CLFun

variable {ℓ : ℕ}

/-- The downsized presentation `L^↓` (paper `def:cl-downsize`): register subspaces `S` become
`S × κ`, the linear maps are conjugated by the downsize map, and the continuations are selected
through it. -/
noncomputable def downsize (b : Module.Basis κ K F) : {ℓ : ℕ} → CLFun F ι ℓ → CLFun K (ι × κ) ℓ
  | _, zero => zero
  | _, cons S L₁ next =>
    cons (S ×ˢ (Finset.univ : Finset κ)) (L₁.downsize b)
      fun v => (next ((downsizeEquiv b).symm v)).downsize b

@[simp] theorem downsize_zero (b : Module.Basis κ K F) :
    (zero : CLFun F ι 0).downsize b = zero := rfl

@[simp] theorem downsize_cons (b : Module.Basis κ K F) {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) :
    (cons S L₁ next).downsize b =
      cons (S ×ˢ (Finset.univ : Finset κ)) (L₁.downsize b)
        fun v => (next ((downsizeEquiv b).symm v)).downsize b := rfl

end CLFun

/-! ## Reindexing coordinates -/

section Reindex

variable [DecidableEq ι']

theorem reindexEquiv_proj (e : ι ≃ ι') (S : Finset ι) (x : ι → F) :
    reindexEquiv e (proj S x) = proj (S.map e.toEmbedding) (reindexEquiv e x) := by
  ext i
  simp [Finset.mem_map_equiv]

theorem reindexEquiv_symm_proj (e : ι ≃ ι') (S : Finset ι) (y : ι' → F) :
    (reindexEquiv e).symm (proj (S.map e.toEmbedding) y) = proj S ((reindexEquiv e).symm y) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [← reindexEquiv_proj, LinearEquiv.symm_apply_apply]

/-- A map on `V_S`, transported along `e`. -/
def RegLinear.reindex (e : ι ≃ ι') {S : Finset ι} (L : RegLinear F S) :
    RegLinear F (S.map e.toEmbedding) where
  toLinearMap := (reindexEquiv e).toLinearMap ∘ₗ L.toLinearMap ∘ₗ (reindexEquiv e).symm.toLinearMap
  proj_comp_proj' y := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, RegLinear.toLinearMap_apply,
      reindexEquiv_symm_proj, RegLinear.apply_proj, ← reindexEquiv_proj, RegLinear.proj_apply]

@[simp] theorem RegLinear.reindex_apply (e : ι ≃ ι') {S : Finset ι} (L : RegLinear F S)
    (y : ι' → F) : L.reindex e y = reindexEquiv e (L ((reindexEquiv e).symm y)) := rfl

@[simp] theorem RegLinear.reindex_zero (e : ι ≃ ι') {S : Finset ι} :
    (0 : RegLinear F S).reindex e = 0 := by
  ext y; simp

namespace CLFun

variable {ℓ : ℕ}

/-- A presentation, transported along a bijection of coordinates. -/
def reindex (e : ι ≃ ι') : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι' ℓ
  | _, zero => zero
  | _, cons S L₁ next =>
    cons (S.map e.toEmbedding) (L₁.reindex e) fun v => (next ((reindexEquiv e).symm v)).reindex e

@[simp] theorem reindex_zero (e : ι ≃ ι') : (zero : CLFun F ι 0).reindex e = zero := rfl

@[simp] theorem reindex_cons (e : ι ≃ ι') {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) :
    (cons S L₁ next).reindex e =
      cons (S.map e.toEmbedding) (L₁.reindex e)
        fun v => (next ((reindexEquiv e).symm v)).reindex e := rfl

end CLFun

end Reindex

/-! ## Evaluation, and the data of `lem:cl-kth` -/

variable [Fintype ι]

namespace CLFun

variable {ℓ : ℕ}

end CLFun

section Reindex

variable [DecidableEq ι'] [Fintype ι']

namespace CLFun

variable {ℓ : ℕ}

end CLFun

end Reindex

section Distribution

variable [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]

end Distribution

end MIPRE.CL


