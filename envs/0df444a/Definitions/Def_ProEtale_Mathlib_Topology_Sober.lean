-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Sober
-- name    : ProEtale_Mathlib_Topology_Sober
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:14.348009+00:00
-- url     : https://prove2.me/theorems/d0689a5e-5089-5248-94b5-ab876db27b6d
-- title:
--   Quasi-sobriety is preserved by homeomorphisms and by finite products
-- statement:
--   A topological space is **quasi-sober** if every irreducible closed subset has a generic point.
--
--   Principal results:
--   1. If $X$ is quasi-sober and $X \cong Y$ is a homeomorphism, then $Y$ is quasi-sober.
--   2. If $X$ and $Y$ are quasi-sober, then so is $X \times Y$: for an irreducible closed $Z \subseteq X \times Y$, the pair of generic points of the closures of its two projections lies in $Z$ and is a generic point of $Z$.
--
--   These are used to show that products and homeomorphic copies of spectral spaces (e.g. $T \times X$ for profinite $T$) are again spectral.
--
--   **Formalization Note** Declarations: `Homeomorph.quasiSober` and the instance `QuasiSober.prod`, using Mathlib's `QuasiSober`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Sober.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Sober

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- after `quasiSober_iff`
-- `by copilot`
theorem Homeomorph.quasiSober {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] (f : X ≃ₜ Y) : QuasiSober Y := by
  -- Prove quasi-sobriety of `Y` by producing generic points for irreducible closed sets.
  refine ⟨?_⟩
  intro S hSirr hSclosed
  -- Pull back `S` along the homeomorphism.
  let T : Set X := f.symm '' S
  have hTclosed : IsClosed T := by
    -- `f.symm` is a homeomorphism `Y ≃ₜ X`, so it maps closed sets to closed sets.
    simpa [T] using (Homeomorph.isClosed_image (X := Y) (Y := X) f.symm (s := S)).2 hSclosed
  have hTirr : IsIrreducible T := by
    -- Use `IsIrreducible.image` with `ContinuousOn`.
    -- (`Continuous` implies `ContinuousOn`.)
    simpa [T] using hSirr.image (fun y : Y => f.symm y) (f.symm.continuous.continuousOn)
  -- Get a generic point of `T` in `X`, then transport it to `Y`.
  have hx : IsGenericPoint hTirr.genericPoint T :=
    hTirr.isGenericPoint_genericPoint hTclosed
  -- `hx.image` gives a generic point for `closure (f '' T)`
  have hy : IsGenericPoint (f hTirr.genericPoint) (closure (f '' T)) :=
    hx.image f.continuous
  -- Now show `closure (f '' T) = S`, so `f hTirr.genericPoint` is generic for `S`.
  have hclosure : closure (f '' T) = S := by
    -- First compute `f '' T = S`.
    have himage : f '' T = S := by
      -- `f '' (f.symm '' S) = S` for a homeomorphism.
      ext y
      constructor
      · rintro ⟨x, hxT, rfl⟩
        rcases hxT with ⟨y', hy'S, rfl⟩
        simpa using hy'S
      · intro hyS
        refine ⟨f.symm y, ?_, by simp⟩
        exact ⟨y, hyS, by simp⟩
    -- Since `S` is closed, `closure S = S`.
    simp [himage]
  -- Convert the generic-point target set using `hclosure`.
  have : IsGenericPoint (f hTirr.genericPoint) S := by
    simpa [hclosure] using hy
  exact ⟨f hTirr.genericPoint, this⟩

/-- The product of two quasi-sober spaces is quasi-sober. -/
-- put this at end of the file
instance QuasiSober.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] : QuasiSober (X × Y) := by
  refine ⟨fun {S} hS hSclosed => ?_⟩
  have hX := hS.image Prod.fst continuous_fst.continuousOn
  have hY := hS.image Prod.snd continuous_snd.continuousOn
  have hx₀ := hX.isGenericPoint_genericPoint_closure
  have hy₀ := hY.isGenericPoint_genericPoint_closure
  suffices hmem : (hX.genericPoint, hY.genericPoint) ∈ S by
    refine ⟨_, (closure_minimal (Set.singleton_subset_iff.mpr hmem) hSclosed).antisymm ?_⟩
    rw [← Set.singleton_prod_singleton, closure_prod_eq, hx₀.def, hy₀.def]
    exact fun ⟨a, b⟩ hab => ⟨subset_closure ⟨_, hab, rfl⟩, subset_closure ⟨_, hab, rfl⟩⟩
  by_contra hmem
  obtain ⟨U, V, hU, hV, hx₀U, hy₀V, hUV⟩ :=
    isOpen_prod_iff.mp hSclosed.isOpen_compl _ _ hmem
  have : S ⊆ (Uᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Vᶜ) := fun ⟨a, b⟩ hab => by
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and]
    by_contra h; push Not at h; exact hUV (Set.mk_mem_prod h.1 h.2) hab
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hS.isPreirreducible) _ _
    (hU.isClosed_compl.prod isClosed_univ) (isClosed_univ.prod hV.isClosed_compl) this with h | h
  · have : Prod.fst '' S ⊆ Uᶜ := Set.image_subset_iff.mpr fun p hp => (h hp).1
    exact closure_minimal this hU.isClosed_compl
      (hx₀.def ▸ subset_closure (Set.mem_singleton _)) hx₀U
  · have : Prod.snd '' S ⊆ Vᶜ := Set.image_subset_iff.mpr fun p hp => (h hp).2
    exact closure_minimal this hV.isClosed_compl
      (hy₀.def ▸ subset_closure (Set.mem_singleton _)) hy₀V


