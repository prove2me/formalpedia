-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpAIdComp
-- name    : RPLib_S4_AlgGrpAIdComp
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:35:43.35489+00:00
-- url     : https://prove2.me/theorems/d985c4e3-4e11-4f4a-b740-ecdf1ecca9e6
-- title:
--   Larsen's alternative library: Zariski closures and identity components in `GL_n(K)`
-- statement:
--   * `zclosure H`: the Zariski closure of a subgroup `H ≤ GL_n(K)`, a Zariski closed subgroup.
--   * `idCompGL G`: the identity component of a subgroup `G` (for its subspace Zariski topology).
--     For Zariski closed `G` it is closed, irreducible, normal and of finite index in `G`, open in
--     `G`, contained in every closed subgroup of finite index of `G`, and it contains every
--     irreducible subset of `G` through `1`; `G` is finite iff `idCompGL G = ⊥`, and `G` is connected
--     (`idCompGL G = G`) iff `G` is irreducible.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpAReg

/-!
# S4-AlgGrpA, file IdComp: Zariski closures and identity components in `GL_n(K)`

* `zclosure H`: the Zariski closure of a subgroup `H ≤ GL_n(K)`, a Zariski closed subgroup.
* `idCompGL G`: the identity component of a subgroup `G` (for its subspace Zariski topology).
  For Zariski closed `G` it is closed, irreducible, normal and of finite index in `G`, open in
  `G`, contained in every closed subgroup of finite index of `G`, and it contains every
  irreducible subset of `G` through `1`; `G` is finite iff `idCompGL G = ⊥`, and `G` is connected
  (`idCompGL G = G`) iff `G` is irreducible.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.AlgGrpA

attribute [local instance] zarTop

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The Zariski closure of a subgroup of `GL_n(K)`, as a subgroup. -/
def zclosure (H : Subgroup (Matrix.GeneralLinearGroup n K)) :
    Subgroup (Matrix.GeneralLinearGroup n K) :=
  SemiTopGroup.closureSubgroup H

theorem coe_zclosure (H : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (zclosure H : Set (Matrix.GeneralLinearGroup n K)) = closure (H : Set _) := rfl

theorem le_zclosure (H : Subgroup (Matrix.GeneralLinearGroup n K)) : H ≤ zclosure H :=
  fun _ hx => subset_closure hx

theorem isClosed_zclosure (H : Subgroup (Matrix.GeneralLinearGroup n K)) :
    IsClosed (zclosure H : Set (Matrix.GeneralLinearGroup n K)) := isClosed_closure

theorem zclosure_le {H G : Subgroup (Matrix.GeneralLinearGroup n K)} (hHG : H ≤ G)
    (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n K))) : zclosure H ≤ G :=
  fun _ hx => closure_minimal (fun _ hy => hHG hy) hG hx

instance noetherianSpace_subgroup (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    TopologicalSpace.NoetherianSpace G :=
  TopologicalSpace.NoetherianSpace.set (G : Set (Matrix.GeneralLinearGroup n K))

/-- The identity component of `G ≤ GL_n(K)` for the Zariski topology of `G`. -/
def idCompGL (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    Subgroup (Matrix.GeneralLinearGroup n K) :=
  (SemiTopGroup.idComp G).map G.subtype

variable {G : Subgroup (Matrix.GeneralLinearGroup n K)}

theorem idCompGL_le (G : Subgroup (Matrix.GeneralLinearGroup n K)) : idCompGL G ≤ G :=
  Subgroup.map_subtype_le _

theorem coe_idCompGL (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (idCompGL G : Set (Matrix.GeneralLinearGroup n K)) =
      (Subtype.val : G → Matrix.GeneralLinearGroup n K) '' SemiTopGroup.G0 G :=
  Subgroup.coe_map _ _

theorem subgroupOf_idCompGL (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (idCompGL G).subgroupOf G = SemiTopGroup.idComp G :=
  Subgroup.comap_map_eq_self_of_injective G.subtype_injective _

theorem isClosed_idCompGL (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n K))) :
    IsClosed (idCompGL G : Set (Matrix.GeneralLinearGroup n K)) := by
  rw [coe_idCompGL]
  exact hG.isClosedMap_subtype_val _ SemiTopGroup.isClosed_G0

theorem isIrreducible_idCompGL (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    IsIrreducible (idCompGL G : Set (Matrix.GeneralLinearGroup n K)) := by
  rw [coe_idCompGL]
  exact SemiTopGroup.isIrreducible_G0.image _ continuous_subtype_val.continuousOn

instance idCompGL_normal (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    ((idCompGL G).subgroupOf G).Normal := by
  rw [subgroupOf_idCompGL]
  infer_instance

theorem conj_mem_idCompGL {g h : Matrix.GeneralLinearGroup n K} (hg : g ∈ G)
    (hh : h ∈ idCompGL G) : g * h * g⁻¹ ∈ idCompGL G := by
  have hhG := idCompGL_le G hh
  have h1 : (⟨h, hhG⟩ : G) ∈ (idCompGL G).subgroupOf G := Subgroup.mem_subgroupOf.2 hh
  have h2 := (idCompGL_normal G).conj_mem _ h1 ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 h2

instance idCompGL_finiteIndex (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    ((idCompGL G).subgroupOf G).FiniteIndex := by
  rw [subgroupOf_idCompGL]
  infer_instance

theorem isOpen_idCompGL_subgroupOf (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    IsOpen (((idCompGL G).subgroupOf G : Subgroup G) : Set G) := by
  rw [subgroupOf_idCompGL]
  exact SemiTopGroup.isOpen_idComp

/-- The identity component lies in every closed subgroup of finite index. -/
theorem idCompGL_le_of_finiteIndex {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K))) [(H.subgroupOf G).FiniteIndex] :
    idCompGL G ≤ H := by
  have hc : IsClosed ((H.subgroupOf G : Subgroup G) : Set G) := hH.preimage continuous_subtype_val
  have hle := SemiTopGroup.idComp_le_of_finiteIndex (H.subgroupOf G) hc
  rintro x ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (hle hy)

/-- `G` is finite iff its identity component is trivial. -/
theorem finite_iff_idCompGL_eq_bot (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    Finite G ↔ idCompGL G = ⊥ := by
  rw [SemiTopGroup.finite_iff_idComp_eq_bot, idCompGL]
  constructor
  · intro h
    rw [h]
    exact Subgroup.map_bot _
  · intro h
    rw [eq_bot_iff] at h ⊢
    intro x hx
    have := h ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 this))

/-- Every irreducible subset of `G` through `1` lies in the identity component. -/
theorem subset_idCompGL {S : Set (Matrix.GeneralLinearGroup n K)} (hS : IsIrreducible S)
    (h1 : (1 : Matrix.GeneralLinearGroup n K) ∈ S) (hSG : S ⊆ G) :
    S ⊆ idCompGL G := by
  have hT : IsIrreducible ((Subtype.val : G → Matrix.GeneralLinearGroup n K) ⁻¹' S) := by
    refine ⟨⟨1, h1⟩, ?_⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro A B hA hB hAB
    obtain ⟨A', hA', rfl⟩ := isClosed_induced_iff.1 hA
    obtain ⟨B', hB', rfl⟩ := isClosed_induced_iff.1 hB
    have hS' : S ⊆ A' ∪ B' := fun x hx =>
      hAB (show (⟨x, hSG hx⟩ : G) ∈ (Subtype.val ⁻¹' S) from hx)
    rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hS.isPreirreducible) A' B' hA' hB' hS'
      with h | h
    · exact Or.inl fun y hy => h hy
    · exact Or.inr fun y hy => h hy
  have hsub := SemiTopGroup.subset_G0 hT (show (1 : G) ∈ Subtype.val ⁻¹' S from h1)
  intro x hx
  exact ⟨⟨x, hSG hx⟩, hsub hx, rfl⟩

/-- `G` is connected (equal to its identity component) iff it is irreducible. -/
theorem idCompGL_eq_self_iff :
    idCompGL G = G ↔ IsIrreducible (G : Set (Matrix.GeneralLinearGroup n K)) := by
  constructor
  · intro h
    have := isIrreducible_idCompGL G
    rwa [h] at this
  · intro h
    exact le_antisymm (idCompGL_le G) (subset_idCompGL h G.one_mem fun _ hx => hx)

end RamanujanPetersson.AlgGrpA

end


