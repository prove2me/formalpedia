-- Prove2me | Definitions.Def_AutomorphicForm_ArchWeightCharTransport
-- name    : AutomorphicForm_ArchWeightCharTransport
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6ef00124-49f4-5600-8deb-2738c1b76648
-- title:
--   Transporting archimedean weight characters to real places
-- statement:
--   Let $K, L$ be normed fields. From a ring equivalence $e : K \simeq L$ the module builds `glEquivOfRingEquiv`, the multiplicative equivalence $GL_2(K) \simeq GL_2(L)$ obtained by applying $e$ entrywise (`RingEquiv.mapMatrix` pushed through `Units.mapEquiv`); `glEquivOfRingEquiv_apply_entry` records that its matrix entries are $e(k_{ij})$. If in addition $e$ preserves norms, `map_mem_rowIsometrySubgroup₀_of_normPreserving` shows that it carries the project's subgroup `rowIsometrySubgroup₀ K` into `rowIsometrySubgroup₀ L`; the membership criterion used is $\det k = 1$, $\|\det k\| = 1$, and the row-isometry identity $\|xk_{00}+yk_{10}\|^2 + \|xk_{01}+yk_{11}\|^2 = \|x\|^2+\|y\|^2$ for all $x,y$ (the subgroup itself is defined in the imported module). This gives the monoid homomorphism `rowIsometrySubgroup₀Map e he`, and `rowIsometrySubgroup₀Map_weyl` says it sends the distinguished Weyl element to the Weyl element.
--
--   For a number field $F$ and a real infinite place $w$, `norm_ringEquivRealOfIsReal` checks that Mathlib's isomorphism $F_w \simeq \mathbb{R}$ is norm-preserving, so transporting along it and composing with the project's character `archWeightOneℝ` yields `archWeightOneAt hw` : $\mathrm{rowIsometrySubgroup₀}(F_w) \to \mathbb{C}^\times$; `archWeightCharAt hw n` is its $n$-th power for $n \in \mathbb{Z}$ (via `zpowGroupHom n`). Non-triviality is recorded twice: the Weyl element is not sent to $1$ (`archWeightOneAt_weyl_ne_one`), hence the character is not trivial (`archWeightOneAt_ne_one`).
--
--   Finally `archWeightCharFamily F n` is the family indexed by all infinite places of $F$ given by a case split: `archWeightCharAt hw n` at real places and the trivial character at complex places, with the two computation lemmas `archWeightCharFamily_apply_of_isReal` and `_of_isComplex`. An `example` notes that the zero function satisfies `HasArchType₀ F (archWeightCharFamily F 1)`, and `archWeightCharFamily_rat_one_ne_one` instantiates non-triviality at the unique place of $\mathbb{Q}$.
--
--   **Relation to Mathlib.** Built on Mathlib's `NumberField.InfinitePlace`, its completions and `ringEquivRealOfIsReal`, and on `RingEquiv.mapMatrix`/`Units.mapEquiv`; the subgroup `rowIsometrySubgroup₀`, the character `archWeightOneℝ` and the predicate `HasArchType₀` are the project's own notions, defined in the imported module.
--
--   **Where it is used.** These families of characters of the determinant-one row-isometry subgroups at the archimedean places supply the archimedean weight condition used in the project's predicate for automorphic forms of a given weight; `archWeightCharFamily F 1` is what the weight-one clause of the arithmetic cuspidal realisation predicate refers to.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchWeightCharTransport.lean

import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Classical

namespace AutomorphicForm

section Furniture

variable {K L : Type*} [NormedField K] [NormedField L]

noncomputable def glEquivOfRingEquiv (e : K ≃+* L) : GL (Fin 2) K ≃* GL (Fin 2) L :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) e).toMulEquiv

theorem glEquivOfRingEquiv_apply_entry (e : K ≃+* L) (k : GL (Fin 2) K) (i j : Fin 2) :
    ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
      = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem map_mem_rowIsometrySubgroup₀_of_normPreserving (e : K ≃+* L)
    (he : ∀ x : K, ‖e x‖ = ‖x‖) (k : GL (Fin 2) K)
    (hk : k ∈ rowIsometrySubgroup₀ K) :
    glEquivOfRingEquiv e k ∈ rowIsometrySubgroup₀ L := by
  obtain ⟨hd, hnd, hiso⟩ := (mem_rowIsometrySubgroup₀_iff K).mp hk
  have hdL : ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
    change (RingEquiv.mapMatrix (m := Fin 2) e (k : Matrix (Fin 2) (Fin 2) K)).det = 1
    rw [← RingEquiv.map_det, hd, map_one]
  refine (mem_rowIsometrySubgroup₀_iff L).mpr ⟨hdL, ?_, ?_⟩
  · rw [hdL]; exact norm_one
  · intro x y
    have hes : ∀ z : L, ‖e.symm z‖ = ‖z‖ := fun z => by
      rw [← he (e.symm z), e.apply_symm_apply]
    have hent : ∀ i j, ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix _ _ L) i j
        = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
    simp only [hent]
    calc ‖x * e (k 0 0) + y * e (k 1 0)‖ ^ 2 + ‖x * e (k 0 1) + y * e (k 1 1)‖ ^ 2
        = ‖e (e.symm x * k 0 0 + e.symm y * k 1 0)‖ ^ 2
          + ‖e (e.symm x * k 0 1 + e.symm y * k 1 1)‖ ^ 2 := by
          simp only [map_add, map_mul, e.apply_symm_apply]
      _ = ‖e.symm x * k 0 0 + e.symm y * k 1 0‖ ^ 2
          + ‖e.symm x * k 0 1 + e.symm y * k 1 1‖ ^ 2 := by rw [he, he]
      _ = ‖e.symm x‖ ^ 2 + ‖e.symm y‖ ^ 2 := hiso (e.symm x) (e.symm y)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [hes, hes]

noncomputable def rowIsometrySubgroup₀Map (e : K ≃+* L)
    (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    rowIsometrySubgroup₀ K →* rowIsometrySubgroup₀ L where
  toFun k := ⟨glEquivOfRingEquiv e k, map_mem_rowIsometrySubgroup₀_of_normPreserving e he k k.2⟩
  map_one' := by ext; simp [glEquivOfRingEquiv]
  map_mul' k k' := by ext; simp [glEquivOfRingEquiv]

theorem rowIsometrySubgroup₀Map_weyl (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    rowIsometrySubgroup₀Map e he ⟨_, weyl_mem_rowIsometrySubgroup₀ K⟩
      = ⟨_, weyl_mem_rowIsometrySubgroup₀ L⟩ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_zero, map_one, map_neg]

end Furniture

section RealPlace

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem norm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖ringEquivRealOfIsReal hw x‖ = ‖x‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x

noncomputable def archWeightOneAt {w : InfinitePlace F} (hw : w.IsReal) :
    rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  archWeightOneℝ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
    (norm_ringEquivRealOfIsReal hw))

noncomputable def archWeightCharAt {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ) :
    rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  (zpowGroupHom n).comp (archWeightOneAt hw)

omit [NumberField F] in

theorem archWeightOneAt_weyl_ne_one {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightOneAt hw ⟨_, weyl_mem_rowIsometrySubgroup₀ w.Completion⟩ ≠ 1 := by
  unfold archWeightOneAt
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_weyl]
  exact archWeightOneℝ_ne_one

omit [NumberField F] in

theorem archWeightOneAt_ne_one {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightOneAt hw ≠ 1 := fun h =>
  archWeightOneAt_weyl_ne_one hw (h ▸ rfl)

end RealPlace

section Family

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

noncomputable def archWeightCharFamily (n : ℤ) :
    ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  fun w => if hw : w.IsReal then archWeightCharAt hw n else 1

omit [NumberField F] in
theorem archWeightCharFamily_apply_of_isReal (n : ℤ) {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightCharFamily F n w = archWeightCharAt hw n := dif_pos hw

omit [NumberField F] in
theorem archWeightCharFamily_apply_of_isComplex (n : ℤ) {w : InfinitePlace F}
    (hw : w.IsComplex) : archWeightCharFamily F n w = 1 :=
  dif_neg (by rwa [← not_isReal_iff_isComplex] at hw)

example : HasArchType₀ F (archWeightCharFamily F 1) (fun _ => 0) :=
  hasArchType₀_zero F (archWeightCharFamily F 1)

theorem archWeightCharFamily_rat_one_ne_one :
    archWeightCharFamily ℚ 1 Rat.infinitePlace ≠ 1 := by
  rw [archWeightCharFamily_apply_of_isReal ℚ 1 Rat.isReal_infinitePlace]
  intro h
  have := DFunLike.congr_fun h ⟨_, weyl_mem_rowIsometrySubgroup₀ _⟩
  simp only [archWeightCharAt, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_one,
    MonoidHom.one_apply] at this
  exact archWeightOneAt_weyl_ne_one Rat.isReal_infinitePlace this

end Family

end AutomorphicForm


