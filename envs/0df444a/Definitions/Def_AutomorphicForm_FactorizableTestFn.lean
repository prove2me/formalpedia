-- Prove2me | Definitions.Def_AutomorphicForm_FactorizableTestFn
-- name    : AutomorphicForm_FactorizableTestFn
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0083b097-ca30-5323-9056-05de7eda010f
-- title:
--   Factorizable test functions on adelic GL2​
-- statement:
--   Let $F$ be a field, later a number field, with adele ring $\mathbb{A}_F = F_\infty \times \mathbb{A}_F^{\mathrm{f}}$ written in Lean as a product of `InfiniteAdeleRing F` and `FiniteAdeleRing (𝓞 F) F`, and let `AdelicLevel.glArch` and `AdelicLevel.glFin` be the group homomorphisms $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(F_\infty)$ and $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}})$ obtained by applying the two coordinate projections entrywise. First, `archEntries F g` records the four entries of $g \in \mathrm{GL}_2(F_\infty)$ transported into the mixed space $\prod_{w \text{ real}} \mathbb{R} \times \prod_{w \text{ complex}} \mathbb{C}$ along `InfiniteAdeleRing.ringEquiv_mixedSpace`, as a function $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to$ mixed space; `archEntries_apply` states this entrywise description.
--
--   Three predicates are then defined. `IsArchTestFactor F fa`, for $fa : \mathrm{GL}_2(F_\infty) \to \mathbb{C}$, asserts two things: that there exists $\Phi$ on the space of $2 \times 2$ matrices over the mixed space which is $C^\infty$ as a map of real vector spaces and satisfies $fa(g) = \Phi(\mathrm{archEntries}\,F\,g)$ for all $g$; and that $fa$ has compact support. Thus smoothness is formulated as smoothness of a chosen extension in the matrix entries. `IsFinTestFactor F ff`, for $ff$ on $\mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}})$, asserts that $ff$ is locally constant and has compact support. `IsFactorizableTestFn F f`, for $f$ on $\mathrm{GL}_2(\mathbb{A}_F)$, asserts the existence of an archimedean test factor $fa$ and a finite test factor $ff$ with $f(g) = fa(g_\infty)\, ff(g_{\mathrm{f}})$ for every $g$, the components being taken via `glArch` and `glFin`.
--
--   The remaining declarations record that the zero function belongs to each of the three classes, and that any function factoring in this way vanishes at $g$ as soon as one of the two factors vanishes at the corresponding component of $g$.
--
--   **Relation to Mathlib.** Smoothness (`ContDiff`), local constancy (`IsLocallyConstant`), compact support (`HasCompactSupport`) and the adele rings are Mathlib's; the classes of archimedean, finite and factorizable test functions on adelic $\mathrm{GL}_2$ are the project's own.
--
--   **Where it is used.** These classes provide the test functions used in the project's adelic analysis on $\mathrm{GL}_2$, where convolution operators and automorphic kernels $\sum_\gamma f(x^{-1}\gamma y)$ are built from a smooth compactly supported archimedean factor and a locally constant compactly supported factor at the finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_FactorizableTestFn.lean

import Definitions.Def_NumberField_AdelicLevel
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.LocallyConstant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

noncomputable section

open scoped Classical

namespace AutomorphicForm

variable (F : Type) [Field F]

def archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)

theorem archEntries_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2) :
    archEntries F g i j = InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) :=
  rfl

variable [NumberField F]

def IsArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  (∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, fa g = Φ (archEntries F g)) ∧
    HasCompactSupport fa

theorem isArchTestFactor_zero : IsArchTestFactor F (fun _ => 0) :=
  ⟨⟨fun _ => 0, contDiff_const, fun _ => rfl⟩, HasCompactSupport.zero⟩

def IsFinTestFactor (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  IsLocallyConstant ff ∧ HasCompactSupport ff

def IsFactorizableTestFn (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
    IsArchTestFactor F fa ∧ IsFinTestFactor F ff ∧
      ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g)

theorem isFinTestFactor_zero : IsFinTestFactor F (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isFactorizableTestFn_zero : IsFactorizableTestFn F (fun _ => 0) :=
  ⟨fun _ => 0, fun _ => 0, isArchTestFactor_zero F, isFinTestFactor_zero F,
    fun _ => (mul_zero _).symm⟩

theorem IsFactorizableTestFn.eq_zero_of_glArch {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : fa (AdelicLevel.glArch (𝓞 F) F g) = 0) :
    f g = 0 := by
  rw [hf g, hg, zero_mul]

theorem IsFactorizableTestFn.eq_zero_of_glFin {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : ff (AdelicLevel.glFin (𝓞 F) F g) = 0) :
    f g = 0 := by
  rw [hf g, hg, mul_zero]

end AutomorphicForm

end


