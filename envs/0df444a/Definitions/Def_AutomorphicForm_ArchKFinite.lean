-- Prove2me | Definitions.Def_AutomorphicForm_ArchKFinite
-- name    : AutomorphicForm_ArchKFinite
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/90141d44-83e6-5f1b-b07b-04e365c1a8a7
-- title:
--   Archimedean K-finiteness for functions on adelic GL2​
-- statement:
--   Three predicates are introduced. First, for a group $G$, a subgroup $K \le G$ and a function $f : G \to \mathbb{C}$, `RightTranslatesSpanFinite K f` asserts the existence of a finite family $s$ of functions $G \to \mathbb{C}$ such that for every $k \in K$ the right translate $x \mapsto f(xk)$ lies in the $\mathbb{C}$-linear span of $s$; note that the spanning family is an arbitrary finite set of functions, not required to consist of translates of $f$. Two elementary instances are recorded: constant functions satisfy this for any $K$ (with $s$ the singleton consisting of that constant), and every $f$ satisfies it for $K = \bot$.
--
--   Second, for a number field $F$ and an infinite place $w$, `archRowIsometrySubgroup F w` is the image in $\mathrm{GL}_2(\mathbb{A}_F)$, under the place-$w$ inclusion `adelicArchGLInclAt F w` (identity at all other archimedean components and at the finite part), of `rowIsometrySubgroup w.Completion`, the subgroup of those $k \in \mathrm{GL}_2(F_w)$ with $\|\det k\| = 1$ for which right multiplication by $k$ preserves $\|x\|^2 + \|y\|^2$ on row vectors $(x,y)$.
--
--   Third, `IsArchKFiniteAt F w φ` is `RightTranslatesSpanFinite` for this subgroup and a function $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, and `IsArchKFinite F φ` requires it at every infinite place $w$ simultaneously — a place-by-place condition rather than one formulated for the full product over the archimedean places. Constants, and in particular the zero function, are $K$-finite in this sense. The substantive inhabitant is `isArchKFinite_of_hasArchType`: if $\varphi$ transforms by a character $\chi_w$ of `rowIsometrySubgroup w.Completion` under right translation at each $w$, in the sense of `HasArchType F χ φ`, then all its translates lie in the line spanned by $\varphi$ itself.
--
--   **Relation to Mathlib.** The adele ring, infinite places and their completions are Mathlib's; the $K$-finiteness predicates, and the subgroups of norm-preserving matrices used in place of a maximal compact subgroup, are the project's own.
--
--   **Where it is used.** This is the archimedean finiteness condition entering the project's notion of an automorphic form on $\mathrm{GL}_2$ over a number field, alongside the invariance, central-character and growth or integrability conditions formulated in the neighbouring modules on $L^2$ and windowed Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchKFinite.lean

import Definitions.Def_AutomorphicForm_ArchType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section Generic

variable {G : Type*} [Group G]

def RightTranslatesSpanFinite (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ s : Finset (G → ℂ),
    ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))

theorem rightTranslatesSpanFinite_const (K : Subgroup G) (c : ℂ) :
    RightTranslatesSpanFinite K (fun _ : G => c) := by
  refine ⟨{fun _ => c}, fun k _hk => ?_⟩
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

theorem rightTranslatesSpanFinite_bot (f : G → ℂ) :
    RightTranslatesSpanFinite (⊥ : Subgroup G) f := by
  refine ⟨{f}, fun k hk => ?_⟩
  rw [Subgroup.mem_bot] at hk; subst hk
  have h1 : (fun x : G => f (x * 1)) = f := by funext x; rw [mul_one]
  rw [h1]
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

end Generic

section Arch

variable (F : Type) [Field F] [NumberField F]

def archRowIsometrySubgroup (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup w.Completion).map (adelicArchGLInclAt F w)

def IsArchKFiniteAt (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  RightTranslatesSpanFinite (archRowIsometrySubgroup F w) φ

def IsArchKFinite (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, IsArchKFiniteAt F w φ

theorem isArchKFinite_const (c : ℂ) : IsArchKFinite F (fun _ => c) :=
  fun w => rightTranslatesSpanFinite_const (archRowIsometrySubgroup F w) c

theorem isArchKFinite_zero : IsArchKFinite F (fun _ => (0 : ℂ)) := isArchKFinite_const F 0

theorem isArchKFinite_of_hasArchType
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : HasArchType F χ φ) :
    IsArchKFinite F φ := by
  intro w
  refine ⟨{φ}, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hχ : (fun x => φ (x * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)))
      = ((χ w ⟨k, hk⟩ : ℂˣ) : ℂ) • φ := by
    funext x
    exact hφ w ⟨k, hk⟩ x
  rw [hχ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _)))

end Arch

end AutomorphicForm


