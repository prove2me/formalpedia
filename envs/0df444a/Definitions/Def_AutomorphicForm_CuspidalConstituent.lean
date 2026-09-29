-- Prove2me | Definitions.Def_AutomorphicForm_CuspidalConstituent
-- name    : AutomorphicForm_CuspidalConstituent
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6ab1b1b7-6934-5db9-87ab-7cef8489eab0
-- title:
--   Cuspidal constituents in the adelic right regular representation
-- statement:
--   Throughout, $F$ is a number field, `pins` a `CarrierPins` datum for $F$ and $\xi : Z \to \mathbb{C}^\times$ a character of the central subgroup `pins.Z` attached to it. The basic operator is right translation, $(\mathtt{rightTranslate}\,g\,\varphi)(x) = \varphi(xg)$ on functions $GL_2(\mathbb{A}_F) \to \mathbb{C}$; `rightRegular` packages it as a Mathlib `Representation` of $GL_2(\mathbb{A}_F)$ on the full function space, and a group of routine lemmas records the composition law $R(g')R(g) = R(g'g)$, additivity, homogeneity, $R(g)0 = 0$, preservation of continuity, and the fact that the set of $\varphi$ all of whose translates satisfy `IsSmoothCuspAutomorphicFnAt` for $(\mathtt{pins},\xi)$ is itself translation-stable.
--
--   The ambient space `cuspKFiniteSubmodule` is the $\mathbb{C}$-span of those $\varphi$ that are continuous, satisfy the predicate `IsSmoothCuspAutomorphicFnAt` for $(\mathtt{pins},\xi)$ after every right translation, and lie in the archimedean cut `archCutSubmodule F tys` of some finite family of types `tys : ArchTypeFamily F` — that is, at every infinite place $w$ the function lies in the sum of the finitely many $K_w^{1}$-type submodules prescribed by `tys`, the types being taken along the inclusions `rowIsometryInclAt₀`. A further lemma shows this span is stable under translation by `rowIsometryInclAt₀ F v k`, the commutation of the inclusions at distinct places being what makes types at other places survive.
--
--   A `IsCuspSubrep` is a structure whose fields assert: $V \le$ `cuspKFiniteSubmodule`; $V$ is stable under right translation by elements of `finiteAdelicGL2Subgroup F`; $V$ is stable under right translation by `rowIsometryInclAt₀ F w k` for every infinite place $w$; and $V$ is stable under right convolution $\varphi \mapsto \mathtt{rightConv}\,\varphi\,f$, $(\varphi * f)(g) = \int \varphi(gx) f(x)\,dx$ against the adelic Haar measure, for every $f$ that is a factorizable test function (a product of a smooth compactly supported factor in the archimedean matrix entries with a locally constant compactly supported finite factor) and satisfies `IsArchBiFinite F tys f` for some `tys`, i.e. $x \mapsto f(x^{-1})$ lies in the archimedean cut and $f$ in the dual cut of `tys`. The last clause stands in for the action of the archimedean component. `IsCuspConstituent` asserts that $V$ is such a subrepresentation, is nonzero, and is minimal: every `IsCuspSubrep` $W \le V$ is $\bot$ or $V$. Linking these to Hecke data, `CuspConstituentMeets pins ξ N S Ψ V` asserts that $V$ contains a nonzero $\varphi$ with `IsIsotypicCuspFormAt` for the level $N$, exceptional set $S$ and eigensystem $\Psi$ (right $U(N)$-invariance, Hecke-coset eigenvalue $\Psi.a\,v$ and central eigenvalue $\Psi.b\,v$ outside $S$), and `cuspConstituentIsotypicCut` is the intersection $V \sqcap$ `isotypicCuspSubmodule`. Also defined is `levelInvariantSubmodule`, the submodule of functions invariant under right multiplication by `pins.U N`. Three closing facts: $\bot$ is a cusp subrepresentation; $\bot$ is not a cusp constituent; and if $V$ meets $(N,S,\Psi)$ then $V \sqcap$ `isotypicCuspSubmodule` $\ne \bot$.
--
--   **Relation to Mathlib.** `rightRegular` is an instance of Mathlib's `Representation` on the space of all complex-valued functions on the adelic group; Mathlib has no notion of cuspidal automorphic representation or of a constituent thereof, so `IsCuspSubrep`, `IsCuspConstituent` and the archimedean-type cuts are the project's own.
--
--   **Where it is used.** These definitions fix the grain at which cuspidal automorphic representations of $GL_2$ over a number field are handled: a constituent plays the role of the $K_\infty^{1}$-finite realisation of a single cuspidal representation with central character $\xi$, and `CuspConstituentMeets` is the link between such a constituent and a Hecke eigensystem of level $N$ with exceptional set $S$, which is the form in which modularity statements are used in the Frey–Serre–Ribet–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CuspidalConstituent.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace CuspidalConstituent

variable (F : Type) [Field F] [NumberField F]

def rightTranslate (g : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun x => φ (x * g)

theorem rightTranslate_apply (g x : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g φ x = φ (x * g) := rfl

def rightRegular : Representation ℂ (AdelicGL2 (𝓞 F) F) (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun g :=
    { toFun := rightTranslate F g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext φ x; simp [rightTranslate]
  map_mul' g h := by ext φ x; simp [rightTranslate, mul_assoc]

@[simp] theorem rightRegular_apply (g : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightRegular F g φ = rightTranslate F g φ := rfl

theorem rightTranslate_rightTranslate (g g' : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g' (rightTranslate F g φ) = rightTranslate F (g' * g) φ := by
  funext x; simp [rightTranslate, mul_assoc]

theorem rightTranslate_add (g : AdelicGL2 (𝓞 F) F) (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g (φ + ψ) = rightTranslate F g φ + rightTranslate F g ψ := rfl

theorem rightTranslate_smul (g : AdelicGL2 (𝓞 F) F) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g (c • φ) = c • rightTranslate F g φ := rfl

theorem rightTranslate_zero (g : AdelicGL2 (𝓞 F) F) : rightTranslate F g (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := rfl

theorem continuous_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F g φ) :=
  hφ.comp (continuous_mul_const g)

theorem forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F pins ξ (rightTranslate F g φ)) (g : AdelicGL2 (𝓞 F) F) :
    ∀ g' : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F pins ξ (rightTranslate F g' (rightTranslate F g φ)) := by
  intro g'; rw [rightTranslate_rightTranslate]; exact h _

theorem rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule (tys : ArchTypeFamily F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) (v : InfinitePlace F)
    (k : rowIsometrySubgroup₀ v.Completion) :
    rightTranslate F (rowIsometryInclAt₀ F v k) φ ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have key : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt F w (tys.rep w i)).map (rightRegular F (rowIsometryInclAt₀ F v k))
        ≤ archTypeSubmoduleAt F w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    by_cases hvw : v = w
    · subst hvw
      exact comp_mul_mem_typeSubmodule hf₀ k
    · refine comp_mul_mem_typeSubmodule_of_commute hf₀ _ fun k' => ?_
      rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
      exact commute_adelicArchGLInclAt_of_ne F hvw _ _
  have hmap : (⨆ i, archTypeSubmoduleAt F w (tys.rep w i)).map (rightRegular F (rowIsometryInclAt₀ F v k))
      ≤ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hφ w))

def cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ
    {φ | (∀ g : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F pins ξ (rightTranslate F g φ)) ∧
      Continuous φ ∧ ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys}

theorem rightTranslate_rowIsometryInclAt₀_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) (v : InfinitePlace F)
    (k : rowIsometrySubgroup₀ v.Completion) :
    rightTranslate F (rowIsometryInclAt₀ F v k) φ ∈ cuspKFiniteSubmodule F pins ξ := by
  refine Submodule.span_induction
    (p := fun φ _ => rightTranslate F (rowIsometryInclAt₀ F v k) φ ∈ cuspKFiniteSubmodule F pins ξ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, tys, htys⟩
    exact Submodule.subset_span ⟨forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate F hsat _,
      continuous_rightTranslate F hcont _, tys, rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule F tys htys v k⟩
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact (cuspKFiniteSubmodule F pins ξ).zero_mem
  · intro u w _ _ hu hw
    show rightTranslate F _ (u + w) ∈ _
    rw [rightTranslate_add]; exact (cuspKFiniteSubmodule F pins ξ).add_mem hu hw
  · intro c u _ hu
    show rightTranslate F _ (c • u) ∈ _
    rw [rightTranslate_smul]; exact (cuspKFiniteSubmodule F pins ξ).smul_mem c hu

structure IsCuspSubrep (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop where
  le : V ≤ cuspKFiniteSubmodule F pins ξ
  rightTranslate_fin_mem : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ φ ∈ V, rightTranslate F g φ ∈ V
  rightTranslate_arch_mem : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
    ∀ φ ∈ V, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ V
  rightConv_mem : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
    IsFactorizableTestFn F f → IsArchBiFinite F tys f → ∀ φ ∈ V, rightConv F φ f ∈ V

def IsCuspConstituent (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop :=
  IsCuspSubrep F pins ξ V ∧ V ≠ ⊥ ∧
    ∀ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), IsCuspSubrep F pins ξ W → W ≤ V → W = ⊥ ∨ W = V

def CuspConstituentMeets (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop :=
  ∃ φ ∈ V, φ ≠ 0 ∧ IsIsotypicCuspFormAt F pins ξ N S Ψ φ

def cuspConstituentIsotypicCut (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ

def levelInvariantSubmodule (pins : CarrierPins F) (N : Ideal (𝓞 F)) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U N, φ (g * u) = φ g}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {a b} ha hb g u hu => by simp only [Pi.add_apply, ha g u hu, hb g u hu]
  smul_mem' := fun c {a} ha g u hu => by simp only [Pi.smul_apply, ha g u hu]

theorem isCuspSubrep_bot (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsCuspSubrep F pins ξ ⊥ :=
  ⟨bot_le, fun g _ φ hφ => by rw [(Submodule.mem_bot ℂ).mp hφ]; exact Submodule.zero_mem _,
    fun w k φ hφ => by rw [(Submodule.mem_bot ℂ).mp hφ]; exact Submodule.zero_mem _,
    fun f _ _ _ φ hφ => by
      rw [(Submodule.mem_bot ℂ).mp hφ]
      exact (Submodule.mem_bot ℂ).mpr (rightConv_zero_left F f)⟩

theorem not_isCuspConstituent_bot (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    ¬ IsCuspConstituent F pins ξ ⊥ := fun h => h.2.1 rfl

theorem inf_isotypicCuspSubmodule_ne_bot_of_cuspConstituentMeets {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (h : CuspConstituentMeets F pins ξ N S Ψ V) :
    V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ ≠ ⊥ := by
  obtain ⟨φ, hφV, hφ0, hφ⟩ := h
  intro hbot
  have : φ ∈ V ⊓ isotypicCuspSubmodule F pins ξ N S Ψ := ⟨hφV, hφ.mem_isotypicCuspSubmodule⟩
  rw [hbot, Submodule.mem_bot] at this
  exact hφ0 this

end CuspidalConstituent

end AutomorphicForm

end


