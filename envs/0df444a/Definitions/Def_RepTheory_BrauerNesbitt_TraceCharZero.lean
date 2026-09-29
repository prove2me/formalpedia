-- Prove2me | Definitions.Def_RepTheory_BrauerNesbitt_TraceCharZero
-- name    : RepTheory_BrauerNesbitt_TraceCharZero
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/71982a75-8549-56cf-ae3a-9dac1303e6cb
-- title:
--   Trace characters and Brauer–Nesbitt in characteristic zero
-- statement:
--   For a commutative base $k$, a $k$-algebra $A$ and a module $M$ carrying compatible $k$- and $A$-actions (a scalar tower), `actionEndo k A M a` is the $k$-linear endomorphism $x \mapsto a \cdot x$ of $M$; `actionEndoHom` assembles these into a $k$-linear map $A \to \operatorname{End}_k(M)$, and `actionTrace k A M` is that map followed by Mathlib's $k$-linear trace, i.e. the trace character $a \mapsto \operatorname{tr}_k(a \mid M)$ as a $k$-linear functional on $A$. Around these the module collects the standard transport properties: the trace of the action is invariant under an $A$-linear equivalence, the action on a product is the product map of the actions, and the trace over $M$ splits as the sum of the traces over two complementary $A$-submodules that are finite-dimensional over $k$.
--
--   The substance is the characteristic-zero Brauer–Nesbitt theorem for trace characters. First, for a semisimple $A$-module $P$, finite-dimensional over a field $k$, and complementary fully invariant $A$-submodules $C, C'$, some $a \in A$ acts on $P$ exactly as the projection onto $C$ along $C'$ (Jacobson density). For such an $a$, the trace of the action on any $A$-submodule $W \le P$ equals the $k$-dimension of $W \cap C$, viewed in $k$. Counting these dimensions on the isotypic decomposition of $M \times N$ gives: if the trace characters of $M$ and $N$ agree, every simple $A$-submodule of $M$ is $A$-isomorphic to a submodule of $N$. An induction on $\dim_k M$ then yields the headline `nonempty_linearEquiv_of_actionTrace_eq`: over a field $k$ of characteristic zero, two semisimple $A$-modules, finite-dimensional over $k$ and possibly in different universes, with equal trace characters are $A$-isomorphic. A final section specialises this to $A = \mathrm{MonoidAlgebra}\,k\,G$, where equality of traces on the group-like elements $g \in G$ already suffices.
--
--   **Relation to Mathlib.** Mathlib's semisimplicity API (`IsSemisimpleModule`, isotypic components, fully invariant submodules, `jacobson_density`) and `LinearMap.trace` are used as given; the trace character `actionTrace` of a module over a $k$-algebra and the Brauer–Nesbitt conclusion drawn from it are the project's own additions.
--
--   **Where it is used.** The result is the characteristic-zero trace route to Brauer–Nesbitt, the companion of a characteristic-free version proved via characteristic polynomials; such statements are what allow two semisimple representations to be identified once their traces (equivalently, characters of Frobenius elements) agree, as is needed when comparing semisimplified Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_BrauerNesbitt_TraceCharZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module LinearMap

noncomputable section

namespace BrauerNesbitt

section ActionEndo

variable (k : Type*) [CommSemiring k]
variable (A : Type*) [Semiring A] [Algebra k A]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]

def actionEndo (a : A) : M →ₗ[k] M where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' c x := smul_comm a c x

@[simp] theorem actionEndo_apply (a : A) (x : M) : actionEndo k A M a x = a • x := rfl

theorem actionEndo_add (a b : A) :
    actionEndo k A M (a + b) = actionEndo k A M a + actionEndo k A M b := by
  ext x; simp [add_smul]

theorem actionEndo_smul (c : k) (a : A) :
    actionEndo k A M (c • a) = c • actionEndo k A M a := by
  ext x; simp [smul_assoc]

theorem actionEndo_one : actionEndo k A M (1 : A) = LinearMap.id := by
  ext x; simp

def actionEndoHom : A →ₗ[k] (M →ₗ[k] M) where
  toFun := actionEndo k A M
  map_add' := actionEndo_add k A M
  map_smul' c a := actionEndo_smul k A M c a

@[simp] theorem actionEndoHom_apply (a : A) : actionEndoHom k A M a = actionEndo k A M a := rfl

def actionTrace : A →ₗ[k] k :=
  (LinearMap.trace k M) ∘ₗ actionEndoHom k A M

@[simp] theorem actionTrace_apply (a : A) :
    actionTrace k A M a = LinearMap.trace k M (actionEndo k A M a) := rfl

end ActionEndo

section Transport

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]

theorem trace_actionEndo_eq_of_linearEquiv
    {M₁ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A M₁] [IsScalarTower k A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module k M₂] [Module A M₂] [IsScalarTower k A M₂]
    (e : M₁ ≃ₗ[A] M₂) (a : A) :
    LinearMap.trace k M₁ (actionEndo k A M₁ a) = LinearMap.trace k M₂ (actionEndo k A M₂ a) := by
  have h : (e.restrictScalars k).conj (actionEndo k A M₁ a) = actionEndo k A M₂ a := by
    ext x
    simp [LinearEquiv.conj_apply, map_smul]
  rw [← h, LinearMap.trace_conj']

theorem actionEndo_prod
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] (a : A) :
    actionEndo k A (M × N) a = (actionEndo k A M a).prodMap (actionEndo k A N a) := by
  ext x <;> simp

theorem trace_actionEndo_eq_add_of_isCompl
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {p q : Submodule A M} [Module.Finite k ↥p] [Module.Finite k ↥q]
    (h : IsCompl p q) (a : A) :
    LinearMap.trace k M (actionEndo k A M a)
      = LinearMap.trace k ↥p (actionEndo k A ↥p a)
        + LinearMap.trace k ↥q (actionEndo k A ↥q a) := by
  rw [← trace_actionEndo_eq_of_linearEquiv (Submodule.prodEquivOfIsCompl p q h) a,
    actionEndo_prod, LinearMap.trace_prodMap']

end Transport

section Density

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

theorem exists_smul_eq_projection [IsSemisimpleModule A P] [Module.Finite k P]
    {C C' : Submodule A P} (hC : C.IsFullyInvariant) (hC' : C'.IsFullyInvariant)
    (hcompl : IsCompl C C') :
    ∃ a : A, ∀ x : P, a • x = C.projection C' hcompl x := by
  classical
  set π : P →ₗ[A] P := C.projection C' hcompl with hπ

  have hcomm : ∀ (φ : Module.End A P) (x : P), π (φ x) = φ (π x) := by
    intro φ x
    obtain ⟨c, hc, c', hc', rfl⟩ : ∃ c ∈ C, ∃ c' ∈ C', x = c + c' := by
      have hx : x ∈ C ⊔ C' := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨c, hc, c', hc', hx⟩ := Submodule.mem_sup.mp hx
      exact ⟨c, hc, c', hc', hx.symm⟩
    have hπc : π c = c := Submodule.projection_apply_left hcompl ⟨c, hc⟩
    have hπc' : π c' = 0 := (Submodule.projection_apply_eq_zero_iff hcompl).mpr hc'
    have hφc : φ c ∈ C := hC φ hc
    have hφc' : φ c' ∈ C' := hC' φ hc'
    have hπφc : π (φ c) = φ c := Submodule.projection_apply_left hcompl ⟨φ c, hφc⟩
    have hπφc' : π (φ c') = 0 := (Submodule.projection_apply_eq_zero_iff hcompl).mpr hφc'
    calc π (φ (c + c')) = π (φ c) + π (φ c') := by rw [map_add φ, map_add π]
      _ = φ c := by rw [hπφc, hπφc', add_zero]
      _ = φ (π (c + c')) := by rw [map_add π, hπc, hπc', add_zero]
  let f : P →ₗ[Module.End A P] P :=
    { toFun := fun x => π x
      map_add' := fun x y => map_add π x y
      map_smul' := fun φ x => by
        simp only [Module.End.smul_def, RingHom.id_apply]
        exact hcomm φ x }

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := P)
  obtain ⟨a, ha⟩ := jacobson_density (R := A) (M := P) f s
  refine ⟨a, fun x => ?_⟩

  have hmaps : actionEndo k A P a = π.restrictScalars k := by
    refine LinearMap.ext_on hs fun y hy => ?_
    have h1 : π y = a • y := ha y hy
    simpa using h1.symm
  have h2 := congrArg (fun (g : P →ₗ[k] P) => g x) hmaps
  simpa using h2

end Density

section ProjectionTrace

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

theorem finiteDimensional_coe_submodule [FiniteDimensional k P] (W : Submodule A P) :
    FiniteDimensional k ↥W :=
  FiniteDimensional.of_injective ((W.subtype).restrictScalars k) (Submodule.injective_subtype W)

theorem trace_actionEndo_eq_finrank_comap [FiniteDimensional k P]
    {C C' : Submodule A P} (hcompl : IsCompl C C') {a : A}
    (ha : ∀ x : P, a • x = C.projection C' hcompl x) (W : Submodule A P) :
    LinearMap.trace k ↥W (actionEndo k A ↥W a)
      = (finrank k ↥((C.restrictScalars k).comap ((W.subtype).restrictScalars k)) : k) := by
  haveI : FiniteDimensional k ↥W := finiteDimensional_coe_submodule W
  set p : Submodule k ↥W := (C.restrictScalars k).comap ((W.subtype).restrictScalars k) with hp
  have hmem : ∀ x : ↥W, x ∈ p ↔ (x : P) ∈ C := by
    intro x
    rw [hp, Submodule.mem_comap]
    simp
  have hcoe : ∀ x : ↥W, ((a • x : ↥W) : P) = a • (x : P) := fun x => rfl
  have hproj : LinearMap.IsProj p (actionEndo k A ↥W a) := by
    constructor
    · intro x
      rw [hmem, actionEndo_apply, hcoe, ha]
      exact Submodule.projection_apply_mem hcompl _
    · intro x hx
      rw [hmem] at hx
      have h1 : a • (x : P) = (x : P) := by
        rw [ha]
        exact Submodule.projection_apply_left hcompl ⟨(x : P), hx⟩
      rw [actionEndo_apply]
      exact Subtype.ext (by rw [hcoe, h1])
  exact hproj.trace

private theorem finrank_comap_pos_of_mem (W C : Submodule A P) [FiniteDimensional k ↥W]
    {v : P} (hvW : v ∈ W) (hvC : v ∈ C) (hvne : v ≠ 0) :
    0 < finrank k ↥((C.restrictScalars k).comap ((W.subtype).restrictScalars k)) := by
  set w : ↥((C.restrictScalars k).comap ((W.subtype).restrictScalars k)) :=
    ⟨⟨v, hvW⟩, by rw [Submodule.mem_comap]; simpa using hvC⟩ with hw
  have hwne : w ≠ 0 := by
    intro h0
    apply hvne
    have h1 : ((w : ↥W) : P) = 0 := by rw [h0]; rfl
    exact h1
  haveI : Nontrivial ↥((C.restrictScalars k).comap ((W.subtype).restrictScalars k)) :=
    nontrivial_of_ne w 0 hwne
  exact (Module.finrank_pos_iff_of_free k _).mpr inferInstance

end ProjectionTrace

section Comparison

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

theorem isSemisimpleModule_prod [IsSemisimpleModule A M] [IsSemisimpleModule A N] :
    IsSemisimpleModule A (M × N) := by
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := Bool.rec (LinearMap.range (LinearMap.inr A M N)) (LinearMap.range (LinearMap.inl A M N)))
    (fun b => ?_) ?_
  · cases b with
    | true =>
      exact IsSemisimpleModule.congr
        (LinearEquiv.ofInjective (LinearMap.inl A M N) LinearMap.inl_injective).symm
    | false =>
      exact IsSemisimpleModule.congr
        (LinearEquiv.ofInjective (LinearMap.inr A M N) LinearMap.inr_injective).symm
  · rw [iSup_bool_eq]
    exact LinearMap.sup_range_inl_inr

theorem exists_linearEquiv_simple_of_actionTrace_eq [CharZero k]
    [IsSemisimpleModule A M] [IsSemisimpleModule A N]
    [FiniteDimensional k M] [FiniteDimensional k N]
    (htr : ∀ a : A, actionTrace k A M a = actionTrace k A N a)
    (S : Submodule A M) [hS : IsSimpleModule A ↥S] :
    ∃ T : Submodule A N, Nonempty (↥S ≃ₗ[A] ↥T) := by
  classical
  by_contra hcon
  haveI : IsSemisimpleModule A (M × N) := isSemisimpleModule_prod

  set M' : Submodule A (M × N) := LinearMap.range (LinearMap.inl A M N) with hM'
  set N' : Submodule A (M × N) := LinearMap.range (LinearMap.inr A M N) with hN'
  have eM : M ≃ₗ[A] ↥M' := LinearEquiv.ofInjective (LinearMap.inl A M N) LinearMap.inl_injective
  have eN : N ≃ₗ[A] ↥N' := LinearEquiv.ofInjective (LinearMap.inr A M N) LinearMap.inr_injective

  set S₁ : Submodule A (M × N) := S.map (LinearMap.inl A M N) with hS₁
  have eS₁ : ↥S ≃ₗ[A] ↥S₁ :=
    Submodule.equivMapOfInjective (LinearMap.inl A M N) LinearMap.inl_injective S
  haveI hS₁simple : IsSimpleModule A ↥S₁ := IsSimpleModule.congr eS₁.symm
  set C : Submodule A (M × N) := isotypicComponent A (M × N) S₁ with hC
  have hCmem : C ∈ isotypicComponents A (M × N) := ⟨S₁, hS₁simple, hC⟩
  set C' : Submodule A (M × N) := sSup (isotypicComponents A (M × N) \ {C}) with hC'

  have hdisj : Disjoint C C' := sSupIndep_isotypicComponents A (M × N) hCmem
  have hcodisj : Codisjoint C C' := by
    rw [codisjoint_iff_le_sup, ← sSup_isotypicComponents A (M × N)]
    refine sSup_le fun x hx => ?_
    by_cases hxC : x = C
    · exact hxC.le.trans le_sup_left
    · exact le_sup_of_le_right (le_sSup ⟨hx, hxC⟩)
  have hcompl : IsCompl C C' := ⟨hdisj, hcodisj⟩
  have hCfi : C.IsFullyInvariant := Submodule.IsFullyInvariant.isotypicComponent A (M × N) S₁
  have hC'fi : C'.IsFullyInvariant :=
    (fullyInvariantSubmodule A (M × N)).sSupClosed
      (fun x hx => Submodule.IsFullyInvariant.of_mem_isotypicComponents hx.1)

  obtain ⟨a, ha⟩ := exists_smul_eq_projection (k := k) hCfi hC'fi hcompl

  have htraceM : LinearMap.trace k M (actionEndo k A M a)
      = (finrank k ↥((C.restrictScalars k).comap ((M'.subtype).restrictScalars k)) : k) := by
    rw [trace_actionEndo_eq_of_linearEquiv eM a]
    exact trace_actionEndo_eq_finrank_comap hcompl ha M'
  have htraceN : LinearMap.trace k N (actionEndo k A N a)
      = (finrank k ↥((C.restrictScalars k).comap ((N'.subtype).restrictScalars k)) : k) := by
    rw [trace_actionEndo_eq_of_linearEquiv eN a]
    exact trace_actionEndo_eq_finrank_comap hcompl ha N'

  have hNbot : (C.restrictScalars k).comap ((N'.subtype).restrictScalars k) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_comap] at hx
    have hxC : (x : M × N) ∈ C := by simpa using hx
    by_contra hxne

    have hmemNC : (x : M × N) ∈ N' ⊓ C := Submodule.mem_inf.mpr ⟨x.2, hxC⟩
    have hne : N' ⊓ C ≠ ⊥ := by
      intro hbot
      apply hxne
      have hx0 : (x : M × N) ∈ (⊥ : Submodule A (M × N)) := hbot ▸ hmemNC
      have : (x : M × N) = 0 := by simpa using hx0
      exact Subtype.ext this

    obtain ⟨T', hT'le, hT'simple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le (N' ⊓ C)).resolve_left hne
    haveI := hT'simple
    have hT'C : T' ≤ C := hT'le.trans inf_le_right
    have hT'N' : T' ≤ N' := hT'le.trans inf_le_left

    have hT'S₁ : Nonempty (↥T' ≃ₗ[A] ↥S₁) :=
      isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent A (M × N) S₁) T' hT'C

    set T : Submodule A N := T'.comap (LinearMap.inr A M N) with hT
    have hmapT : T.map (LinearMap.inr A M N) = T' := by
      rw [hT, Submodule.map_comap_eq]
      exact inf_eq_right.mpr hT'N'
    have eT : ↥T ≃ₗ[A] ↥T' :=
      (Submodule.equivMapOfInjective (LinearMap.inr A M N) LinearMap.inr_injective T).trans
        (LinearEquiv.ofEq _ _ hmapT)
    exact hcon ⟨T, ⟨eS₁.trans (hT'S₁.some.symm.trans eT.symm)⟩⟩

  haveI : FiniteDimensional k ↥M' := finiteDimensional_coe_submodule M'
  have hMpos : 0 < finrank k ↥((C.restrictScalars k).comap ((M'.subtype).restrictScalars k)) := by
    have hS₁M' : S₁ ≤ M' := by
      rw [hS₁, hM']
      intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact LinearMap.mem_range_self _ y
    have hS₁C : S₁ ≤ C := Submodule.le_isotypicComponent S₁

    haveI : Nontrivial ↥S₁ := IsSimpleModule.nontrivial A ↥S₁
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥S₁)
    exact finrank_comap_pos_of_mem M' C (hS₁M' v.2) (hS₁C v.2)
      (fun h => hv (Subtype.ext h))

  have hcontr := htr a
  rw [actionTrace_apply, actionTrace_apply, htraceM, htraceN, hNbot, finrank_bot,
    Nat.cast_zero] at hcontr
  have h0 : finrank k ↥((C.restrictScalars k).comap ((M'.subtype).restrictScalars k)) = 0 :=
    Nat.cast_eq_zero.mp hcontr
  omega

end Comparison

section Headline

universe vM vN

variable {k : Type*} [Field k] [CharZero k]
variable {A : Type*} [Ring A] [Algebra k A]

private theorem nonempty_linearEquiv_of_subsingleton
    {M : Type vM} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {N : Type vN} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [FiniteDimensional k M] [FiniteDimensional k N] [Subsingleton M]
    (htr : ∀ a : A, actionTrace k A M a = actionTrace k A N a) :
    Nonempty (M ≃ₗ[A] N) := by
  have h1 : (finrank k N : k) = (finrank k M : k) := by
    have h2 := (htr 1).symm
    rwa [actionTrace_apply, actionTrace_apply, actionEndo_one, actionEndo_one,
      LinearMap.trace_id, LinearMap.trace_id] at h2
  have hM0 : finrank k M = 0 := by
    by_contra hne
    have hnt : Nontrivial M := (Module.finrank_pos_iff_of_free k M).mp (Nat.pos_of_ne_zero hne)
    exact (not_subsingleton_iff_nontrivial.mpr hnt) ‹Subsingleton M›
  have hN0 : finrank k N = 0 := by
    have h3 : (finrank k N : k) = 0 := by rw [h1, hM0, Nat.cast_zero]
    exact_mod_cast h3
  haveI : Subsingleton N := by
    rw [← not_nontrivial_iff_subsingleton]
    intro h
    have h4 : 0 < finrank k N := (Module.finrank_pos_iff_of_free k N).mpr h
    omega
  refine ⟨LinearEquiv.ofLinear (0 : M →ₗ[A] N) (0 : N →ₗ[A] M) ?_ ?_⟩
  · ext x; exact Subsingleton.elim _ _
  · ext x; exact Subsingleton.elim _ _

private theorem nonempty_linearEquiv_of_actionTrace_eq_aux : ∀ (d : ℕ)
    (M : Type vM) (N : Type vN)
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [IsSemisimpleModule A M] [IsSemisimpleModule A N]
    [FiniteDimensional k M] [FiniteDimensional k N],
    finrank k M ≤ d →
    (∀ a : A, actionTrace k A M a = actionTrace k A N a) →
    Nonempty (M ≃ₗ[A] N) := by
  intro d
  induction d with
  | zero =>
    intro M N _ _ _ _ _ _ _ _ _ _ _ _ hle htr
    haveI : Subsingleton M := by
      rw [← not_nontrivial_iff_subsingleton]
      intro h
      have h1 : 0 < finrank k M := (Module.finrank_pos_iff_of_free k M).mpr h
      omega
    exact nonempty_linearEquiv_of_subsingleton htr
  | succ d ih =>
    intro M N _ _ _ _ _ _ _ _ _ _ _ _ hle htr
    by_cases hsub : Subsingleton M
    · exact nonempty_linearEquiv_of_subsingleton htr
    · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub

      have htop : (⊤ : Submodule A M) ≠ ⊥ := by
        intro h
        refine hsub ⟨fun u v => ?_⟩
        have hu : u ∈ (⊤ : Submodule A M) := trivial
        have hv : v ∈ (⊤ : Submodule A M) := trivial
        rw [h, Submodule.mem_bot] at hu hv
        rw [hu, hv]
      obtain ⟨S, -, hSsimple⟩ :=
        (IsSemisimpleModule.eq_bot_or_exists_simple_le (⊤ : Submodule A M)).resolve_left htop
      haveI := hSsimple

      obtain ⟨T, ⟨eST⟩⟩ := exists_linearEquiv_simple_of_actionTrace_eq htr S
      haveI : IsSimpleModule A ↥T := IsSimpleModule.congr eST.symm

      obtain ⟨Sc, hScompl⟩ := exists_isCompl S
      obtain ⟨Tc, hTcompl⟩ := exists_isCompl T
      haveI : FiniteDimensional k ↥S := finiteDimensional_coe_submodule S
      haveI : FiniteDimensional k ↥Sc := finiteDimensional_coe_submodule Sc
      haveI : FiniteDimensional k ↥T := finiteDimensional_coe_submodule T
      haveI : FiniteDimensional k ↥Tc := finiteDimensional_coe_submodule Tc

      have htr' : ∀ a : A, actionTrace k A ↥Sc a = actionTrace k A ↥Tc a := by
        intro a
        have h1 := trace_actionEndo_eq_add_of_isCompl (k := k) hScompl a
        have h2 := trace_actionEndo_eq_add_of_isCompl (k := k) hTcompl a
        have h3 := trace_actionEndo_eq_of_linearEquiv (k := k) eST a
        have h4 := htr a
        rw [actionTrace_apply, actionTrace_apply, h1, h2, h3] at h4
        rw [actionTrace_apply, actionTrace_apply]
        exact add_left_cancel h4

      have hdim : finrank k ↥S + finrank k ↥Sc = finrank k M := by
        have h5 := LinearEquiv.finrank_eq
          ((Submodule.prodEquivOfIsCompl S Sc hScompl).restrictScalars k)
        rwa [Module.finrank_prod] at h5
      have hSpos : 0 < finrank k ↥S := by
        haveI : Nontrivial ↥S := IsSimpleModule.nontrivial A ↥S
        exact (Module.finrank_pos_iff_of_free k ↥S).mpr inferInstance
      have hScle : finrank k ↥Sc ≤ d := by omega

      obtain ⟨e'⟩ := ih ↥Sc ↥Tc hScle htr'

      exact ⟨((Submodule.prodEquivOfIsCompl S Sc hScompl).symm.trans
        (eST.prodCongr e')).trans (Submodule.prodEquivOfIsCompl T Tc hTcompl)⟩

theorem nonempty_linearEquiv_of_actionTrace_eq
    {M : Type vM} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {N : Type vN} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [IsSemisimpleModule A M] [IsSemisimpleModule A N]
    [FiniteDimensional k M] [FiniteDimensional k N]
    (htr : ∀ a : A, actionTrace k A M a = actionTrace k A N a) :
    Nonempty (M ≃ₗ[A] N) :=
  nonempty_linearEquiv_of_actionTrace_eq_aux (finrank k M) M N le_rfl htr

end Headline

section MonoidAlgebraForm

variable {k : Type*} [Field k]
variable {G : Type*} [Monoid G]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]
variable {N : Type*} [AddCommGroup N] [Module k N] [Module (MonoidAlgebra k G) N]
  [IsScalarTower k (MonoidAlgebra k G) N]

theorem actionTrace_eq_of_forall_of
    (htr : ∀ g : G, actionTrace k (MonoidAlgebra k G) M (MonoidAlgebra.of k G g)
      = actionTrace k (MonoidAlgebra k G) N (MonoidAlgebra.of k G g)) :
    ∀ a : MonoidAlgebra k G,
      actionTrace k (MonoidAlgebra k G) M a = actionTrace k (MonoidAlgebra k G) N a := by
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of g => exact htr g
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul c x hx => rw [map_smul, map_smul, hx]

theorem nonempty_linearEquiv_of_forall_trace_of_eq [CharZero k]
    [IsSemisimpleModule (MonoidAlgebra k G) M] [IsSemisimpleModule (MonoidAlgebra k G) N]
    [FiniteDimensional k M] [FiniteDimensional k N]
    (htr : ∀ g : G,
      LinearMap.trace k M (actionEndo k (MonoidAlgebra k G) M (MonoidAlgebra.of k G g))
      = LinearMap.trace k N (actionEndo k (MonoidAlgebra k G) N (MonoidAlgebra.of k G g))) :
    Nonempty (M ≃ₗ[MonoidAlgebra k G] N) :=
  nonempty_linearEquiv_of_actionTrace_eq (actionTrace_eq_of_forall_of (fun g => htr g))

end MonoidAlgebraForm

end BrauerNesbitt
end


