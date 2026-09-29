-- Prove2me | Definitions.Def_MilnorConjecture_HomogeneousCochains
-- name    : MilnorConjecture_HomogeneousCochains
-- status  : Definition
-- author  : @vatsj
-- created : 2026-09-24T21:10:05.520817+00:00
-- url     : https://prove2.me/theorems/759c5dea-fe66-4726-b925-2a047c3f292a
-- title:
--   Classes of invariant homogeneous cocycles in continuous cohomology
-- statement:
--   Let $G$ be a locally compact topological group, $k$ a topological ring and $M$ a topological $k$-module, regarded as a **trivial** representation of $G$. Mathlib computes continuous cohomology $H^n_{\mathrm{cts}}(G,M)$ from the complex of $G$-invariant elements of $C(G, C(G, \cdots C(G, M)))$ ($n+1$ nested copies of $G$ in degree $n$), with an inductively defined differential.
--
--   This file translates that model into functions of several variables. For a continuous $F : G^{n+1}\to M$ which is **invariant under simultaneous left translation**,
--   $$F(gx_0,\dots,gx_n) = F(x_0,\dots,x_n)\quad (g\in G),$$
--   and satisfies the **homogeneous cocycle identity**
--   $$\sum_{i=0}^{n+1} (-1)^i\, F(y_0,\dots,\widehat{y_i},\dots,y_{n+1}) = 0,$$
--   it defines the class $[F] \in H^n_{\mathrm{cts}}(G,M)$ of the corresponding nested cochain $x_0\mapsto x_1\mapsto\cdots\mapsto F(x_0,\dots,x_n)$. The file proves that Mathlib's differential of this nested cochain is the alternating face sum above, and that the $G$-action translates all arguments.
--
--   This is reusable infrastructure: it gives a concrete way to write down classes in Mathlib's continuous cohomology with trivial coefficients.
--
--   **Formalization Note** `curryN`, `coboundary` and `classOf` are sorry-free; local compactness of $G$ is used only to make iterated currying continuous.
-- source:
--   Standard homogeneous-cochain description of continuous group cohomology (cf. Neukirch-Schmidt-Wingberg, Cohomology of Number Fields), specialised to Mathlib's `continuousCohomology` (Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean).

import Mathlib

/-!
# Homogeneous cochains with trivial coefficients, as functions of several variables

Mathlib's continuous cohomology `continuousCohomology n A` is the homology of the complex
of `G`-invariant elements of `C(G, C(G, ⋯ C(G, A)))` (`n + 1` nested copies of `G`), with the
inductively defined differential `TopRep.d`. For trivial coefficients `M` and a locally compact
group `G`, this file turns a continuous function `F : Gⁿ⁺¹ → M` that is invariant under
simultaneous left translation and satisfies the homogeneous cocycle identity
`∑ᵢ (-1)ⁱ F(x₀, …, x̂ᵢ, …, xₙ₊₁) = 0` into a class in `continuousCohomology n`.
-/

open CategoryTheory

namespace MilnorConjecture

universe u

variable {k G M : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M]

variable (k G M) in
/-- `M` as a trivial continuous `k`-linear representation of `G`. -/
abbrev trivialRep : TopRep k G := TopRep.of (ContRepresentation.trivial k G M)

/-- The map `(x, v) ↦ (x, v₀, …, vₙ₋₁)` from `G × Gⁿ` to `Gⁿ⁺¹`. -/
def consMap (n : ℕ) : C(G × (Fin n → G), Fin (n + 1) → G) :=
  ⟨fun p ↦ Fin.cons p.1 p.2, by fun_prop⟩

variable (k G M) in
/-- Currying `n` times: a continuous `F : Gⁿ → M` becomes the element
`x₀ ↦ x₁ ↦ ⋯ ↦ F(x₀, …, xₙ₋₁)` of `C(G, C(G, ⋯ C(G, M)))`, the `n`-th term of Mathlib's
resolution `TopRep.resolutionX`. The assignment is itself continuous. -/
noncomputable def curryN : (n : ℕ) →
    C(C(Fin n → G, M), ((trivialRep k G M).resolutionX n : Type u))
  | 0 => ⟨fun F ↦ F Fin.elim0, continuous_eval_const _⟩
  | n + 1 => ⟨fun F ↦ (curryN n).comp (F.comp (consMap n)).curry,
      (ContinuousMap.continuous_postcomp _).comp
        (ContinuousMap.continuous_curry.comp (ContinuousMap.continuous_precomp _))⟩

@[simp]
lemma curryN_zero_apply (F : C(Fin 0 → G, M)) : curryN k G M 0 F = F Fin.elim0 := rfl

@[simp]
lemma curryN_succ_apply {n : ℕ} (F : C(Fin (n + 1) → G, M)) (x : G) :
    curryN k G M (n + 1) F x = curryN k G M n ⟨fun v ↦ F (Fin.cons x v), by fun_prop⟩ := rfl

lemma curryN_sub {n : ℕ} (F F' : C(Fin n → G, M)) :
    curryN k G M n (F - F') = curryN k G M n F - curryN k G M n F' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext1 x
    rw [curryN_succ_apply, ContinuousMap.sub_apply, curryN_succ_apply, curryN_succ_apply, ← ih]
    rfl

/-- The `i`-th face map `Gⁿ⁺¹ → Gⁿ`, deleting the `i`-th coordinate. -/
def faceMap (n : ℕ) (i : Fin (n + 1)) : C(Fin (n + 1) → G, Fin n → G) :=
  ⟨fun y ↦ y ∘ i.succAbove, by fun_prop⟩

/-- The homogeneous coboundary with trivial coefficients:
`(δF)(y₀, …, yₙ) = ∑ᵢ (-1)ⁱ F(y₀, …, ŷᵢ, …, yₙ)`. -/
def coboundary (n : ℕ) (F : C(Fin n → G, M)) : C(Fin (n + 1) → G, M) :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • F.comp (faceMap n i)

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
lemma coboundary_apply {n : ℕ} (F : C(Fin n → G, M)) (y : Fin (n + 1) → G) :
    coboundary n F y = ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • F (y ∘ i.succAbove) := by
  simp [coboundary, faceMap]

/-- Mathlib's inductively defined differential agrees with the alternating face sum. -/
lemma d_curryN (n : ℕ) (F : C(Fin n → G, M)) :
    ((trivialRep k G M).d n).hom (curryN k G M n F) = curryN k G M (n + 1) (coboundary n F) := by
  induction n with
  | zero =>
    ext x
    show F Fin.elim0 = coboundary 0 F (Fin.cons x Fin.elim0)
    rw [coboundary_apply, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    exact congrArg F (funext fun i ↦ i.elim0)
  | succ n ih =>
    ext1 x
    rw [TopRep.hom_d_succ]
    change curryN k G M (n + 1) F - ((trivialRep k G M).d n).hom (curryN k G M (n + 1) F x) = _
    rw [curryN_succ_apply, ih, ← curryN_sub, curryN_succ_apply]
    congr 1
    ext w
    simp only [ContinuousMap.sub_apply, ContinuousMap.coe_mk]
    rw [coboundary_apply, coboundary_apply]
    show F w - ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • F (Fin.cons x (w ∘ i.succAbove)) = _
    conv_rhs => rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Fin.cons_comp_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove]
    rfl

lemma curryN_zero {n : ℕ} : curryN k G M n 0 = 0 := by
  simpa using curryN_sub (k := k) (0 : C(Fin n → G, M)) 0

/-- Left translation `(v₀, …, vₙ₋₁) ↦ (g v₀, …, g vₙ₋₁)` on `Gⁿ`. -/
def translate (n : ℕ) (g : G) : C(Fin n → G, Fin n → G) :=
  ⟨fun v i ↦ g * v i, by fun_prop⟩

/-- With trivial coefficients, `g` acts on `C(G, ⋯ C(G, M))` by translating every argument
by `g⁻¹`. -/
lemma ρ_curryN (n : ℕ) (g : G) (F : C(Fin n → G, M)) :
    ((trivialRep k G M).resolutionX n).ρ g (curryN k G M n F) =
      curryN k G M n (F.comp (translate n g⁻¹)) := by
  induction n with
  | zero =>
    show F Fin.elim0 = F (fun i ↦ g⁻¹ * Fin.elim0 i)
    exact congrArg F (funext fun i ↦ i.elim0)
  | succ n ih =>
    ext1 x
    rw [ContRepresentation.coind₁_apply_apply, curryN_succ_apply, ih, curryN_succ_apply]
    congr 1
    ext v
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, translate]
    congr 1
    funext i
    cases i using Fin.cases <;> simp

lemma curryN_mem_invariants {n : ℕ} (F : C(Fin n → G, M))
    (hF : ∀ (g : G) (v : Fin n → G), F (fun i ↦ g * v i) = F v) :
    curryN k G M n F ∈ ((trivialRep k G M).resolutionX n).ρ.invariants := by
  intro g
  rw [ρ_curryN]
  congr 1
  ext v
  exact hF g⁻¹ v

variable [IsTopologicalRing k]

variable (k) in
/-- The class in `continuousCohomology n` of a continuous `F : Gⁿ⁺¹ → M` that is invariant
under simultaneous left translation and is a homogeneous cocycle (`δF = 0`), with `M` a
trivial representation of `G`. -/
noncomputable def classOf (n : ℕ) (F : C(Fin (n + 1) → G, M))
    (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 1) F = 0) :
    continuousCohomology n (trivialRep k G M) :=
  let σ : (trivialRep k G M).homogeneousCochains.X n :=
    ⟨curryN k G M (n + 1) F, curryN_mem_invariants F hinv⟩
  let ι : TopModuleCat.of k k ⟶ (trivialRep k G M).homogeneousCochains.X n :=
    TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k σ)
  have hd : ((trivialRep k G M).homogeneousCochains.d n (n + 1)).hom σ = 0 := by
    apply Subtype.ext
    rw [TopRep.homogeneousCochains.d_apply]
    change ((trivialRep k G M).d (n + 1)).hom (curryN k G M (n + 1) F) = 0
    rw [d_curryN, hcoc, curryN_zero]
  have hσ : ι ≫ (trivialRep k G M).homogeneousCochains.d n (n + 1) = 0 := by
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext_ring
    have h1 : ι 1 = σ := one_smul k σ
    rw [ConcreteCategory.comp_apply, h1]
    simpa using hd
  (ContinuousCohomology.π _ n).hom
    (((trivialRep k G M).homogeneousCochains.liftCycles ι (n + 1) (by simp) hσ).hom 1)

end MilnorConjecture


