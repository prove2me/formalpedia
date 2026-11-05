-- Prove2me | Definitions.Def_ChapterEsaOneParticleDGamma
-- name    : ChapterEsaOneParticleDGamma
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T13:40:05.257378+00:00
-- url     : https://prove2.me/theorems/c40f2608-b779-4235-87fd-d043670bed1d
-- title:
--   The Lean 4 theorem `dense_clDom` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEsaOneParticleDGamma.lean`): generated def bundle for ChapterEsaOneParticleDGamma. See BookProof/ChapterEsaOneParticleDGamma.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEsaOneParticleDGamma.lean

import Theorems.Thm_BookProof_ChapterUnboundedPosition_single_mem_mulDomain
import Theorems.Thm_BookProof_SecondQuantizationCore_essentiallySelfAdjointOn_fockSectorCore
import Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_dGammaCoreOp

import Definitions.Def_ChapterFlowDGammaEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterDiagonalDGammaEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Mathlib
import Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_graphCore
import Theorems.Thm_BookProof_GraphCore_mem_pushDom
import Theorems.Thm_BookProof_GraphCore_pushOp_apply
import Theorems.Thm_BookProof_GraphCore_IsGraphCore_refl
import Theorems.Thm_BookProof_GraphCore_symmetricOn_restrictOp
import Theorems.Thm_BookProof_GraphCore_IsGraphCore_trans
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply


/-!
# Second quantization of an **essentially self-adjoint** one-particle operator

`BookProof/ChapterFlowDGammaEsa.lean` proves that `dΓ(A)` is essentially self-adjoint on the
finite-particle domain over a graph-norm core `D` whenever the one-particle operator `A` is
**self-adjoint**.  This module removes the self-adjointness: the one-particle operator is
only assumed **symmetric and essentially self-adjoint on its own domain `D`** (trivial
deficiency at `± i`, the classical criterion), and the conclusion is stated for that same `D`.

The route is the one the closure machinery of `BookProof/ChapterEsaClosureCore.lean` makes
available:

* `closureSelfAdjoint` — the closure `Ā` of `A`, an `UnboundedSelfAdjoint` operator on
  `clDom A`, self-adjoint exactly because `A` is essentially self-adjoint;
* `isGraphCore_clDom` — `D` is a graph-norm core of `Ā` (this is what the graph closure is);
* the self-adjoint theorem, applied to `Ā` with core `D`, gives essential self-adjointness of
  the sector derivation of `Ā` on the tensor power `D^{⊗n}` of the core;
* `esa_graph_le` and the tensor lemmas `exists_pow_of_mem_corePow`, `sectorCore_graph_le`,
  `fockSectorCore_graph_le` — essential self-adjointness passes to an extension of the graph,
  and the graph of the sector derivation of `Ā` over `D^{⊗n}` is contained in the graph of the
  sector derivation of `A` itself, because `Ā` extends `A`;
* `essentiallySelfAdjointOn_fockSectorDom_esa` — the sectorwise statement for `A` alone;
* `dGamma_essentiallySelfAdjointOn_of_esa` — **the main theorem**: if the one-particle
  Hermitian operator `A` is essentially self-adjoint on `D`, then `dΓ(A)` is essentially
  self-adjoint on the finite-particle domain `𝓕_fin(D)`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.EsaOneParticle

open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa BookProof.EsaClosure
  BookProof.EsaPair BookProof.FlowDGamma BookProof.ChapterStoneResolvent
  BookProof.ChapterUnitaryTransport

noncomputable section

/-! ## The elementary-tensor equations of `inclPow` / `derPow`

The platform's published `Def_ChapterTensorGraphCore` carries the definitions but not these
three `rfl` equations, so each consumer states them itself.  The local declaration shadows the
same name opened from `BookProof.FlowDGamma` (local always wins over `open`). -/

@[simp] theorem inclPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (n : ℕ)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b := rfl

@[simp] theorem derPow_zero (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (x : ((domSpace Hs D₂).pow 0)) :
    derPow Hs D₂ A 0 x = 0 := rfl

@[simp] theorem derPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b := rfl

/-! ## Essential self-adjointness passes to an extension -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- If the graph of `T₁` is contained in the graph of `T₂`, then triviality of a deficiency
space of `T₁` forces triviality of the same deficiency space of `T₂`: the defining condition
for `T₂` is the stronger one. -/
theorem deficiencyTrivialAt_of_graph_le {D₁ D₂ : Submodule ℂ F} {T₁ : D₁ →ₗ[ℂ] F}
    {T₂ : D₂ →ₗ[ℂ] F} (h : ∀ v : D₁, ∃ u : D₂, (u : F) = (v : F) ∧ T₂ u = T₁ v) {z : ℂ}
    (h₁ : DeficiencyTrivialAt D₁ T₁ z) : DeficiencyTrivialAt D₂ T₂ z := by
  intro w hw
  refine h₁ w fun v => ?_
  obtain ⟨u, hu, hTu⟩ := h v
  have hwu := hw u
  rw [hTu, hu] at hwu
  exact hwu

/-- **Essential self-adjointness passes to an extension of the graph.** -/
theorem esa_graph_le {D₁ D₂ : Submodule ℂ F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h : ∀ v : D₁, ∃ u : D₂, (u : F) = (v : F) ∧ T₂ u = T₁ v)
    (h₁ : EssentiallySelfAdjointOn D₁ T₁) : EssentiallySelfAdjointOn D₂ T₂ :=
  ⟨deficiencyTrivialAt_of_graph_le h h₁.1, deficiencyTrivialAt_of_graph_le h h₁.2⟩

end Transfer

/-! ## The graph of the sector derivation over the core -/

section Tensor

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A₂ : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier) (hle : D ≤ D₂)
  (hext : ∀ v : D, A₂ ⟨(v : Hs.carrier), hle v.2⟩ = A v)

include hle hext in
/-- A vector of the algebraic tensor power `D^{⊗n}`, viewed inside `D₂^{⊗n}`, comes from
`(domSpace Hs D).pow n`, with the same image in `H^{⊗n}` and the same value of the sector
derivation — because `A₂` extends `A`. -/
theorem exists_pow_of_mem_corePow :
    ∀ (n : ℕ) (y : ((domSpace Hs D₂).pow n)), y ∈ corePow Hs D₂ D n →
      ∃ y' : ((domSpace Hs D).pow n),
        inclPow Hs D n y' = inclPow Hs D₂ n y ∧
          derPow Hs D A n y' = derPow Hs D₂ A₂ n y := by
  intro n
  induction n with
  | zero => exact fun y _ => ⟨y, rfl, rfl⟩
  | succ n ih =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, haD, b, hb, rfl⟩ := ht
          obtain ⟨b', hb1, hb2⟩ := ih b hb
          refine ⟨(⟨(a : Hs.carrier), haD⟩ : D) ⊗ₜ[ℂ] b', ?_, ?_⟩
          · rw [inclPow_tmul, inclPow_tmul, hb1]
          · have ha : A₂ a = A ⟨(a : Hs.carrier), haD⟩ := by
              simpa using hext ⟨(a : Hs.carrier), haD⟩
            rw [derPow_tmul, derPow_tmul, hb1, hb2, ha]
      | zero => exact ⟨0, by simp, by simp⟩
      | add x y hx hy hx' hy' =>
          obtain ⟨x', hx1, hx2⟩ := hx'
          obtain ⟨y', hy1, hy2⟩ := hy'
          exact ⟨x' + y', by rw [map_add, map_add, hx1, hy1], by rw [map_add, map_add, hx2, hy2]⟩
      | smul c x hx hx' =>
          obtain ⟨x', hx1, hx2⟩ := hx'
          exact ⟨c • x', by rw [map_smul, map_smul, hx1], by rw [map_smul, map_smul, hx2]⟩

include hle hext in
/-- The graph of the sector derivation of `A₂` over the core `D` is contained in the graph of
the sector derivation of `A` on `D^{⊗n}`. -/
theorem sectorCore_graph_le (n : ℕ) (x : sectorCore Hs D₂ D n) :
    ∃ u : sectorDom Hs D n, (u : Hs.pow n) = (x : Hs.pow n) ∧
      sectorOp Hs D A n u =
        sectorOp Hs D₂ A₂ n ⟨(x : Hs.pow n), sectorCore_le_sectorDom Hs D₂ D n x.2⟩ := by
  obtain ⟨y, hy, hyx⟩ := x.2
  obtain ⟨y', hy1, hy2⟩ := exists_pow_of_mem_corePow Hs D₂ A₂ D A hle hext n y hy
  refine ⟨⟨inclPow Hs D n y', ⟨y', rfl⟩⟩, ?_, ?_⟩
  · exact hy1.trans hyx
  · rw [sectorOp_apply Hs D A n ⟨inclPow Hs D n y', ⟨y', rfl⟩⟩ y' rfl,
      sectorOp_apply Hs D₂ A₂ n ⟨(x : Hs.pow n), sectorCore_le_sectorDom Hs D₂ D n x.2⟩ y
        hyx.symm]
    exact hy2

include hle hext in
/-- The same statement inside the completed sector. -/
theorem fockSectorCore_graph_le (n : ℕ) (x : fockSectorCore Hs D₂ D n) :
    ∃ u : fockSectorDom Hs D n, (u : fockSector Hs n) = (x : fockSector Hs n) ∧
      fockSectorOp Hs D A n u =
        restrictOp (fockSectorOp Hs D₂ A₂ n) (fockSectorCore_le_fockSectorDom Hs D₂ D n) x := by
  obtain ⟨s, hs, hsx⟩ := x.2
  obtain ⟨u, hu1, hu2⟩ := sectorCore_graph_le Hs D₂ A₂ D A hle hext n ⟨s, hs⟩
  refine ⟨⟨sectorEmb Hs n (u : Hs.pow n), mem_pushDom _ u⟩, ?_, ?_⟩
  · change sectorEmb Hs n (u : Hs.pow n) = (x : fockSector Hs n)
    rw [hu1]; exact hsx
  · have h1 : fockSectorOp Hs D A n ⟨sectorEmb Hs n (u : Hs.pow n), mem_pushDom _ u⟩
        = sectorEmb Hs n (sectorOp Hs D A n u) :=
      pushOp_apply (sectorEmb Hs n) (sectorOp Hs D A n) _ u rfl
    have h2 : restrictOp (fockSectorOp Hs D₂ A₂ n)
          (fockSectorCore_le_fockSectorDom Hs D₂ D n) x
        = sectorEmb Hs n
            (sectorOp Hs D₂ A₂ n ⟨s, sectorCore_le_sectorDom Hs D₂ D n hs⟩) := by
      -- `restrictOp T h` is `T ∘ inclusion h`, so the left side is *definitionally*
      -- `fockSectorOp … ⟨x, h x.2⟩`; the published `Def_ChapterGraphCoreTransfer`
      -- keeps `restrictOp` but not its `restrictOp_apply` lemma, so this goes
      -- through `exact` (defeq) instead of naming a lemma the platform omits.
      exact pushOp_apply (sectorEmb Hs n) (sectorOp Hs D₂ A₂ n) _
        ⟨s, sectorCore_le_sectorDom Hs D₂ D n hs⟩ hsx.symm
    rw [h1, h2, hu2]

end Tensor

/-! ## The closure of an essentially self-adjoint one-particle operator -/

section Closure

variable {Hs : IPSpace} {D : Submodule ℂ Hs.carrier}

/-- The domain of the closure is dense, since it contains `D`. -/
theorem dense_clDom (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) :
    Dense ((clDom A : Submodule ℂ Hs.carrier) : Set Hs.carrier) :=
  hdense.mono (fun x hx => coe_mem_clDom A ⟨x, hx⟩)

/-- `D` is contained in the domain of the closure. -/
theorem le_clDom (A : D →ₗ[ℂ] Hs.carrier) : D ≤ clDom A :=
  fun x hx => coe_mem_clDom A ⟨x, hx⟩

/-- **`D` is a graph-norm core of the closure** — that is exactly what the graph closure
is. -/
theorem isGraphCore_clDom (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier))
    (hsym : SymmetricOn D A) : IsGraphCore D (clExt A hdense hsym) := by
  intro x ε hε
  have hmem : ((x : Hs.carrier), clFun A x) ∈ closure ((opGraph A : Submodule ℂ _) :
      Set (Hs.carrier × Hs.carrier)) := clFun_spec A x
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨v, rfl⟩ : ∃ v : D, ((v : Hs.carrier), A v) = p := by
    obtain ⟨v, hv⟩ := hp
    exact ⟨v, hv⟩
  refine ⟨⟨(v : Hs.carrier), coe_mem_clDom A v⟩, v.2, ?_, ?_⟩
  · have := (max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hdist)).1
    simpa using this
  · have := (max_lt_iff.mp (by simpa [Prod.dist_eq, dist_eq_norm] using hdist)).2
    have hval : clExt A hdense hsym ⟨(v : Hs.carrier), coe_mem_clDom A v⟩ = A v :=
      clExt_extends A hdense hsym v
    rw [clExt_apply, hval]
    simpa using this

variable [CompleteSpace Hs.carrier]

/-- **The closure of an essentially self-adjoint operator, as a self-adjoint operator.**  Its
domain is the domain `clDom A` of the graph closure, and it extends `A`. -/
def closureSelfAdjoint (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier))
    (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A) :
    UnboundedSelfAdjoint Hs.carrier where
  domain := clDom A
  op := clExt A hdense hsym
  denseDomain := dense_clDom A hdense
  symmetric := clExt_symmetricOn A hdense hsym
  selfAdjoint := by
    ext phi
    constructor
    · rintro ⟨eta, heta⟩
      obtain ⟨hmem, -⟩ := clExt_selfAdjointCriterion A hdense hsym hesa phi eta heta
      exact hmem
    · intro hphi
      exact ⟨clExt A hdense hsym ⟨phi, hphi⟩,
        fun psi => clExt_symmetricOn A hdense hsym psi ⟨phi, hphi⟩⟩

@[simp] theorem closureSelfAdjoint_domain (A : D →ₗ[ℂ] Hs.carrier)
    (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
    (hesa : EssentiallySelfAdjointOn D A) :
    (closureSelfAdjoint A hdense hsym hesa).domain = clDom A := rfl

@[simp] theorem closureSelfAdjoint_op (A : D →ₗ[ℂ] Hs.carrier)
    (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
    (hesa : EssentiallySelfAdjointOn D A) :
    (closureSelfAdjoint A hdense hsym hesa).op = clExt A hdense hsym := rfl

end Closure

/-! ## The main theorem -/

section Main

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

include hdense hsym hesa in
/-- **The sectorwise statement for an essentially self-adjoint one-particle operator.**  The
sector derivation `dΓ(A)⁽ⁿ⁾` is essentially self-adjoint on the tensor power `D^{⊗n}` of the
one-particle domain itself. -/
theorem essentiallySelfAdjointOn_fockSectorDom_esa (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs D n) (fockSectorOp Hs D A n) := by
  have hcore : IsGraphCore D (clExt A hdense hsym) := isGraphCore_clDom A hdense hsym
  have hsectorClosure : EssentiallySelfAdjointOn (fockSectorDom Hs (clDom A) n)
      (fockSectorOp Hs (clDom A) (clExt A hdense hsym) n) :=
    essentiallySelfAdjointOn_fockSectorDom_selfAdjoint (closureSelfAdjoint A hdense hsym hesa) n
  have hsource : EssentiallySelfAdjointOn (fockSectorCore Hs (clDom A) D n)
      (restrictOp (fockSectorOp Hs (clDom A) (clExt A hdense hsym) n)
        (fockSectorCore_le_fockSectorDom Hs (clDom A) D n)) :=
    essentiallySelfAdjointOn_fockSectorCore Hs (clDom A) (clExt A hdense hsym) D hcore n
      hsectorClosure
  refine esa_graph_le ?_ hsource
  exact fockSectorCore_graph_le Hs (clDom A) (clExt A hdense hsym) D A (le_clDom A)
    (fun v => clExt_extends A hdense hsym v) n

include hdense hsym hesa in
/-- **Main theorem.**  Let the one-particle Hermitian operator `A` be *essentially*
self-adjoint on its dense domain `D` — symmetric, with both deficiency spaces trivial, and
with no self-adjointness assumed.  Then the second quantization `dΓ(A)` is essentially
self-adjoint on the finite-particle domain `𝓕_fin(D)` built from `D` alone. -/
theorem dGamma_essentiallySelfAdjointOn_of_esa :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs D D n))
      (dGammaCoreOp Hs D A D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs D A D (IsGraphCore.refl A)
    (essentiallySelfAdjointOn_fockSectorDom_esa A hdense hsym hesa)

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)` is symmetric on the same domain. -/
theorem symmetricOn_dGammaCoreOp_of_esa :
    SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs D D n)) (dGammaCoreOp Hs D A D) :=
  symmetricOn_dGammaCoreOp Hs D A D hsym

end Main

/-! ## The hypothesis is strictly weaker than self-adjointness -/

section Weaker

variable {Hs : IPSpace}

/-- A self-adjoint operator has no deficiency at a non-real point. -/
theorem deficiencyTrivialAt_of_selfAdjoint (T : UnboundedSelfAdjoint Hs.carrier) {z : ℂ}
    (hz : (starRingEnd ℂ) z ≠ z) : DeficiencyTrivialAt T.domain T.op z := by
  intro w hw
  have hrep : ∀ v : T.domain, (inner ℂ (T.op v) w : ℂ) = inner ℂ (v : Hs.carrier) (z • w) := by
    intro v
    rw [inner_smul_right]
    exact hw v
  have hmem : w ∈ T.domain := T.mem_domain_of_inner hrep
  have hval : T.op ⟨w, hmem⟩ = z • w := T.op_eq_of_inner hmem hrep
  have h1 := T.symmetric ⟨w, hmem⟩ ⟨w, hmem⟩
  rw [hval] at h1
  simp only [inner_smul_left, inner_smul_right] at h1
  have h2 : ((starRingEnd ℂ) z - z) * (inner ℂ w w : ℂ) = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact h1
  have h3 : (inner ℂ w w : ℂ) = 0 :=
    (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hz)
  exact inner_self_eq_zero.mp h3

/-- **A self-adjoint operator is essentially self-adjoint on its own domain**, so the
hypothesis of the main theorem is implied by self-adjointness. -/
theorem essentiallySelfAdjointOn_of_selfAdjoint (T : UnboundedSelfAdjoint Hs.carrier) :
    EssentiallySelfAdjointOn T.domain T.op :=
  ⟨deficiencyTrivialAt_of_selfAdjoint T (by simp [Complex.ext_iff]; norm_num),
    deficiencyTrivialAt_of_selfAdjoint T (by simp [Complex.ext_iff]; norm_num)⟩

/-- **The restriction of a self-adjoint operator to a graph-norm core is essentially
self-adjoint** — this is the standard source of operators satisfying the hypothesis of the
main theorem. -/
theorem essentiallySelfAdjointOn_restrict (T : UnboundedSelfAdjoint Hs.carrier)
    {D : Submodule ℂ Hs.carrier} (hle : D ≤ T.domain) (hcore : IsGraphCore D T.op) :
    EssentiallySelfAdjointOn D (restrictOp T.op hle) :=
  essentiallySelfAdjointOn_of_graphCore _ hle hcore (essentiallySelfAdjointOn_of_selfAdjoint T)

/-- **... but it is not self-adjoint on a proper core.**  The adjoint domain of the
restriction contains the whole domain of `T`, so it is strictly larger than `D` as soon as
`D` is a proper subspace of `T.domain`.  Together with the previous lemma this shows that the
hypothesis "essentially self-adjoint on `D`" is strictly weaker than "self-adjoint on `D`". -/
theorem not_isSelfAdjointOn_restrict (T : UnboundedSelfAdjoint Hs.carrier)
    {D : Submodule ℂ Hs.carrier} (hle : D ≤ T.domain) (hne : D ≠ T.domain) :
    ¬ IsSelfAdjointOn D (restrictOp T.op hle) := by
  intro hsa
  refine hne (le_antisymm hle fun x hx => ?_)
  have hmem : x ∈ adjointDomain D (restrictOp T.op hle) :=
    ⟨T.op ⟨x, hx⟩, fun psi => T.symmetric ⟨(psi : Hs.carrier), hle psi.2⟩ ⟨x, hx⟩⟩
  rw [hsa] at hmem
  exact hmem

end Weaker

/-! ## A concrete instance: the position operator on the finitely supported vectors

Nothing above is vacuous.  On `ℓ²(ℤ)` the position operator — multiplication by `k`, an
unbounded self-adjoint operator — is restricted to the span `Dfin` of the basis vectors
`δ_k`, i.e. to the finitely supported sequences.  On that domain it is *essentially* self
adjoint (`positionCore_essentiallySelfAdjoint`) but *not* self-adjoint
(`positionCore_not_isSelfAdjointOn`), and the main theorem applies to it. -/

section PositionExample

open BookProof.ChapterUnboundedPosition BookProof.ChapterStoneSeparable
open BookProof.ChapterContinuityUnitaryInfinite (L2Z)
open BookProof.DiagonalDGamma

/-- The basis vector `δ_k` of `ℓ²(ℤ)`. -/
def deltaVec (k : ℤ) : L2Z := lp.single 2 k (1 : ℂ)

/-- The finitely supported vectors: the span of the basis vectors. -/
def Dfin : Submodule ℂ L2Z := Submodule.span ℂ (Set.range deltaVec)

/-- The span of the basis vectors is dense in `ℓ²(ℤ)`. -/
theorem dense_Dfin : Dense ((Dfin : Submodule ℂ L2Z) : Set L2Z) := by
  intro psi
  refine mem_closure_of_tendsto (lp.hasSum_single (by norm_num) psi) ?_
  filter_upwards with s
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [lp_single_eq_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The finitely supported vectors lie in the domain of every multiplication operator. -/
theorem Dfin_le_mulDomain (f : ℤ → ℝ) : Dfin ≤ mulDomain f := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact single_mem_mulDomain f k 1

/-- **The position operator restricted to the finitely supported vectors.** -/
def positionCore : Dfin →ₗ[ℂ] L2Z :=
  restrictOp (mulOp positionField) (Dfin_le_mulDomain positionField)

/-- The restricted position operator is symmetric. -/
theorem positionCore_symmetricOn : SymmetricOn Dfin positionCore :=
  symmetricOn_restrictOp _ _ (mulOp_symmetric positionField)

/-- `δ_k` is an eigenvector of the restricted position operator, with eigenvalue `k`. -/
theorem positionCore_eig (k : ℤ) :
    positionCore ⟨deltaVec k, Submodule.subset_span ⟨k, rfl⟩⟩
      = ((k : ℝ) : ℂ) • deltaVec k := by
  ext j
  by_cases hj : j = k
  · subst hj
    simp [positionCore, restrictOp, mulOp, deltaVec, positionField, lp.single_apply]
  · simp [positionCore, restrictOp, mulOp, deltaVec, positionField, lp.single_apply, hj]

/-- **The restricted position operator is essentially self-adjoint**: its eigenvectors span a
dense subspace. -/
theorem positionCore_essentiallySelfAdjoint : EssentiallySelfAdjointOn Dfin positionCore := by
  refine essentiallySelfAdjointOn_of_dense_eigenvectors positionCore
    (fun k : ℤ => (⟨deltaVec k, Submodule.subset_span ⟨k, rfl⟩⟩ : Dfin))
    (fun k : ℤ => (k : ℝ)) (fun k => positionCore_eig k) ?_
  have hrange : (Set.range fun k : ℤ => ((⟨deltaVec k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      Dfin) : L2Z)) = Set.range deltaVec := rfl
  rw [hrange]
  exact dense_Dfin

/-! ### The core is proper: an explicit vector of the domain outside it -/

/-- The summability input: `∑ 1/k²` over `ℤ`. -/
theorem summable_one_div_int_sq : Summable (fun k : ℤ => 1 / ((k : ℝ)) ^ 2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

/-- `1 ≤ k²` for a nonzero integer `k`. -/
theorem one_le_int_sq {k : ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ ((k : ℝ)) ^ 2 := by
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h2 : 1 ≤ |k| := Int.one_le_abs (by omega)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h2
      _ = |(k : ℝ)| := by push_cast [Int.cast_abs]; ring
  nlinarith [abs_nonneg ((k : ℝ)), sq_abs ((k : ℝ))]

/-- The tail sequence `1/(k²+1)` is square-summable. -/
theorem summable_witness_sq : Summable (fun k : ℤ => (1 / ((k : ℝ) ^ 2 + 1)) ^ 2) := by
  refine (summable_one_div_int_sq.update 0 1).of_nonneg_of_le (fun k => by positivity)
    (fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · norm_num [Function.update]
  · rw [Function.update_of_ne hk, div_pow, one_pow]
    have ht := one_le_int_sq hk
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- ... and so is `k/(k²+1)`, which is the image of the tail sequence under the position
operator. -/
theorem summable_witness_mul_sq :
    Summable (fun k : ℤ => ((k : ℝ) / ((k : ℝ) ^ 2 + 1)) ^ 2) := by
  refine summable_one_div_int_sq.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · norm_num
  · have ht := one_le_int_sq hk
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The witness sequence `k ↦ 1/(k²+1)`, as a vector of `ℓ²(ℤ)`. -/
def witnessFun (k : ℤ) : ℂ := ((1 / ((k : ℝ) ^ 2 + 1) : ℝ) : ℂ)

theorem memℓp_witnessFun : Memℓp witnessFun 2 := by
  refine memℓp_gen ?_
  have h : (fun k : ℤ => ‖witnessFun k‖ ^ (2 : ℝ≥0∞).toReal)
      = fun k : ℤ => (1 / ((k : ℝ) ^ 2 + 1)) ^ 2 := by
    funext k
    have hpos : (0 : ℝ) ≤ 1 / ((k : ℝ) ^ 2 + 1) := by positivity
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, witnessFun,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  rw [h]
  exact summable_witness_sq

/-- The witness vector of `ℓ²(ℤ)`: every entry is nonzero, so it is not finitely
supported. -/
def witness : L2Z := ⟨witnessFun, memℓp_witnessFun⟩

theorem witness_apply (k : ℤ) : (witness : ℤ → ℂ) k = witnessFun k := rfl

theorem witness_mem_mulDomain : witness ∈ mulDomain positionField := by
  refine memℓp_gen ?_
  have h : (fun k : ℤ => ‖(positionField k : ℂ) * (witness : ℤ → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal)
      = fun k : ℤ => ((k : ℝ) / ((k : ℝ) ^ 2 + 1)) ^ 2 := by
    funext k
    have hpos : (0 : ℝ) < (k : ℝ) ^ 2 + 1 := by positivity
    have habs : |(k : ℝ)| * (1 / ((k : ℝ) ^ 2 + 1)) = |(k : ℝ) / ((k : ℝ) ^ 2 + 1)| := by
      rw [abs_div, abs_of_pos hpos]; ring
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, witness_apply,
      witnessFun, positionField, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < 1 / ((k : ℝ) ^ 2 + 1))), habs]
    norm_num [sq_abs]
  rw [h]
  exact summable_witness_mul_sq

/-- The finitely supported vectors, as a submodule. -/
def finSupp : Submodule ℂ L2Z where
  carrier := {x : L2Z | {k : ℤ | (x : ℤ → ℂ) k ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    refine Set.Finite.subset (ha.union hb) (fun k hk => ?_)
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at hk
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    exact hk (by rw [hcon.1, hcon.2, add_zero])
  smul_mem' := by
    intro c a ha
    refine Set.Finite.subset ha (fun k hk => ?_)
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hk ⊢
    intro h0
    exact hk (by rw [h0, mul_zero])

theorem Dfin_le_finSupp : Dfin ≤ finSupp := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine Set.Finite.subset (Set.finite_singleton k) (fun j hj => ?_)
  simp only [Set.mem_setOf_eq, deltaVec, lp.single_apply] at hj
  by_contra hne
  exact hj (by simp [Pi.single_eq_of_ne (by simpa using hne)])

theorem witness_not_mem_Dfin : witness ∉ Dfin := by
  intro hmem
  have hfin : {k : ℤ | (witness : ℤ → ℂ) k ≠ 0}.Finite := Dfin_le_finSupp hmem
  have huniv : {k : ℤ | (witness : ℤ → ℂ) k ≠ 0} = Set.univ := by
    ext k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) ^ 2 + 1) := by positivity
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, witness_apply, witnessFun, ne_eq,
      Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

/-- **The core is proper**: the domain of the position operator is strictly larger than the
finitely supported vectors. -/
theorem Dfin_ne_mulDomain : Dfin ≠ mulDomain positionField := by
  intro h
  exact witness_not_mem_Dfin (h ▸ witness_mem_mulDomain)



/-- **The main theorem applied to a genuinely essentially self-adjoint one-particle
operator.**  `A` is the position operator on `ℓ²(ℤ)` restricted to the finitely supported
vectors: symmetric, essentially self-adjoint, unbounded, and *not* self-adjoint on that
domain.  Then `dΓ(A)` is essentially self-adjoint on the finite-particle domain over it. -/
theorem dGamma_positionCore_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore L2ZSpace Dfin Dfin n))
      (dGammaCoreOp L2ZSpace Dfin positionCore Dfin) :=
  dGamma_essentiallySelfAdjointOn_of_esa (Hs := L2ZSpace) positionCore dense_Dfin
    positionCore_symmetricOn positionCore_essentiallySelfAdjoint

end PositionExample

end

end BookProof.EsaOneParticle


