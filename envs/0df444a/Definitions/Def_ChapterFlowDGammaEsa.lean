-- Prove2me | Definitions.Def_ChapterFlowDGammaEsa
-- name    : ChapterFlowDGammaEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T22:19:37.48437+00:00
-- url     : https://prove2.me/theorems/ea697ece-cb23-44eb-b63e-e1f63af650ec
-- title:
--   The Lean 4 theorem `deficiencyTrivialAt_of_orbits` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFlowDGammaEsa.lean`): generated def bundle for ChapterFlowDGammaEsa. See BookProof/ChapterFlowDGammaEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFlowDGammaEsa.lean

import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric

import Theorems.Thm_BookProof_GraphCore_pushOp_apply

import Theorems.Thm_BookProof_TensorCore_sectorOp_apply

import Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_hasDerivAt_smul_of_bounded

import Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_inner_right_eq_zero_on_dense

import Theorems.Thm_BookProof_GraphCore_mem_pushDom

import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_op
import Theorems.Thm_BookProof_ChapterStoneSeparable_mulSA_position_unbounded





import Definitions.Def_ChapterDiagonalDGammaEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterStoneUnitary
import Mathlib


/-!
# Second quantization of an arbitrary **self-adjoint** one-particle operator

`BookProof/ChapterBoundedDGammaEsa.lean` discharged the sectorwise input of the second
quantization theorem for *bounded* one-particle operators, and
`BookProof/ChapterDiagonalDGammaEsa.lean` for *unbounded* ones with a total family of
eigenvectors.  This module removes the last restriction: the sectorwise input is proved for
**every self-adjoint one-particle operator**, with no bound, no positivity and no assumption
on the spectrum (point, continuous or mixed).

The mechanism is the invariant-domain (Nelson) argument, run on the sectors:

* `deficiencyTrivialAt_of_orbits` — if every vector of a spanning family of the domain has a
  norm-preserving orbit `t ↦ orb t` solving `d/dt orb t = -i T (orb t)` for all real times,
  then `T` has no deficiency: `g(t) = ⟪w, orb t⟫` would solve `g' = ± g` and stay bounded, so
  `g 0 = ⟪w, orb 0⟫ = 0`;
* `OneParticleFlow` — the data of the one-particle unitary group: `U t` isometric and
  invertible, `U t` leaves the domain invariant, and `d/dt U t x = -i A (U t x)` on the
  domain.  For a self-adjoint operator this is Stone's theorem, available in the tree
  (`BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU`), so `ofSelfAdjoint` builds
  the package from self-adjointness alone;
* `OneParticleFlow.pow` — the tensor power `U t ⊗ ⋯ ⊗ U t` of the flow, which is again
  isometric (`norm_pow`) and leaves the tensor power of the domain invariant by construction;
* `hasDerivAt_pow` — the Leibniz rule: the tensor flow solves
  `d/dt (U t ⊗ ⋯ ⊗ U t) x = -i dΓ(A)⁽ⁿ⁾ ((U t ⊗ ⋯ ⊗ U t) x)`, proved by induction on the
  number of particles from the product rule for the (bounded bilinear) tensor multiplication;
* `essentiallySelfAdjointOn_fockSectorDom_flow` — **the sector hypothesis, proved**;
* `dGamma_flow_essentiallySelfAdjointOn_fockCore` and
  `dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore` — **the main theorem**: for any
  self-adjoint one-particle operator `A` and any graph-norm core `D` of `A`, `dΓ(A)` is
  essentially self-adjoint on the finite-particle domain `𝓕_fin(D)` built from `D` alone.
  `D` is only a core: it is not invariant under the flow, and no resolvent of `A` on `D` is
  used;
* `dGamma_position_essentiallySelfAdjointOn_fockCore` — a concrete instance: the one-particle
  operator is multiplication by `k` on `ℓ²(ℤ)`, self-adjoint and genuinely unbounded
  (`position_not_bounded`).

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.FlowDGamma

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa BookProof.EsaPair
  BookProof.TensorOpBound BookProof.DiagonalDGamma

noncomputable section

/-! ## The elementary-tensor equations of `inclPow` / `derPow`

The platform's published `Def_ChapterTensorGraphCore` carries the definitions but not these
three `rfl` equations, so each consumer states them itself.  The local declaration shadows the
same name opened from `BookProof.DiagonalDGamma` (local always wins over `open`). -/

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

/-! ## Nelson's criterion, in orbit form -/

section Nelson

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- **Nelson's invariant-domain criterion.**  Suppose every member of a family `orb g` of
curves in the domain solves `d/dt orb g t = -i T (orb g t)` for *all* real times, preserves
the norm, and that the initial values `orb g 0` span a dense subspace.  Then the deficiency
space of `T` at `± i` is trivial.  No boundedness, positivity or self-adjointness of `T` is
used. -/
theorem deficiencyTrivialAt_of_orbits {G : Type*} (T : D →ₗ[ℂ] F) (orb : G → ℝ → D)
    (hnorm : ∀ (g : G) (t : ℝ), ‖((orb g t : D) : F)‖ = ‖((orb g 0 : D) : F)‖)
    (hderiv : ∀ (g : G) (t : ℝ), HasDerivAt (fun s : ℝ => ((orb g s : D) : F))
      ((-Complex.I) • T (orb g t)) t)
    (hdense : Dense ((Submodule.span ℂ (Set.range fun g : G => ((orb g 0 : D) : F)) :
      Submodule ℂ F) : Set F))
    (s : ℝ) (hs : s * s = 1) :
    DeficiencyTrivialAt D T ((s : ℂ) * Complex.I) := by
  intro w hw
  have key : ∀ g : G, (inner ℂ w ((orb g 0 : D) : F) : ℂ) = 0 := by
    intro g
    set gf : ℝ → ℂ := fun t => inner ℂ w ((orb g t : D) : F) with hgf
    have hgd : ∀ t : ℝ, HasDerivAt gf (((-s : ℝ) : ℂ) * gf t) t := by
      intro t
      have h1 : HasDerivAt gf (inner ℂ w (((-Complex.I) • T (orb g t)) : F) : ℂ) t :=
        ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hderiv g t)
      have hconj : (inner ℂ w (T (orb g t)) : ℂ)
          = (starRingEnd ℂ) ((s : ℂ) * Complex.I) * inner ℂ w ((orb g t : D) : F) := by
        have hk := hw (orb g t)
        have h2 : (inner ℂ w (T (orb g t)) : ℂ)
            = (starRingEnd ℂ) (inner ℂ (T (orb g t)) w : ℂ) := by
          rw [inner_conj_symm]
        rw [h2, hk, map_mul, inner_conj_symm]
      have h3 : (inner ℂ w (((-Complex.I) • T (orb g t)) : F) : ℂ) = ((-s : ℝ) : ℂ) * gf t := by
        rw [inner_smul_right, hconj, hgf]
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [h3] at h1
      exact h1
    have hb : ∀ t : ℝ, ‖gf t‖ ≤ ‖w‖ * ‖((orb g 0 : D) : F)‖ := by
      intro t
      calc ‖gf t‖ ≤ ‖w‖ * ‖((orb g t : D) : F)‖ := norm_inner_le_norm _ _
        _ = ‖w‖ * ‖((orb g 0 : D) : F)‖ := by rw [hnorm]
    have hss : (-s) * (-s) = 1 := by nlinarith
    exact BookProof.NavierStokesFlow.eq_zero_of_hasDerivAt_smul_of_bounded gf (-s)
      (‖w‖ * ‖((orb g 0 : D) : F)‖) hss hgd hb
  have hspan : ∀ v : (Submodule.span ℂ (Set.range fun g : G => ((orb g 0 : D) : F)) :
      Submodule ℂ F), (inner ℂ w (v : F) : ℂ) = 0 := by
    rintro ⟨v, hv⟩
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact key g
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]
  exact BookProof.NavierStokesFlow.eq_zero_of_inner_right_eq_zero_on_dense hdense w hspan

/-- Both deficiency spaces vanish, so the operator is essentially self-adjoint. -/
theorem essentiallySelfAdjointOn_of_orbits {G : Type*} (T : D →ₗ[ℂ] F) (orb : G → ℝ → D)
    (hnorm : ∀ (g : G) (t : ℝ), ‖((orb g t : D) : F)‖ = ‖((orb g 0 : D) : F)‖)
    (hderiv : ∀ (g : G) (t : ℝ), HasDerivAt (fun s : ℝ => ((orb g s : D) : F))
      ((-Complex.I) • T (orb g t)) t)
    (hdense : Dense ((Submodule.span ℂ (Set.range fun g : G => ((orb g 0 : D) : F)) :
      Submodule ℂ F) : Set F)) :
    EssentiallySelfAdjointOn D T := by
  constructor
  · have h := deficiencyTrivialAt_of_orbits T orb hnorm hderiv hdense 1 (by norm_num)
    simpa using h
  · have h := deficiencyTrivialAt_of_orbits T orb hnorm hderiv hdense (-1) (by norm_num)
    simpa using h

end Nelson

/-! ## The product rule for elementary tensors -/

section TmulDeriv

variable (E₁ E₂ : Type) [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂]

/-- Tensor multiplication as a real-bilinear map. -/
def tmulRlin : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] (E₁ ⊗[ℂ] E₂) where
  toFun a := ((TensorProduct.mk ℂ E₁ E₂ a).restrictScalars ℝ)
  map_add' a b := by ext y; simp
  map_smul' r a := by ext y; simp [TensorProduct.smul_tmul']

/-- Tensor multiplication is a bounded bilinear map (`‖a ⊗ b‖ = ‖a‖ ‖b‖`). -/
def tmulL : E₁ →L[ℝ] E₂ →L[ℝ] (E₁ ⊗[ℂ] E₂) :=
  LinearMap.mkContinuous₂ (tmulRlin E₁ E₂) 1 (by
    intro x y
    change ‖x ⊗ₜ[ℂ] y‖ ≤ 1 * ‖x‖ * ‖y‖
    rw [TensorProduct.norm_tmul, one_mul])

variable {E₁ E₂}

@[simp]
lemma tmulL_apply (a : E₁) (b : E₂) : tmulL E₁ E₂ a b = a ⊗ₜ[ℂ] b := rfl

local instance : ContinuousSMul ℝ (E₁ ⊗[ℂ] E₂) := by
  have h : IsBoundedSMul ℝ (E₁ ⊗[ℂ] E₂) := NormedSpace.toIsBoundedSMul
  haveI := h
  exact IsBoundedSMul.continuousSMul

set_option maxHeartbeats 2000000 in
/-- **The product rule for elementary tensors.**  `tmulL` is the bounded bilinear
tensor multiplication `a b ↦ a ⊗ₜ b`; `ContinuousLinearMap.hasDerivAt_of_bilinear`
applied to its flip gives the Leibniz rule with the summands in the stated order. -/
theorem hasDerivAt_tmul {f : ℝ → E₁} {g : ℝ → E₂} {f' : E₁} {g' : E₂} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => (f s) ⊗ₜ[ℂ] (g s)) (f' ⊗ₜ[ℂ] (g t) + (f t) ⊗ₜ[ℂ] g') t :=
  (tmulL E₁ E₂).flip.hasDerivAt_of_bilinear (fun _ => hg) (fun _ => hf)

end TmulDeriv

/-! ## The one-particle flow and its tensor powers -/

variable {Hs : IPSpace} {D₂ : Submodule ℂ Hs.carrier} {A : D₂ →ₗ[ℂ] Hs.carrier}

/-- **The unitary group of the one-particle operator.**  `U t` is a linear isometry of the
one-particle space with `U 0 = id` and `U (-t) ∘ U t = id`, it leaves the domain `D₂`
invariant, and on the domain it solves the Schrödinger equation `d/dt U t x = -i A (U t x)`
for every real time.  For a self-adjoint `A` this is exactly Stone's theorem; see
`ofSelfAdjoint`. -/
structure OneParticleFlow (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) where
  /-- the group of evolution operators -/
  U : ℝ → Hs.carrier →ₗ[ℂ] Hs.carrier
  /-- the evolution preserves the norm -/
  norm_U : ∀ (t : ℝ) (x : Hs.carrier), ‖U t x‖ = ‖x‖
  /-- it starts at the identity -/
  U_zero : ∀ x : Hs.carrier, U 0 x = x
  /-- it is invertible, with inverse the backwards evolution -/
  U_neg : ∀ (t : ℝ) (x : Hs.carrier), U (-t) (U t x) = x
  /-- the domain is invariant -/
  mem_domain : ∀ (t : ℝ) (x : D₂), U t (x : Hs.carrier) ∈ D₂
  /-- the Schrödinger equation on the domain, for all times -/
  hasDerivAt_U : ∀ (x : D₂) (t : ℝ),
    HasDerivAt (fun s : ℝ => U s (x : Hs.carrier))
      ((-Complex.I) • A ⟨U t (x : Hs.carrier), mem_domain t x⟩) t

namespace OneParticleFlow

variable (P : OneParticleFlow Hs D₂ A)

/-- The flow, restricted to the invariant domain. -/
def dmap (t : ℝ) : D₂ →ₗ[ℂ] D₂ where
  toFun x := ⟨P.U t (x : Hs.carrier), P.mem_domain t x⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

@[simp] theorem dmap_coe (t : ℝ) (x : D₂) :
    ((dmap P t x : D₂) : Hs.carrier) = P.U t (x : Hs.carrier) := rfl

theorem norm_dmap (t : ℝ) (x : D₂) : ‖dmap P t x‖ = ‖x‖ := by
  change ‖((dmap P t x : D₂) : Hs.carrier)‖ = ‖(x : Hs.carrier)‖
  rw [dmap_coe, P.norm_U]

theorem dmap_neg (t : ℝ) (x : D₂) : dmap P (-t) (dmap P t x) = x := by
  apply Subtype.ext
  simp [P.U_neg]

/-- The tensor power `U t ⊗ ⋯ ⊗ U t` of the flow, acting on the tensor power of the
domain. -/
def tpow (t : ℝ) : ∀ n : ℕ, ((domSpace Hs D₂).pow n) →ₗ[ℂ] ((domSpace Hs D₂).pow n)
  | 0 => LinearMap.id
  | (n + 1) => TensorProduct.map (dmap P t) (tpow t n)

theorem tpow_succ (t : ℝ) (n : ℕ) :
    tpow P t (n + 1) = TensorProduct.map (dmap P t) (tpow P t n) := rfl

@[simp] theorem tpow_tmul (t : ℝ) (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    tpow P t (n + 1) (a ⊗ₜ[ℂ] b) = (dmap P t a) ⊗ₜ[ℂ] (tpow P t n b) := by
  rw [tpow_succ]
  exact TensorProduct.map_tmul _ _ _ _

theorem tpow_zero_time : ∀ (n : ℕ) (x : ((domSpace Hs D₂).pow n)), tpow P 0 n x = x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have hx : x ∈ Submodule.span ℂ
          {u : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = u} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨p, q, rfl⟩ := hy
          rw [tpow_tmul, ih q]
          congr 1
          apply Subtype.ext
          simp [P.U_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | smul c a _ ha => rw [map_smul, ha]

theorem norm_tpow_le : ∀ (t : ℝ) (n : ℕ) (x : ((domSpace Hs D₂).pow n)),
    ‖tpow P t n x‖ ≤ ‖x‖ := by
  intro t n
  induction n with
  | zero => intro x; simp [tpow]
  | succ n ih =>
      intro x
      have h := norm_map_le (dmap P t) (tpow P t n) zero_le_one zero_le_one
        (fun a => by rw [norm_dmap]; simp) (fun b => by rw [one_mul]; exact ih b) x
      rw [tpow_succ]
      simpa using h

theorem tpow_neg : ∀ (t : ℝ) (n : ℕ) (x : ((domSpace Hs D₂).pow n)),
    tpow P (-t) n (tpow P t n x) = x := by
  intro t n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have hx : x ∈ Submodule.span ℂ
          {u : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = u} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨p, q, rfl⟩ := hy
          rw [tpow_tmul, tpow_tmul, dmap_neg, ih q]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
      | smul c a _ ha => rw [map_smul, map_smul, ha]

theorem norm_tpow (t : ℝ) (n : ℕ) (x : ((domSpace Hs D₂).pow n)) : ‖tpow P t n x‖ = ‖x‖ := by
  refine le_antisymm (norm_tpow_le P t n x) ?_
  have h := norm_tpow_le P (-t) n (tpow P t n x)
  rwa [tpow_neg P t n x] at h

/-- **The Leibniz rule for the tensor flow.**  The tensor power of the one-particle flow
solves the Schrödinger equation of the sector derivation. -/
theorem hasDerivAt_tpow : ∀ (n : ℕ) (x : ((domSpace Hs D₂).pow n)) (t : ℝ),
    HasDerivAt (fun s : ℝ => inclPow Hs D₂ n (tpow P s n x))
      ((-Complex.I) • derPow Hs D₂ A n (tpow P t n x)) t := by
  intro n
  induction n with
  | zero =>
      intro x t
      have h : HasDerivAt (fun _ : ℝ => inclPow Hs D₂ 0 x) 0 t := hasDerivAt_const _ _
      have heq : (fun s : ℝ => inclPow Hs D₂ 0 (tpow P s 0 x))
          = fun _ : ℝ => inclPow Hs D₂ 0 x := rfl
      rw [heq, derPow_zero]
      simpa using h
  | succ n ih =>
      haveI : ContinuousSMul ℝ (Hs.pow (n + 1)).carrier := by
        have h : IsBoundedSMul ℝ (Hs.pow (n + 1)).carrier := NormedSpace.toIsBoundedSMul
        haveI := h
        exact IsBoundedSMul.continuousSMul
      have hpure : ∀ (a : D₂) (b : ((domSpace Hs D₂).pow n)) (t : ℝ),
          HasDerivAt (fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) (a ⊗ₜ[ℂ] b)))
            ((-Complex.I) • derPow Hs D₂ A (n + 1) (tpow P t (n + 1) (a ⊗ₜ[ℂ] b))) t := by
        intro a b t
        have hf : HasDerivAt (fun s : ℝ => P.U s (a : Hs.carrier))
            ((-Complex.I) • A ⟨P.U t (a : Hs.carrier), P.mem_domain t a⟩) t :=
          P.hasDerivAt_U a t
        have hg : HasDerivAt (fun s : ℝ => inclPow Hs D₂ n (tpow P s n b))
            ((-Complex.I) • derPow Hs D₂ A n (tpow P t n b)) t := ih b t
        have h := hasDerivAt_tmul hf hg
        have hcurve : (fun s : ℝ => (P.U s (a : Hs.carrier)) ⊗ₜ[ℂ]
              (inclPow Hs D₂ n (tpow P s n b)))
            = fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) (a ⊗ₜ[ℂ] b)) := by
          funext s
          rw [tpow_tmul, inclPow_tmul, dmap_coe]
        rw [hcurve] at h
        have hval : ((-Complex.I) • A ⟨P.U t (a : Hs.carrier), P.mem_domain t a⟩)
              ⊗ₜ[ℂ] (inclPow Hs D₂ n (tpow P t n b))
            + (P.U t (a : Hs.carrier)) ⊗ₜ[ℂ]
                ((-Complex.I) • derPow Hs D₂ A n (tpow P t n b))
            = (-Complex.I) • derPow Hs D₂ A (n + 1) (tpow P t (n + 1) (a ⊗ₜ[ℂ] b)) := by
          rw [tpow_tmul, derPow_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            ← smul_add, dmap_coe]
          rfl
        rw [hval] at h
        exact h
      intro x t
      have hx : x ∈ Submodule.span ℂ
          {u : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = u} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨p, q, rfl⟩ := hy; exact hpure p q t
      | zero =>
          have heq : (fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) 0))
              = fun _ : ℝ => inclPow Hs D₂ (n + 1) (0 : _) := by
            funext s
            simp [tpow_succ]
          rw [heq]
          rw [show (-Complex.I) • derPow Hs D₂ A (n + 1) (tpow P t (n + 1) 0)
              = (0 : (Hs.pow (n + 1)).carrier) by simp [tpow_succ]]
          exact hasDerivAt_const _ _
      | add a b _ _ ha hb =>
          have h := ha.add hb
          rw [show (fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) a))
                + (fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) b))
                = fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) a)
                    + inclPow Hs D₂ (n + 1) (tpow P s (n + 1) b) from rfl] at h
          simpa [map_add, smul_add] using h
      | smul c a _ ha =>
          have h := ha.const_smul c
          have hfun : (c • fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) a))
              = fun s : ℝ => inclPow Hs D₂ (n + 1) (tpow P s (n + 1) (c • a)) := by
            funext s
            simp
          rw [hfun] at h
          have hval : c • ((-Complex.I) • derPow Hs D₂ A (n + 1) (tpow P t (n + 1) a))
              = (-Complex.I) • derPow Hs D₂ A (n + 1) (tpow P t (n + 1) (c • a)) := by
            rw [map_smul, map_smul]
            exact smul_comm c (-Complex.I) _
          rw [hval] at h
          exact h

/-! ## The orbits in the completed sector -/

/-- The orbit of a vector of the tensor power of the domain, inside the completed sector. -/
def fockOrbit (n : ℕ) (x : ((domSpace Hs D₂).pow n)) (t : ℝ) : fockSectorDom Hs D₂ n :=
  ⟨sectorEmb Hs n (inclPow Hs D₂ n (tpow P t n x)),
    mem_pushDom (sectorEmb Hs n)
      (⟨inclPow Hs D₂ n (tpow P t n x), ⟨tpow P t n x, rfl⟩⟩ : sectorDom Hs D₂ n)⟩

@[simp] theorem fockOrbit_coe (n : ℕ) (x : ((domSpace Hs D₂).pow n)) (t : ℝ) :
    ((fockOrbit P n x t : fockSectorDom Hs D₂ n) : fockSector Hs n)
      = sectorEmb Hs n (inclPow Hs D₂ n (tpow P t n x)) := rfl

theorem fockOrbit_zero (n : ℕ) (x : ((domSpace Hs D₂).pow n)) :
    ((fockOrbit P n x 0 : fockSectorDom Hs D₂ n) : fockSector Hs n)
      = sectorEmb Hs n (inclPow Hs D₂ n x) := by
  rw [fockOrbit_coe, tpow_zero_time]

theorem norm_fockOrbit (n : ℕ) (x : ((domSpace Hs D₂).pow n)) (t : ℝ) :
    ‖((fockOrbit P n x t : fockSectorDom Hs D₂ n) : fockSector Hs n)‖
      = ‖((fockOrbit P n x 0 : fockSectorDom Hs D₂ n) : fockSector Hs n)‖ := by
  rw [fockOrbit_coe, fockOrbit_zero, (sectorEmb Hs n).norm_map, (sectorEmb Hs n).norm_map,
    (inclPow Hs D₂ n).norm_map, (inclPow Hs D₂ n).norm_map, norm_tpow]

theorem fockSectorOp_fockOrbit (n : ℕ) (x : ((domSpace Hs D₂).pow n)) (t : ℝ) :
    fockSectorOp Hs D₂ A n (fockOrbit P n x t)
      = sectorEmb Hs n (derPow Hs D₂ A n (tpow P t n x)) := by
  have hx₀ : ((fockOrbit P n x t : fockSectorDom Hs D₂ n) : fockSector Hs n)
      = sectorEmb Hs n ((⟨inclPow Hs D₂ n (tpow P t n x), ⟨tpow P t n x, rfl⟩⟩ :
        sectorDom Hs D₂ n) : (Hs.pow n).carrier) := rfl
  have h1 : fockSectorOp Hs D₂ A n (fockOrbit P n x t)
      = sectorEmb Hs n (sectorOp Hs D₂ A n
        (⟨inclPow Hs D₂ n (tpow P t n x), ⟨tpow P t n x, rfl⟩⟩ : sectorDom Hs D₂ n)) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D₂ A n) _ _ hx₀
  rw [h1, sectorOp_apply Hs D₂ A n _ (tpow P t n x) rfl]

theorem hasDerivAt_fockOrbit (n : ℕ) (x : ((domSpace Hs D₂).pow n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((fockOrbit P n x s : fockSectorDom Hs D₂ n) : fockSector Hs n))
      ((-Complex.I) • fockSectorOp Hs D₂ A n (fockOrbit P n x t)) t := by
  have h := hasDerivAt_tpow P n x t
  have hcomp := (((sectorEmb Hs n).toContinuousLinearMap.restrictScalars
    ℝ).hasFDerivAt).comp_hasDerivAt t h
  rw [fockSectorOp_fockOrbit]
  have hval : ((sectorEmb Hs n).toContinuousLinearMap.restrictScalars ℝ)
      ((-Complex.I) • derPow Hs D₂ A n (tpow P t n x))
      = (-Complex.I) • sectorEmb Hs n (derPow Hs D₂ A n (tpow P t n x)) := by
    simp
  rw [hval] at hcomp
  exact hcomp

/-! ## The sector hypothesis, and the main theorem -/

include P in
/-- **The sector hypothesis, proved for a one-particle operator with a unitary flow** — in
particular for every self-adjoint one-particle operator, bounded or not, with arbitrary
spectrum. -/
theorem essentiallySelfAdjointOn_fockSectorDom_flow (hdense : Dense (D₂ : Set Hs.carrier))
    (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n) := by
  have hspanD : Dense ((Submodule.span ℂ (Set.range fun i : D₂ => (i : Hs.carrier)) :
      Submodule ℂ Hs.carrier) : Set Hs.carrier) := by
    have hrange : (Set.range fun i : D₂ => (i : Hs.carrier)) = (D₂ : Set Hs.carrier) :=
      Subtype.range_coe
    rw [hrange, Submodule.span_eq]
    exact hdense
  have hdense' : Dense ((Submodule.span ℂ (Set.range fun x : ((domSpace Hs D₂).pow n) =>
      ((fockOrbit P n x 0 : fockSectorDom Hs D₂ n) : fockSector Hs n)) :
      Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n)) := by
    refine Dense.mono ?_ (dense_span_fockEigVec Hs D₂ (fun i : D₂ => i) hspanD n)
    refine Submodule.span_le.mpr ?_
    rintro y ⟨f, rfl⟩
    refine Submodule.subset_span ⟨eigTensor Hs D₂ (fun i : D₂ => i) n f, ?_⟩
    have heq : ((fockOrbit P n (eigTensor Hs D₂ (fun i : D₂ => i) n f) 0 :
        fockSectorDom Hs D₂ n) : fockSector Hs n)
        = fockEigVec Hs D₂ (fun i : D₂ => i) n f := by
      rw [fockOrbit_zero]
      rfl
    exact heq
  exact essentiallySelfAdjointOn_of_orbits _ (fun x => fockOrbit P n x)
    (fun x t => norm_fockOrbit P n x t) (fun x t => hasDerivAt_fockOrbit P n x t) hdense'

include P in
/-- **Main theorem for a one-particle operator with a unitary flow.**  `dΓ(A)` is essentially
self-adjoint on the finite-particle domain built from any graph-norm core `D` of `A`. -/
theorem dGamma_flow_essentiallySelfAdjointOn_fockCore (hdense : Dense (D₂ : Set Hs.carrier))
    (D : Submodule ℂ Hs.carrier) (hcore : IsGraphCore D A) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n))
      (dGammaCoreOp Hs D₂ A D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs D₂ A D hcore
    (essentiallySelfAdjointOn_fockSectorDom_flow P hdense)

end OneParticleFlow

/-! ## Stone's theorem: every self-adjoint one-particle operator carries a flow -/

section SelfAdjoint

open BookProof.ChapterStoneResolvent

variable {Hs : IPSpace} [CompleteSpace Hs.carrier]

/-- **The flow of a self-adjoint one-particle operator**, supplied by Stone's theorem
(`UnboundedSelfAdjoint.stoneU`): no boundedness, positivity or spectral hypothesis. -/
def ofSelfAdjoint (T : UnboundedSelfAdjoint Hs.carrier) :
    OneParticleFlow Hs T.domain T.op where
  U t := (T.stoneU t : Hs.carrier →L[ℂ] Hs.carrier).toLinearMap
  norm_U t x := T.norm_stoneU_apply t x
  U_zero x := by simp
  U_neg t x := by
    change T.stoneU (-t) (T.stoneU t x) = x
    rw [T.stoneU_apply_stoneU]
    simp
  mem_domain t x := T.stoneU_mem_domain t x
  hasDerivAt_U x t := T.hasDerivAt_stoneU_op x t

/-- **The theorem, with no hypothesis left over.**  For every self-adjoint one-particle
operator `A` — unbounded, with arbitrary spectrum, no positivity — and every graph-norm core
`D` of `A`, the second quantization `dΓ(A)` is essentially self-adjoint on the finite-particle
domain `𝓕_fin(D)` built from `D` alone.  `D` is only a core: it is not invariant under the
unitary group, and no resolvent of `A` on `D` is used. -/
theorem dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore
    (T : UnboundedSelfAdjoint Hs.carrier) (D : Submodule ℂ Hs.carrier)
    (hcore : IsGraphCore D T.op) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs T.domain D n))
      (dGammaCoreOp Hs T.domain T.op D) :=
  OneParticleFlow.dGamma_flow_essentiallySelfAdjointOn_fockCore (ofSelfAdjoint T)
    T.denseDomain D hcore

/-- The sectorwise input of the packaged theorem, for a self-adjoint one-particle
operator. -/
theorem essentiallySelfAdjointOn_fockSectorDom_selfAdjoint
    (T : UnboundedSelfAdjoint Hs.carrier) (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs T.domain n) (fockSectorOp Hs T.domain T.op n) :=
  OneParticleFlow.essentiallySelfAdjointOn_fockSectorDom_flow (ofSelfAdjoint T)
    T.denseDomain n

/-- **The packaged form.**  For a self-adjoint one-particle operator and a graph-norm core
`D`, this is an `ESAPair` whose sectorwise input is *proved*, not assumed; the packaged
theorem `ESAPair.dGamma_essentiallySelfAdjoint` therefore applies with no hypothesis left
over. -/
def esaPairOfSelfAdjoint (T : UnboundedSelfAdjoint Hs.carrier) (D : Submodule ℂ Hs.carrier)
    (hsub : D ≤ T.domain) (hcore : IsGraphCore D T.op) : ESAPair Hs where
  closureDomain := T.domain
  closureOp := T.op
  symmetric := T.symmetric
  sector_esa := essentiallySelfAdjointOn_fockSectorDom_selfAdjoint T
  coreDomain := D
  sub_domain := hsub
  is_core := hcore

end SelfAdjoint

/-! ## A genuinely unbounded instance: the position operator on `ℓ²(ℤ)`

Nothing above is vacuous.  `BookProof.ChapterStoneSeparable.mulSA positionField` is
multiplication by `k` on `ℓ²(ℤ)`, a self-adjoint operator which is *not* bounded
(`mulSA_position_unbounded`) and whose eigenvalues are unbounded in both directions.  The
theorem applies to it with no hypothesis beyond `D` being a graph-norm core. -/

section Position

open BookProof.ChapterStoneResolvent BookProof.ChapterStoneSeparable
  BookProof.ChapterUnboundedPosition

/-- `ℓ²(ℤ)` as a bundled inner product space. -/
def L2ZSpace : IPSpace := ⟨BookProof.ChapterContinuityUnitaryInfinite.L2Z⟩

instance : CompleteSpace L2ZSpace.carrier :=
  inferInstanceAs (CompleteSpace (BookProof.ChapterContinuityUnitaryInfinite.L2Z))

/-- **Second quantization of the position operator.**  `A` is multiplication by `k` on
`ℓ²(ℤ)` — self-adjoint and unbounded above and below — and `D` is any graph-norm core of it.
Then `dΓ(A)` is essentially self-adjoint on the finite-particle domain over `D`. -/
theorem dGamma_position_essentiallySelfAdjointOn_fockCore
    (D : Submodule ℂ L2ZSpace.carrier)
    (hcore : IsGraphCore D (mulSA positionField).op) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore L2ZSpace (mulSA positionField).domain D n))
      (dGammaCoreOp L2ZSpace (mulSA positionField).domain (mulSA positionField).op D) :=
  dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore (Hs := L2ZSpace) (mulSA positionField)
    D hcore

/-- The one-particle operator of the previous theorem is genuinely unbounded. -/
theorem position_not_bounded :
    ¬ ∃ C : ℝ, ∀ x : (mulSA positionField).domain,
      ‖(mulSA positionField).op x‖ ≤ C * ‖(x : BookProof.ChapterContinuityUnitaryInfinite.L2Z)‖ :=
  BookProof.ChapterStoneSeparable.mulSA_position_unbounded

end Position

end

end BookProof.FlowDGamma


