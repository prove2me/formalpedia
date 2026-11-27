-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuotientNormSquareData
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuotientNormSquareData
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T05:06:26.64138+00:00
-- url     : https://prove2.me/theorems/5dab11a9-8f23-5a19-8a94-633e572ef211
-- title:
--   Quotient Norm Square Data
-- statement:
--   Definitions and structural lemmas for Quotient Norm Square Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuotientNormSquareData.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData
variable {L : Type} [Field L] [NumberField L]
def quotNormSq {κ τ : Type} [Fintype κ] [DecidableEq κ] (X : InfinitePlace L → Matrix κ κ ℂ)
    (V : Submodule L (κ → L)) (A : Matrix τ κ L) (p : InfinitePlace L) (y : τ → L) : ℝ :=
  sInf {s : ℝ | ∃ F ∈ V, A.mulVec F = y ∧ s = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun L κ) X p F ^ 2}
structure RowData (L : Type) [Field L] [NumberField L] (T : Type) (κ : T → Type)
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] (τ ε C : Type) [Fintype ε] [DecidableEq ε]
    (m : ℕ) where

  t₀ : T

  tup : HeightOneSpectrum (𝓞 L) → T
  tup_finite : {w | tup w ≠ t₀}.Finite

  M : ∀ t, Submodule (𝓞 L) (κ t → L)
  M_lattice : ∀ t, Submodule.IsLattice L (M t)

  V₀ : ∀ t, Submodule L (κ t → L)

  v : ∀ t, Matrix τ (κ t) L

  r : T → Lˣ
  r_ref : r t₀ = 1

  X₀ : InfinitePlace L → Matrix (κ t₀) (κ t₀) ℂ
  X₀_unit : ∀ p, IsUnit (X₀ p).det

  psi : Matrix τ ε L
  psi_injective : Function.Injective psi.mulVecLin
  psi_range : LinearMap.range psi.mulVecLin = (V₀ t₀).map (v t₀).mulVecLin

  part : C → Submodule L (ε → L)
  part_span : ⨆ c, part c = ⊤

  lam : InfinitePlace L → Fin m → C → ℝ
  lam_pos : ∀ p j c, 0 < lam p j c

  kap : InfinitePlace L → ℝ
  kap_pos : ∀ p, 0 < kap p

  XE : InfinitePlace L → Matrix ε ε ℂ
  XE_unit : ∀ p, IsUnit (XE p).det
  XE_norm : ∀ p c, ∀ x ∈ part c, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun L ε) XE p x ^ 2 =
    kap p * (∏ j, lam p j c) * quotNormSq X₀ (V₀ t₀) (v t₀) p (psi.mulVec x)
  XE_orth : ∀ p c c', c ≠ c' → ∀ x ∈ part c, ∀ y ∈ part c',
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun L ε) XE p x y = 0
namespace RowData
variable {T : Type} {κ : T → Type} [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)]
  {τ ε C : Type} [Fintype ε] [DecidableEq ε] {m : ℕ} (D : RowData L T κ τ ε C m)
def rowLat (t : T) : Submodule (𝓞 L) (ε → L) :=
  ((D.M t ⊓ (D.V₀ t).restrictScalars (𝓞 L)).map
    (((((D.r t)⁻¹ : Lˣ) : L) • (D.v t).mulVecLin).restrictScalars (𝓞 L))).comap
    (D.psi.mulVecLin.restrictScalars (𝓞 L))
def glued : Submodule (𝓞 L) (ε → L) where
  carrier := {x | ∀ w : HeightOneSpectrum (𝓞 L),
    ∃ s : 𝓞 L, s ∉ w.asIdeal ∧ s • x ∈ D.rowLat (D.tup w)}
  zero_mem' := fun w => ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by simp⟩
  add_mem' := by
    intro x y hx hy w
    obtain ⟨s, hs, hx⟩ := hx w
    obtain ⟨s', hs', hy⟩ := hy w
    refine ⟨s * s', fun h => (w.isPrime.mem_or_mem h).elim hs hs', ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  smul_mem' := by
    intro a x hx w
    obtain ⟨s, hs, hx⟩ := hx w
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hx
def logKap : ℝ :=
  (1 / (finrank ℚ L : ℝ)) * ∑ φ : L →+* ℂ, Real.log (D.kap (InfinitePlace.mk φ))
def SlopeBound [StarRing L] (hh : ℝ) : Prop :=
  ∀ K' : Submodule (𝓞 L) (ε → L), K' ≤ D.glued → K' ≠ ⊥ →
    Formalism.HN.muDef (Pi.basisFun L ε) D.XE K' ≤ hh - D.logKap
end RowData
def RowSlopeBound {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] [StarRing L]
    {T : Type} [Finite T]
    {κ : T → Type} [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] {τ ε C : Type} [Fintype ε]
    [DecidableEq ε] {m : ℕ} (D : RowData L T κ τ ε C m) (x e CH : ℝ) (_hx : 0 < x) : Prop :=
  D.SlopeBound (x ^ CH * Real.exp (x ^ e))
open Classical in

def sample (ι : Type) [Fintype ι] [DecidableEq ι] (w₀ : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    RowData L Bool (fun _ => ι) ι ι Unit 1 where
  t₀ := false
  tup w := if w = w₀ then true else false
  tup_finite := (Set.finite_singleton w₀).subset fun w hw => by
    by_contra h
    exact hw (if_neg h)
  M _ := Submodule.span (𝓞 L) (Set.range (Pi.basisFun L ι))
  M_lattice _ := ⟨Submodule.fg_span (Set.finite_range _), by
    rw [Submodule.span_span_of_tower]; exact (Pi.basisFun L ι).span_eq⟩
  V₀ _ := ⊤
  v _ := 1
  r t := if t then a else 1
  r_ref := rfl
  X₀ _ := 1
  X₀_unit _ := by simp
  psi := 1
  psi_injective := by simpa using Function.injective_id
  psi_range := by simp
  part _ := ⊤
  part_span := by simp
  lam _ _ _ := 1
  lam_pos _ _ _ := one_pos
  kap _ := 1
  kap_pos _ := one_pos
  XE _ := 1
  XE_unit _ := by simp
  XE_norm p c x _ := by simp [quotNormSq]
  XE_orth _ _ _ h := (h rfl).elim
end GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData


