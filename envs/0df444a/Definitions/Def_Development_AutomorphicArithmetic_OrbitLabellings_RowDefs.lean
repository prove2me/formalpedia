-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
-- name    : Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:37.826568+00:00
-- url     : https://prove2.me/theorems/9989aee5-7fd8-4231-bf6e-e4d6975fbf10
-- title:
--   Row Defs
-- statement:
--   Definitions and structural lemmas for Row Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/RowDefs.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RestNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
namespace UpperTheory.G2
section Blocks
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
def OneType (L : Orb → List (RF.GlobalTheory d × ℝ)) : Prop :=
  ∀ o, ∀ q ∈ L o, ∀ g e N, q.1 = RF.GlobalTheory.mon g e N → ∃ s : ZMod d, ∀ a k, a ≠ s → e a k = 0
def WtSum (hd : ZMod d) (X : ∀ o, RowData C V d (I o) (J o)) (ga : Orb → ZMod d → ℕ → ℕ) (L : Orb → List (RF.GlobalTheory d × ℝ)) : Prop :=
  ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + hd) k).sum = ga o s k
def ValBlocksS (hd : ZMod d) (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, RF.Flag (X o)) (nW : ℕ)
    (ga : Orb → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (RF.GlobalTheory d × ℝ), (∀ o, ∀ q ∈ L o, q.1.Attains (X o) (F o) q.2) → OneType L →
    2 * (∑ o, ((L o).map fun q => q.1.what₂ (X o).n).sum) ≤ nW → WtSum hd X ga L → ν ≤ ∑ o, ((L o).map Prod.snd).sum
def PlaneBlockProductsMemFamily (hd : ZMod d) (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (F : ∀ o, RF.Flag (X o))
    (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ga : Orb → ZMod d → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (RF.GlobalTheory d × ℝ), OneType L → WtSum hd X ga L → RF.ProdMem X n F FFimg L
end Blocks
def WtTieS {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → ZMod d → T) (ga : Orb → ZMod d → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o s (i : ℕ), i < r (tau o s) → a (tau o s) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o s)), ga o s k) ∧
  ∀ σ, (∀ o s, tau o s ≠ σ) → ∀ i, i < r σ → a σ i = 0
structure RowFamS (P : RF.Par) (l : ℕ) (Z : Finset P.Pl) : Type 1 where
  C : Type
  [fC : Field C]
  V : VF C
  hVl : V.l = l
  I : {z // z ∈ Z} → Fin 2 → Type
  J : {z // z ∈ Z} → Fin 2 → Type
  [fI : ∀ o g, Fintype (I o g)]
  [fJ : ∀ o g, Fintype (J o g)]
  X : ∀ o, RowData C V (2 * P.d) (I o) (J o)
  F : ∀ o, RF.Flag (X o)
  hn : ∀ o, (X o).n = P.k - 1 ∧ (X o).m = P.m
  alt : ∀ o, (X o).Alt
attribute [instance] RowFamS.fC RowFamS.fI RowFamS.fJ
structure PkgCs (P : RF.Par) (l : ℕ) (C1 : ℝ) : Type 1 where
  odd : Odd P.d
  Z : Finset P.Pl
  hZ : RF.IsReps P Z
  R : RowFamS P l Z
  ga : {z // z ∈ Z} → ZMod (2 * P.d) → ℕ → ℕ
  W : P.Pl → ℕ
  nW : ℕ
  T : ℝ
  θ0 : ℝ
  rest : ℝ
  ν : ℝ
  supp : ∀ o s k, ga o s k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X o).rkF 0 s
  main : ∀ o (s : ZMod (2 * P.d)), Even s.val → ga o s (P.k - 1) = W (P.pos o.1 (s.val % P.d))
  rest_eq : rest = ∑ o, ∑ s : ZMod (2 * P.d), ∑ k ∈ Finset.Icc 1 P.r,
    (if Even s.val ∧ k = P.k - 1 then (0 : ℝ) else (k : ℝ) * ga o s k)
  what₂ : P.f * ((RF.i0 P.k l + 1) * (P.k - 1) + 4 * P.r) ≤ nW
  deg : RF.DegHyp2 P W T θ0 rest C1
  val : ValBlocksS (P.d : ZMod (2 * P.d)) R.X R.F nW ga ν
structure PkgZeroCs (P : RF.Par) (l : ℕ) : Type 1 where
  Z : Finset P.Pl
  R : RowFamS P l Z
  ga : {z // z ∈ Z} → ZMod (2 * P.d) → ℕ → ℕ
  K : ℕ
  s : ℕ
  nW : ℕ
  T : ℝ
  ν : ℝ
  T_one : 1 ≤ T
  w_nonneg : ∀ z, 0 ≤ P.w z
  supp : ∀ o σ k, ga o σ k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X o).rkF 0 σ ∧ k ≤ K
  first : ∀ o σ, ∑ k ∈ Finset.Icc 1 K, ga o σ k ≤ s * (l - 1)
  what₂ : 4 * K * s * (Z.card * P.d) ≤ nW
  val : ValBlocksS (P.d : ZMod (2 * P.d)) R.X R.F nW ga ν
end UpperTheory.G2
end


