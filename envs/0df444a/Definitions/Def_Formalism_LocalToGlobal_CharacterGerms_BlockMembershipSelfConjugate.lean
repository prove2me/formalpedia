-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
-- name    : Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:46.725873+00:00
-- url     : https://prove2.me/theorems/c72bc761-ffb7-44d8-b41b-044384273331
-- title:
--   Block Membership Self Conjugate
-- statement:
--   Definitions and structural lemmas for Block Membership Self Conjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
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
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
section SlopeTestRemainingChoices
variable {C : Type} [Field C] {V : VF C} {d : ℕ}
end SlopeTestRemainingChoices
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)
def ValO (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ) : Prop :=
  ∀ Po ∈ FFimg, ∀ kind : Orb → Fin n → Knd d, (∀ o, RowsOK (X o).G (X o).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys ((X o).G g)) (t : ∀ o g, I o g → MvPowerSeries (I o g) C), (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      (ν : WithTop ℝ) ≤ ∑ o, V.v (ValOf (X o).hL (Po o) (kind o) (gr o))
def plAt {K : Orb → ℕ} {what₂ : ∀ o, Fin (K o) → ℕ} (pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n) (o : Orb) :
    (Σ i : Fin (K o), Fin (what₂ o i)) → Fin n := fun s => pl ⟨o, s⟩
variable {X n}
def GlobalTheory.AttainsOK {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X)
    (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ kind : Fin (b.what₂ X.n) → Knd d, RowsOK X.G X.Alt (b.poly X F) kind ∧
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (b.poly X F) kind gr) ≤ ((c : ℝ) : WithTop ℝ)
abbrev blkAt (L : Orb → List (GlobalTheory d × ℝ)) (o : Orb) (i : Fin (L o).length) : GlobalTheory d := ((L o).get i).1
variable (X) in

abbrev rowsAt (L : Orb → List (GlobalTheory d × ℝ)) (o : Orb) (i : Fin (L o).length) : ℕ := (blkAt L o i).what₂ (X o).n
variable (X n) in

def ProdMem (F : ∀ o, Flag (X o)) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (L : Orb → List (GlobalTheory d × ℝ)) : Prop :=
  ∀ pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n, Function.Injective pl →
    (fun o => prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)) ∈ FFimg
variable (X n)
def BlockMembership (F : ∀ o, Flag (X o)) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ), (∀ o, o ∉ Z → L o = []) →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun q => q.1.wt (X o) g a k).sum = ga o g a k) → ProdMem X n F FFimg L
def BlockAdmissible (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun q => q.1.wt (X o) g a k).sum = ga o g a k) →
    ∀ o ∈ Z, ∀ q ∈ L o, q.1.Attains (X o) (F o) q.2 → q.1.AttainsOK (X o) (F o) q.2
variable {X n}
end Formalism.L2.FormalSeriesBounds.RF
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (n : ℕ)
def BlockMembershipSelfConjugate (F : ∀ o, Flag (X o)) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o, ∀ q ∈ L o, ∀ g e N, q.1 = GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0) →
    (∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) → ProdMem X n F FFimg L
def BlockAdmissibleSelfConjugate (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) →
    ∀ o, ∀ q ∈ L o, q.1.Attains (X o) (F o) q.2 → q.1.AttainsOK (X o) (F o) q.2
variable {X n}
end Formalism.L2.FormalSeriesBounds.RF


