-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
-- name    : LeanPool_BlockSpectralSensitivity_LLL_Obstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:58:48.626914+00:00
-- url     : https://prove2.me/theorems/edc323ea-9563-4b50-9b5d-1ce4d1e2968c
-- title:
--   Obstruction
-- statement:
--   Definitions and structural lemmas for Obstruction, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
abbrev GateCfg (ι : Type*) (r : ℕ) : Type _ := ι × ι → Fin r
def toGamma : GateCfg ι r → ι → ι → Fin r := Function.curry
def ownerGates (i : ι) (T : Finset ι) : Finset (ι × ι) := {i} ×ˢ T
def arcSet (Arc : ι → ι → Bool) (T : Finset ι) : Finset (ι × ι) :=
  T.offDiag.filter fun p => Arc p.1 p.2 = true
section ArcSet
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
variable (hT : IsTournament Arc)
include hT
end ArcSet
def missSet (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) (Z : ι → Finset (Fin r)) (T : Finset ι)
    (i : ι) : Finset ι :=
  T.filter fun j => Arc i j = true ∧ γ i j ∉ Z j
section MissSet
omit [Fintype ι] [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ γ' : ι → ι → Fin r} {Z : ι → Finset (Fin r)}
  {T T' S : Finset ι} {i j : ι}
end MissSet
def IntObstruction (Arc : ι → ι → Bool) (ell : ℕ) (S : Finset ι) (h : ι)
    (γ : ι → ι → Fin r) : Prop :=
  ∃ Z : ι → Finset (Fin r),
    Z h = ∅ ∧
    (∀ j ∈ S, Arc h j → γ h j ∈ Z j) ∧
    (∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ ell)
def zeroSet (x : Input (Construction.Coord ι r)) (i : ι) : Finset (Fin r) :=
  Finset.univ.filter fun k => x (i, k) = false
@[ext]
structure Flag1 (ι : Type*) [DecidableEq ι] where
  /-- The proposed owner. -/
  owner : ι
  /-- The second top vertex, for `Type B` patterns. -/
  top : Option ι
  /-- The bottom vertices. -/
  bot : Finset ι
namespace Flag1
def equivProd : Flag1 ι ≃ ι × Option ι × Finset ι where
  toFun F := (F.owner, F.top, F.bot)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance : DecidableEq (Flag1 ι) := equivProd.injective.decidableEq
instance : Fintype (Flag1 ι) := .ofEquiv _ equivProd.symm
def nonOwners (F : Flag1 ι) : Finset ι :=
  match F.top with
  | none => F.bot
  | some v => insert v F.bot
def supp (F : Flag1 ι) : Finset ι := insert F.owner F.nonOwners
section Membership
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}
def Active (F : Flag1 ι) (Arc : ι → ι → Bool) : Prop :=
  F.owner ∉ F.nonOwners ∧
  match F.top with
  | none => F.bot.card = 4 ∧ ∀ j ∈ F.bot, Arc F.owner j = true
  | some v =>
    v ∉ F.bot ∧ F.bot.card = 3 ∧ Arc v F.owner = true ∧
      ∀ j ∈ F.bot, Arc F.owner j = true ∧ Arc v j = true
namespace Active
variable (hF : F.Active Arc)
include hF
end Active
end Membership
end Flag1
noncomputable def flagEvent (Arc : ι → ι → Bool) (F : Flag1 ι) :
    Finset (GateCfg ι r) :=
  open scoped Classical in
  Finset.univ.filter fun ω => ∀ p ∈ arcSet Arc F.nonOwners, ω p = ω (F.owner, p.2)
noncomputable def radiusTwoEvent (Arc : ι → ι → Bool) (S : Finset ι) : Finset (GateCfg ι r) :=
  open scoped Classical in
  Finset.univ.filter fun ω => ∃ h ∈ S, IntObstruction Arc 2 S h (toGamma ω)
def radiusTwoOwnerConst : ℕ :=
  2 ^ 20 * ∑ l ∈ Finset.range 9, Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l
def radiusTwoConst : ℕ := 1300311466573824
section MissArcs
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
def missArcs (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) (Z : ι → Finset (Fin r))
    (T : Finset ι) : Finset (ι × ι) :=
  (arcSet Arc T).filter fun p => γ p.1 p.2 ∉ Z p.2
def discSet (γ : ι → ι → Fin r) (Z : ι → Finset (Fin r)) (T : Finset ι) (h : ι) : Finset ι :=
  T.filter fun j => ¬ (Z j ⊆ {γ h j})
end MissArcs
noncomputable def branch2 (Arc : ι → ι → Bool) (S : Finset ι) (h : ι) (L : Finset ι)
    (w : (j : ι) → j ∈ L → Fin r) (X : Finset (ι × ι)) : Finset (GateCfg ι r) :=
  open scoped Classical in
  Finset.univ.filter fun ω =>
    ∀ p ∈ arcSet Arc (S.erase h), p ∉ X →
      ω p = ω (h, p.2) ∨ ω p = (if hp : p.2 ∈ L then w p.2 hp else ω (h, p.2))
end LLL
end BSLambda


