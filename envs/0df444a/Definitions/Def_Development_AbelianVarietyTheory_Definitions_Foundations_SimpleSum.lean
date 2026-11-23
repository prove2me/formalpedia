-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:08.396211+00:00
-- url     : https://prove2.me/theorems/49ec35c3-581e-40c5-9828-d47d620da5f5
-- title:
--   Simple Sum
-- statement:
--   Definitions and structural lemmas for Simple Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.RootEx
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
def lev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => p) (fun i => i.val + 1)
def InN (p : ℕ) (g : GL (n ⊕ Fin c) k) : Prop :=
  ∀ r s, lev p s ≤ lev p r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
def N (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  Subgroup.closure {g | InN p g}
def embX (c : ℕ) : GL n k →* GL (n ⊕ Fin c) k :=
  Units.map
    { toFun := fun g : Matrix n n k => (fromBlocks g 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
      map_one' := fromBlocks_one
      map_mul' := fun g h => by simp [fromBlocks_multiply] }
def embA (n : Type*) [Fintype n] [DecidableEq n] : GL (Fin c) k →* GL (n ⊕ Fin c) k :=
  Units.map
    { toFun := fun g : Matrix (Fin c) (Fin c) k => (fromBlocks 1 0 0 g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
      map_one' := fromBlocks_one
      map_mul' := fun g h => by simp [fromBlocks_multiply] }
def R (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  (embX c).range ⊔ N k n c p
def lowU (C : Matrix (Fin c) n k) : GL (n ⊕ Fin c) k :=
  ⟨fromBlocks 1 0 C 1, fromBlocks 1 0 (-C) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
def upU (B : Matrix n (Fin c) k) : GL (n ⊕ Fin c) k :=
  ⟨fromBlocks 1 B 0 1, fromBlocks 1 (-B) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
def rowE (c p : ℕ) (u : n → k) : GL (n ⊕ Fin c) k :=
  lowU (Matrix.of fun l s => if l.val + 1 = p then u s else 0)
def colE (c p : ℕ) (β : n → k) : GL (n ⊕ Fin c) k :=
  upU (Matrix.of fun r i => if i.val + 1 = p then β r else 0)
def simpleSum (g : GL (n ⊕ Fin c) k) : k :=
  ∑ i : Fin c, ∑ j : Fin c, if j.val = i.val + 1 then g.val (Sum.inr i) (Sum.inr j) else 0
variable {n' : Type*} [Fintype n'] [DecidableEq n']
def Free (p : ℕ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (Sum.inl _, Sum.inl _) => False
  | (Sum.inr l, Sum.inl _) => l.val + 1 < p
  | (Sum.inl _, Sum.inr i) => p < i.val + 1
  | (Sum.inr l, Sum.inr i) => l.val < i.val
def basePt (c : ℕ) (x₀ : Matrix n n' k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks x₀ 0 0 (Matrix.of fun l i => if l.val = i.val then 1 else 0)
open Classical in

def affPt (p : ℕ) (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  basePt c x₀ + Matrix.of fun r s => if h : Free p (r, s) then e ⟨(r, s), h⟩ else 0
def ch (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : k := ∑ i : Fin c, x (Sum.inr i) (Sum.inr i.succ)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {P A : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
def IsNEquiv (ψ : AddChar k Circle) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) : Prop :=
  ∀ g ∈ N k n c p, ∀ v, l (σ g v) = (ψ (simpleSum g) : ℂ) * l v
def IsPos (ψ : AddChar k Circle) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ p σ (b φ)) ∧ ∀ (g : GL n k) φ v, b (π g φ) (σ (embX c g) v) =
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b φ v
variable [MeasurableSpace k] [BorelSpace k]
def exUp (ν : Measure k) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) (v : A) : ℂ :=
  ∫ u : n → k, l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)
def exDown (ν : Measure k) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) (v : A) : ℂ :=
  ∫ β : n → k, l (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν)
open Classical in

def opE (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x₀ : Matrix n n' k) : ℂ :=
  ∫ e, Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) ∂(Measure.pi fun _ => ν)
open Classical in

def volN (ν : Measure k) (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Measure (N k n c p) :=
  (Measure.pi fun _ : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} => ν).comap
    fun g rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2
def IsQuotInt (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (p : ℕ)
    (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ) : Prop :=
  ∃ F ∈ SB (GL (n ⊕ Fin c) k),
    (∀ h, f h = ∫ g, (∫ u : N k n c p, F (embX c g * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c p)) ∂μX) ∧ z = ∫ h, F h ∂μG
end GlobalTheory.RootEx


