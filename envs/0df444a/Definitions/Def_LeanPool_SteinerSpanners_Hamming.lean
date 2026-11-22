-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_Hamming
-- name    : LeanPool_SteinerSpanners_Hamming
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:41.410998+00:00
-- url     : https://prove2.me/theorems/5de87837-58f4-4e3f-93b0-54bbe9ba9234
-- title:
--   Hamming
-- statement:
--   Definitions and structural lemmas for Hamming, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Hamming.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Hamming
lemma card_nonzero_zmod2_vec (r : ℕ) :
    (Finset.univ.erase (0 : Fin r → ZMod 2)).card = 2 ^ r - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, ZMod.card 2, Fintype.card_fin]
noncomputable def hammingColEquiv (r : ℕ) :
    Fin (2 ^ r - 1) ≃ ↥(Finset.univ.erase (0 : Fin r → ZMod 2)) :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, card_nonzero_zmod2_vec])).symm
noncomputable def hammingSyndrome (r : ℕ) (u : Fin (2 ^ r - 1) → Bool) :
    Fin r → ZMod 2 :=
  ∑ j : Fin (2 ^ r - 1), if u j then (hammingColEquiv r j).val else 0
def flipBit {n : ℕ} (u : Fin n → Bool) (j : Fin n) : Fin n → Bool :=
  Function.update u j (!u j)
noncomputable def hammingBlkCode (r : ℕ) : Finset (Fin (2 ^ r - 1) → Bool) :=
  Finset.univ.filter (fun u => hammingSyndrome r u = 0)
noncomputable def hammingBlkDecode (r : ℕ) (u : Fin (2 ^ r - 1) → Bool) :
    Fin (2 ^ r - 1) → Bool :=
  if h : hammingSyndrome r u = 0 then u
  else flipBit u ((hammingColEquiv r).symm ⟨hammingSyndrome r u,
    Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩)
def coordEquiv (r d : ℕ) :
    (Fin (d / (2 ^ r - 1)) × Fin (2 ^ r - 1)) ⊕ Fin (d % (2 ^ r - 1)) ≃ Fin d :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans
      (Fin.castOrderIso (by rw [Nat.mul_comm]; exact Nat.div_add_mod d (2 ^ r - 1))).toEquiv)
def getBlock (r d : ℕ) (x : Fin d → Bool)
    (m : Fin (d / (2 ^ r - 1))) : Fin (2 ^ r - 1) → Bool :=
  fun j => x (coordEquiv r d (.inl (m, j)))
def getRem (r d : ℕ) (x : Fin d → Bool) : Fin (d % (2 ^ r - 1)) → Bool :=
  fun k => x (coordEquiv r d (.inr k))
def mkFromBlocks (r d : ℕ)
    (B : Fin (d / (2 ^ r - 1)) → Fin (2 ^ r - 1) → Bool)
    (R : Fin (d % (2 ^ r - 1)) → Bool) : Fin d → Bool :=
  fun i =>
    match (coordEquiv r d).symm i with
    | .inl (m, j) => B m j
    | .inr k => R k
noncomputable def blockDecode (r d : ℕ) (x : Fin d → Bool) : Fin d → Bool :=
  mkFromBlocks r d (fun m => hammingBlkDecode r (getBlock r d x m)) (getRem r d x)
noncomputable def blockCode (r d : ℕ) : Finset (Fin d → Bool) :=
  Finset.univ.filter (fun c => ∀ m : Fin (d / (2 ^ r - 1)), getBlock r d c m ∈ hammingBlkCode r)
def zeroCube (d : ℕ) : Fin d → Bool := fun _ => false
noncomputable def bReal (r : ℕ) : ℝ := (2 : ℝ) ^ r - 1
noncomputable def rhoReal (r : ℕ) : ℝ := 1 / (64 * bReal r)
open Classical in
def layerUnionGraph {α ι : Type} [DecidableEq α] (P S : Finset α) (z₀ : α)
    (S_fn : ι → Finset α) (H_fn : ∀ r : ι, SimpleGraph ↥(P ∪ S_fn r)) :
    SimpleGraph ↥(P ∪ S) :=
  { Adj := fun u v =>
      (u ≠ v ∧ ((u.val ∈ P ∧ v.val = z₀) ∨ (v.val ∈ P ∧ u.val = z₀))) ∨
      (∃ (r : ι) (u' v' : ↥(P ∪ S_fn r)),
        u'.val = u.val ∧ v'.val = v.val ∧ (H_fn r).Adj u' v')
    symm := ⟨fun u v h => by
      rcases h with ⟨hne, hstar⟩ | ⟨r, u', v', hu', hv', hadj⟩
      · exact Or.inl ⟨hne.symm, hstar.symm⟩
      · exact Or.inr ⟨r, v', u', hv', hu', (H_fn r).adj_symm hadj⟩⟩
    loopless := ⟨fun u h => by
      rcases h with ⟨hne, _⟩ | ⟨r, u', v', hu', hv', hadj⟩
      · exact hne rfl
      · have heq : u' = v' := Subtype.ext (hu'.trans hv'.symm)
        rw [heq] at hadj
        exact (H_fn r).irrefl hadj⟩ }
end HighDimSteinerSpanners.Proofs.Hamming


