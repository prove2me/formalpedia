-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
-- name    : QuantumLTF_Membership_Supplement_lcgSym54ArithV2
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T02:59:11.095828+00:00
-- url     : https://prove2.me/theorems/c28b7f8f-ac30-4012-b187-6da61217b060
-- title:
--   Reversible $\mathrm{gates12}$ arithmetic primitives and sub-register embedding combinators ($\mathrm{LcgSym54ArithV2}$)
-- statement:
--   Defines pure classical specifications of MSB-first unsigned register operations, disjoint sub-register embedding combinators (`combineEmb`, `act_mapWires_ket_expand`, `act_mapWires_ket_sum`), and the bundled `gates12` (`LayeredCircuit`) suite `LcgSym54ArithV2` for `[LCG26]` Stage B circuits.
--
--   1. **Sub-Register Lifting:** `combineEmb` packs disjoint main and clean-ancilla embeddings into `Fin (main + anc) -> Fin m`, while `act_mapWires_ket_expand` and `act_mapWires_ket_sum` lift both basis permutations and uniform superpositions across arbitrary wire embeddings without manual basis-vector unpacking.
--
--   2. **Reversible `gates12` Arithmetic Primitives:** Packages exact `ImplementsOnClean (permMat ...)` specifications and linear gate counts for `copyRegCircuit` ($w$), `swapRegCircuit` ($3w$), `cswapRegCircuit` ($7w$), `ctrlCopyRegCircuit` ($5w$), `eqRegCircuit` ($\le 14w + 12$), constant/register MSB-first toggles and comparators `setConstMSBCircuit`, `ctrlConstXorMSBCircuit`, `eqConstMSBCircuit`, `ltConstMSBCircuit`, `ltRegMSBCircuit` ($16w + 1$), and Cuccaro ripple-carry adders/subtractors `addInPlaceMSBCircuit`, `subInPlaceMSBCircuit` ($14w$), `ctrlAddInPlaceMSBCircuit`, `ctrlSubInPlaceMSBCircuit` ($24w$), `ctrlAddConstInPlaceMSBCircuit`, and `ctrlSubConstInPlaceMSBCircuit` ($\le 16w$).
--
--   **Formalization Note** All MSB-first circuits are derived at zero extra gate overhead from LSB-first Cuccaro ripple-carry primitives by wire reversal (`Fin.revPerm`) and proved inhabited by `lcg_sym_arith_54`.
-- source:
--   Cuccaro, Draper, Kutin, Moulton (2004), A new quantum ripple-carry addition circuit (quant-ph/0410184); Liu, Childs, Gottesman [LCG26] (arXiv:2411.04019, Section IV); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54

set_option autoImplicit false

/-!
# Arithmetic & Reversible Circuit Primitives Interface for `[LCG26]` Stage B

Defines pure classical specifications (bitwise and MSB-first unsigned register arithmetic),
sub-register embedding combinators (`combineEmb`, `act_mapWires_ket_expand`,
`act_mapWires_ket_sum`), and the bundled `gates12` (`LayeredCircuit`) suite `LcgSym54Arith`
for `alonso_schott_sil_54`, `harm_bucket_hl_54`, and `nsil_symmetrize_54`.
-/

namespace QuantumLTF.Membership.Supplement.LcgSym54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement Thm49Primitives Thm410Router

/-! ### Part 1: Structural Combinators & General `mapWires` Superposition Lifting -/

def combineEmb {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) : Fin (a + b) ↪ Fin m where
  toFun := Fin.addCases ea eb
  inj' x y h := by
    induction x using Fin.addCases with
    | left ix =>
      induction y using Fin.addCases with
      | left iy => simp only [Fin.addCases_left] at h; rw [ea.injective h]
      | right jy => simp only [Fin.addCases_left, Fin.addCases_right] at h; exact absurd h (hdisj ix jy)
    | right jx =>
      induction y using Fin.addCases with
      | left iy => simp only [Fin.addCases_right, Fin.addCases_left] at h; exact absurd h.symm (hdisj iy jx)
      | right jy => simp only [Fin.addCases_right] at h; rw [eb.injective h]

@[simp] lemma combineEmb_castAdd {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) (i : Fin a) :
    combineEmb ea eb hdisj (Fin.castAdd b i) = ea i := by
  change Fin.addCases ea eb (Fin.castAdd b i) = ea i; simp

@[simp] lemma combineEmb_natAdd {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) (j : Fin b) :
    combineEmb ea eb hdisj (Fin.natAdd a j) = eb j := by
  change Fin.addCases ea eb (Fin.natAdd a j) = eb j; simp

lemma castAddEmb_trans_combineEmb {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) :
    (Fin.castAddEmb b).trans (combineEmb ea eb hdisj) = ea := by
  ext i; simp

@[simp] lemma padZero_val_lt {main anc : ℕ} (x : Qubits main) (u : Fin (main + anc)) (h : u.1 < main) :
    padZero main anc x u = x ⟨u.1, h⟩ := by
  have heq : u = Fin.castAdd anc ⟨u.1, h⟩ := Fin.ext rfl
  conv_lhs => rw [heq]
  exact padZero_castAdd main anc x ⟨u.1, h⟩

@[simp] lemma padZero_val_ge {main anc : ℕ} (x : Qubits main) (u : Fin (main + anc)) (h : main ≤ u.1) :
    padZero main anc x u = false := by
  have heq : u = Fin.natAdd main ⟨u.1 - main, by have := u.isLt; omega⟩ := by
    apply Fin.ext; simp; omega
  conv_lhs => rw [heq]
  exact padZero_natAdd main anc x ⟨u.1 - main, by have := u.isLt; omega⟩

@[simp] lemma padZero_zero {main : ℕ} (x : Qubits main) (u : Fin (main + 0)) :
    padZero main 0 x u = x ⟨u.1, by have := u.isLt; omega⟩ :=
  padZero_val_lt x u (by have := u.isLt; omega)

lemma updateOn_comp_self {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z : Qubits m) (x : Qubits m₀) :
    updateOn emb z x ∘ emb = x := by
  funext i; exact updateOn_apply_emb emb z x i

lemma updateOn_eq_of_off {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (y z : Qubits m)
    (hoff : ∀ a : Fin m, a ∉ Set.range emb → y a = z a) :
    updateOn emb z (y ∘ emb) = y := by
  funext a
  by_cases ha : a ∈ Set.range emb
  · rcases ha with ⟨i, rfl⟩
    exact updateOn_apply_emb emb z (y ∘ emb) i
  · rw [updateOn_apply_not_mem emb z (y ∘ emb) ha]
    exact (hoff a ha).symm

lemma act_mapWires_ket_expand {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) :
    act (lc.mapWires emb).unitary (ket z) =
      ∑ x : Qubits m₀, (act lc.unitary (ket (z ∘ emb))) x • ket (updateOn emb z x) := by
  classical
  rw [LayeredCircuit.mapWires_unitary, act_ket_eq]
  let S : Finset (Qubits m) := Finset.univ.filter fun y => ∀ a : Fin m, a ∉ Set.range emb → y a = z a
  have hsub : ∑ y : Qubits m, embedOp lc.unitary emb y z • ket y =
      ∑ y ∈ S, embedOp lc.unitary emb y z • ket y := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro y _ hy
    have hnot : ¬ ∀ a : Fin m, a ∉ Set.range emb → y a = z a := by
      intro h; apply hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    dsimp only [embedOp, Matrix.of_apply]
    rw [if_neg hnot, zero_smul]
  rw [hsub]
  refine Finset.sum_bij (fun y _ => y ∘ emb) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro y₁ hy₁ y₂ hy₂ heq
    have h1 := (Finset.mem_filter.mp hy₁).2
    have h2 := (Finset.mem_filter.mp hy₂).2
    rw [← updateOn_eq_of_off emb y₁ z h1, ← updateOn_eq_of_off emb y₂ z h2, heq]
  · intro x _
    refine ⟨updateOn emb z x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, updateOn_comp_self emb z x⟩
    intro a ha; exact updateOn_apply_not_mem emb z x ha
  · intro y hy
    have hoff := (Finset.mem_filter.mp hy).2
    rw [updateOn_eq_of_off emb y z hoff]
    congr 1
    simp only [embedOp, Matrix.of_apply, if_pos hoff]
    change _ = (WithLp.ofLp (act lc.unitary (ket (z ∘ emb)))) (y ∘ emb)
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma act_mapWires_ket_sum {m₀ m : ℕ} {ι : Type*} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) (s : Finset ι) (c : ι → ℂ) (f : ι → Qubits m₀)
    (h : act lc.unitary (ket (z ∘ emb)) = ∑ i ∈ s, c i • ket (f i)) :
    act (lc.mapWires emb).unitary (ket z) = ∑ i ∈ s, c i • ket (updateOn emb z (f i)) := by
  rw [act_mapWires_ket_expand, h]
  have hcoord : ∀ x : Qubits m₀,
      (∑ i ∈ s, c i • ket (f i)) x = ∑ i ∈ s, if x = f i then c i else 0 := by
    intro x
    change (WithLp.ofLp (∑ i ∈ s, c i • ket (f i))) x = _
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, ket, PiLp.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp_rw [hcoord, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro x _ hx
    simp [hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-! ### Part 2: Pure Bitwise & MSB-First Register Specification Functions -/

def copyRegFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  fun u => if _h : w ≤ u.1 then xor (x u) (x ⟨u.1 - w, by omega⟩) else x u

def swapRegFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  fun u => if _h : u.1 < w then x ⟨w + u.1, by omega⟩ else x ⟨u.1 - w, by omega⟩

def cswapRegFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  fun u =>
    if x ⟨0, by omega⟩ then
      if _h1 : 1 ≤ u.1 ∧ u.1 < 1 + w then x ⟨u.1 + w, by omega⟩
      else if _h2 : 1 + w ≤ u.1 then x ⟨u.1 - w, by omega⟩
      else x u
    else x u

def ctrlCopyRegFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  fun u =>
    if x ⟨0, by omega⟩ then
      if _h : 1 + w ≤ u.1 then xor (x u) (x ⟨u.1 - w, by omega⟩) else x u
    else x u

def eqRegFn (w : ℕ) (x : Qubits (w + w + 1)) : Qubits (w + w + 1) :=
  Function.update x ⟨w + w, by omega⟩
    (xor (x ⟨w + w, by omega⟩)
      (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = x ⟨w + i.1, by omega⟩)))

def setConstMSBFn (w c : ℕ) (x : Qubits w) : Qubits w :=
  fun i => xor (x i) (natToBits w c i)

def ctrlConstXorMSBFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  fun u => if x ⟨0, by omega⟩ then
    if _h : 1 ≤ u.1 then xor (x u) (natToBits w c ⟨u.1 - 1, by have := u.isLt; omega⟩) else x u
  else x u

def eqConstMSBFn (w c : ℕ) (x : Qubits (w + 1)) : Qubits (w + 1) :=
  Function.update x ⟨w, by omega⟩
    (xor (x ⟨w, by omega⟩)
      (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = natToBits w c i)))

def ltConstMSBFn (w H : ℕ) (x : Qubits (w + 1)) : Qubits (w + 1) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  Function.update x ⟨w, Nat.lt_succ_self w⟩
    (xor (x ⟨w, Nat.lt_succ_self w⟩) (decide (bitsToNat a < H)))

def ltRegMSBFn (w : ℕ) (x : Qubits (w + w + 1)) : Qubits (w + w + 1) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  Function.update x ⟨w + w, by omega⟩
    (xor (x ⟨w + w, by omega⟩) (decide (bitsToNat a < bitsToNat b)))

def addInPlaceMSBFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let s := natToBits w (bitsToNat a + bitsToNat b)
  fun u => if _h : u.1 < w then x u else s ⟨u.1 - w, by have := u.isLt; omega⟩

def subInPlaceMSBFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let d := natToBits w (2 ^ w + bitsToNat b - bitsToNat a)
  fun u => if _h : u.1 < w then x u else d ⟨u.1 - w, by have := u.isLt; omega⟩

def ctrlAddInPlaceMSBFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let s := natToBits w (bitsToNat a + bitsToNat b)
  fun u =>
    if x ⟨0, by omega⟩ then
      if _h : 1 + w ≤ u.1 then s ⟨u.1 - (1 + w), by omega⟩ else x u
    else x u

def ctrlSubInPlaceMSBFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let d := natToBits w (2 ^ w + bitsToNat b - bitsToNat a)
  fun u =>
    if x ⟨0, by omega⟩ then
      if _h : 1 + w ≤ u.1 then d ⟨u.1 - (1 + w), by omega⟩ else x u
    else x u

def ctrlAddConstInPlaceMSBFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let s := natToBits w (c % 2 ^ w + bitsToNat b)
  fun u => if x ⟨0, by omega⟩ then if _h : 1 ≤ u.1 then s ⟨u.1 - 1, by omega⟩ else x u else x u

def ctrlSubConstInPlaceMSBFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let d := natToBits w (2 ^ w + bitsToNat b - c % 2 ^ w)
  fun u => if x ⟨0, by omega⟩ then if _h : 1 ≤ u.1 then d ⟨u.1 - 1, by omega⟩ else x u else x u

end QuantumLTF.Membership.Supplement.LcgSym54

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

/-- Bundled `gates12` (`LayeredCircuit`) reversible arithmetic suite for `[LCG26]` Stage B. -/
structure LcgSym54ArithV2 where
  permMat_id : ∀ {ι : Type} [DecidableEq ι], permMat (id : ι → ι) = 1
  permMat_mul : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ι),
    permMat f * permMat g = permMat (f ∘ g)
  seqClean_perm : ∀ {main anc₁ anc₂ : ℕ}
      (lc₁ : LayeredCircuit (main + anc₁)) (lc₂ : LayeredCircuit (main + anc₂))
      {f g : Qubits main → Qubits main},
    lc₁.ImplementsOnClean (permMat f) → lc₂.ImplementsOnClean (permMat g) →
    (seqClean lc₁ lc₂).ImplementsOnClean (permMat (g ∘ f))
  adj_implementsOnClean_perm : ∀ {main anc : ℕ} (lc : LayeredCircuit (main + anc))
      {f g : Qubits main → Qubits main},
    (∀ x, g (f x) = x) → (∀ x, f (g x) = x) →
    lc.ImplementsOnClean (permMat f) →
    lc.adj.ImplementsOnClean (permMat g)
  implementsOnClean_id_perm : ∀ {main anc : ℕ},
    (LayeredCircuit.id (main + anc)).ImplementsOnClean (permMat id)
  act_mapWires_perm : ∀ {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
      (f : Qubits main → Qubits main),
    lc.ImplementsOnClean (permMat f) →
    ∀ (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m),
      (∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false) →
      let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
      act (lc.mapWires emb).unitary (ket z) = ket (updateOn embMain z (f (z ∘ embMain)))
  act_subReg_perm : ∀ {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
      (f : Qubits main → Qubits main),
    lc.ImplementsOnClean (permMat f) →
    ∀ (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
      (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m),
      (∀ j : Fin anc, z (embAnc j) = false) →
      act (lc.mapWires (combineEmb embMain embAnc hdisj)).unitary (ket z) =
        ket (updateOn embMain z (f (z ∘ embMain)))
  copyRegCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 0)
  copyRegCircuit_size : ∀ w, (copyRegCircuit w).size = w
  copyRegCircuit_implements : ∀ w, (copyRegCircuit w).ImplementsOnClean (permMat (copyRegFn w))
  swapRegCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 0)
  swapRegCircuit_size : ∀ w, (swapRegCircuit w).size = 3 * w
  swapRegCircuit_implements : ∀ w, (swapRegCircuit w).ImplementsOnClean (permMat (swapRegFn w))
  cswapRegCircuit : (w : ℕ) → LayeredCircuit ((1 + w + w) + 0)
  cswapRegCircuit_size : ∀ w, (cswapRegCircuit w).size = 7 * w
  cswapRegCircuit_implements : ∀ w, (cswapRegCircuit w).ImplementsOnClean (permMat (cswapRegFn w))
  ctrlCopyRegCircuit : (w : ℕ) → LayeredCircuit ((1 + w + w) + 0)
  ctrlCopyRegCircuit_size : ∀ w, (ctrlCopyRegCircuit w).size = 5 * w
  ctrlCopyRegCircuit_implements : ∀ w, (ctrlCopyRegCircuit w).ImplementsOnClean (permMat (ctrlCopyRegFn w))
  eqRegCircuit : (w : ℕ) → LayeredCircuit ((w + w + 1) + w)
  eqRegCircuit_size : ∀ w, (eqRegCircuit w).size ≤ 14 * w + 12
  eqRegCircuit_implements : ∀ w, (eqRegCircuit w).ImplementsOnClean (permMat (eqRegFn w))
  setConstMSBCircuit : (w c : ℕ) → LayeredCircuit (w + 0)
  setConstMSBCircuit_size : ∀ w c, (setConstMSBCircuit w c).size ≤ w
  setConstMSBCircuit_implements : ∀ w c,
    (setConstMSBCircuit w c).ImplementsOnClean (permMat (setConstMSBFn w c))
  ctrlConstXorMSBCircuit : (w c : ℕ) → LayeredCircuit ((1 + w) + 0)
  ctrlConstXorMSBCircuit_size : ∀ w c, (ctrlConstXorMSBCircuit w c).size ≤ w
  ctrlConstXorMSBCircuit_implements : ∀ w c,
    (ctrlConstXorMSBCircuit w c).ImplementsOnClean (permMat (ctrlConstXorMSBFn w c))
  eqConstMSBCircuit : (w c : ℕ) → LayeredCircuit ((w + 1) + w)
  eqConstMSBCircuit_size : ∀ w c, (eqConstMSBCircuit w c).size ≤ 14 * w + 12
  eqConstMSBCircuit_implements : ∀ w c,
    (eqConstMSBCircuit w c).ImplementsOnClean (permMat (eqConstMSBFn w c))
  ltConstMSBCircuit : (w H : ℕ) → LayeredCircuit ((w + 1) + w)
  ltConstMSBCircuit_size : ∀ w H, (ltConstMSBCircuit w H).size ≤ 20 * w + 1
  ltConstMSBCircuit_implements : ∀ w H,
    (ltConstMSBCircuit w H).ImplementsOnClean (permMat (ltConstMSBFn w H))
  ltRegMSBCircuit : (w : ℕ) → LayeredCircuit ((w + w + 1) + 1)
  ltRegMSBCircuit_size : ∀ w, (ltRegMSBCircuit w).size = 16 * w + 1
  ltRegMSBCircuit_implements : ∀ w, (ltRegMSBCircuit w).ImplementsOnClean (permMat (ltRegMSBFn w))
  addInPlaceMSBCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 1)
  addInPlaceMSBCircuit_size : ∀ w, (addInPlaceMSBCircuit w).size = 14 * w
  addInPlaceMSBCircuit_implements : ∀ w,
    (addInPlaceMSBCircuit w).ImplementsOnClean (permMat (addInPlaceMSBFn w))
  subInPlaceMSBCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 1)
  subInPlaceMSBCircuit_size : ∀ w, (subInPlaceMSBCircuit w).size = 14 * w
  subInPlaceMSBCircuit_implements : ∀ w,
    (subInPlaceMSBCircuit w).ImplementsOnClean (permMat (subInPlaceMSBFn w))
  ctrlAddInPlaceMSBCircuit : (w : ℕ) → LayeredCircuit ((1 + w + w) + (w + 1))
  ctrlAddInPlaceMSBCircuit_size : ∀ w, (ctrlAddInPlaceMSBCircuit w).size = 24 * w
  ctrlAddInPlaceMSBCircuit_implements : ∀ w,
    (ctrlAddInPlaceMSBCircuit w).ImplementsOnClean (permMat (ctrlAddInPlaceMSBFn w))
  ctrlSubInPlaceMSBCircuit : (w : ℕ) → LayeredCircuit ((1 + w + w) + (w + 1))
  ctrlSubInPlaceMSBCircuit_size : ∀ w, (ctrlSubInPlaceMSBCircuit w).size = 24 * w
  ctrlSubInPlaceMSBCircuit_implements : ∀ w,
    (ctrlSubInPlaceMSBCircuit w).ImplementsOnClean (permMat (ctrlSubInPlaceMSBFn w))
  ctrlAddConstInPlaceMSBCircuit : (w c : ℕ) → LayeredCircuit ((1 + w) + (w + 1))
  ctrlAddConstInPlaceMSBCircuit_size : ∀ w c, (ctrlAddConstInPlaceMSBCircuit w c).size ≤ 16 * w
  ctrlAddConstInPlaceMSBCircuit_implements : ∀ w c,
    (ctrlAddConstInPlaceMSBCircuit w c).ImplementsOnClean (permMat (ctrlAddConstInPlaceMSBFn w c))
  ctrlSubConstInPlaceMSBCircuit : (w c : ℕ) → LayeredCircuit ((1 + w) + (w + 1))
  ctrlSubConstInPlaceMSBCircuit_size : ∀ w c, (ctrlSubConstInPlaceMSBCircuit w c).size ≤ 16 * w
  ctrlSubConstInPlaceMSBCircuit_implements : ∀ w c,
    (ctrlSubConstInPlaceMSBCircuit w c).ImplementsOnClean (permMat (ctrlSubConstInPlaceMSBFn w c))

end QuantumLTF.Membership.Supplement


