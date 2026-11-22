-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowDot20261120
-- name    : LinearSetReconciliation327_Main_HintRowDot20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:33:07.329637+00:00
-- url     : https://prove2.me/theorems/e30af9e2-1f8b-4545-a872-0af216b378a5
-- title:
--   LinearSetReconciliation327 — HintRowDot (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowDot20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRFrame20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintBit_mul (a b : ZMod 2) : a.val * b.val = (a * b).val := by
  have hh : ∀ a b : ZMod 2, a.val * b.val = (a * b).val := by decide
  exact hh a b

theorem hintBit_xor (a b : ZMod 2) : a.val ^^^ b.val = (a + b).val := by
  have hh : ∀ a b : ZMod 2, a.val ^^^ b.val = (a + b).val := by decide
  exact hh a b

def hintDotBody : List Instr :=
  [.mul 3 0 7, .add 3 5 3, .load 9 3, .add 3 4 0,
    .load 10 3, .mul 11 9 10, .bxor 1 1 11, .add 0 0 15]

def hintDotSum (f g : ℕ → ZMod 2) (k : ℕ) : ZMod 2 := ∑ i ∈ Finset.range k, f i * g i

structure HintDotParams (vec mat count stride : ℕ) (p : RAMState) : Prop where
  vec_value : p.regs 4 = vec
  mat_value : p.regs 5 = mat
  count_value : p.regs 6 = count
  stride_value : p.regs 7 = stride
  one_value : p.regs 15 = 1

structure HintDotInv (vec mat count stride : ℕ) (f g : ℕ → ZMod 2) (k : ℕ)
    (original : ℕ → ℕ) (p : RAMState) : Prop where
  params : HintDotParams vec mat count stride p
  counter : p.regs 0 = k
  sum_value : p.regs 1 = (hintDotSum f g k).val
  memory : p.mem = original

def hintDotBodyResult (p : RAMState) (vec k : ℕ) (f g : ℕ → ZMod 2) : RAMState :=
  {p with pc := p.pc + 8, regs :=
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update p.regs
      3 (vec + k)) 9 (f k).val) 10 (g k).val) 11 (f k * g k).val)
      1 (hintDotSum f g (k + 1)).val) 0 (k + 1)}

theorem hintDotBody_spec (E : RAMEnv) (p : RAMState) (vec mat count stride k : ℕ)
    (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hInv : HintDotInv vec mat count stride f g k original p)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hVec : vec + k < 2 ^ E.W) (hMat : mat + k * stride < 2 ^ E.W)
    (hF : original (mat + k * stride) = (f k).val) (hG : original (vec + k) = (g k).val) :
    runBlock hintDotBody E p = hintDotBodyResult p vec k f g := by
  have hMul : k * stride < 2 ^ E.W := by omega
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hFBound : (f k).val < 2 ^ E.W := (ZMod.val_lt (f k)).trans_le hWord
  have hGBound : (g k).val < 2 ^ E.W := (ZMod.val_lt (g k)).trans_le hWord
  have hProdBound : (f k * g k).val < 2 ^ E.W := (ZMod.val_lt (f k * g k)).trans_le hWord
  have hSumBound : (hintDotSum f g (k + 1)).val < 2 ^ E.W :=
    (ZMod.val_lt (hintDotSum f g (k + 1))).trans_le hWord
  have hSum : hintDotSum f g (k + 1) = hintDotSum f g k + f k * g k := by
    exact Finset.sum_range_succ _ _
  apply crState_ext
  · simp [hintDotBody, hintDotBodyResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    fin_cases r <;>
      simp [hintDotBody, hintDotBodyResult, runBlock, execInstr, hInv.params.vec_value,
        hInv.params.mat_value, hInv.params.stride_value, hInv.params.one_value, hInv.counter,
        hInv.sum_value, hInv.memory, Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hMat, Nat.mod_eq_of_lt hVec,
        hF, hG, Nat.mod_eq_of_lt hFBound, Nat.mod_eq_of_lt hGBound, hintBit_mul,
        Nat.mod_eq_of_lt hProdBound, hintBit_xor, ← hSum, Nat.mod_eq_of_lt hSumBound,
        Nat.mod_eq_of_lt hNext]
  · rfl

theorem hintDotBody_invariant (E : RAMEnv) (p : RAMState) (vec mat count stride k : ℕ)
    (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hInv : HintDotInv vec mat count stride f g k original p)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hVec : vec + k < 2 ^ E.W) (hMat : mat + k * stride < 2 ^ E.W)
    (hF : original (mat + k * stride) = (f k).val) (hG : original (vec + k) = (g k).val) :
    HintDotInv vec mat count stride f g (k + 1) original (runBlock hintDotBody E p) := by
  rw [hintDotBody_spec E p vec mat count stride k f g original hInv hWord hCount hk hVec hMat hF hG]
  refine ⟨?_, ?_, ?_, hInv.memory⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hintDotBodyResult] using hInv.params.vec_value
    · simpa [hintDotBodyResult] using hInv.params.mat_value
    · simpa [hintDotBodyResult] using hInv.params.count_value
    · simpa [hintDotBodyResult] using hInv.params.stride_value
    · simpa [hintDotBodyResult] using hInv.params.one_value
  · simp [hintDotBodyResult]
  · simp [hintDotBodyResult]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDotBody_invariant


