-- Prove2me | Definitions.Def_ErasureQTanner_inputWords
-- name    : ErasureQTanner_inputWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:41.915213+00:00
-- url     : https://prove2.me/theorems/ff4a269a-ba76-4291-b0e4-4f9bb034a999
-- title:
--   The decoder on the word RAM: input layout, output cells, a run
-- statement:
--   The paper's decoder receives "the erasure vector $\varepsilon$ together with the syndromes $H_Xe_Z^{\mathsf T}$, $H_Ze_X^{\mathsf T}$" and returns estimates $e'_Z,e'_X$. This item fixes the input words, in order: $m=|G|$; the indices of $A(a)g$ for $a<\Delta$, $g<m$; the indices of $gB(b)$ for $b<\Delta$, $g<m$; the $N$ bits of the pattern by $(g,a,b)$; the bits of $H_Xe_Z^{\mathsf T}$; the bits of $H_Ze_X^{\mathsf T}$. The output is $e'_X$ then $e'_Z$, one bit per word, in the cells right after the input. A run of a program $P$ is a halting execution on the published word RAM.
--
--   **Formalization Note** The paper names no machine. The cost model it needs (constant-time look-ups and pointer updates, pp.28–29) is the word RAM with $O(\log|G|)$-bit words. The complex is input, since one program serves all family members; computing it is not part of "decoding time". $\Delta$ and the local codes live in the program. The errors $e_X,e_Z$ never appear in the input.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §2, p.4; proof of Theorem 16, pp.27–29

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_ErasureQTanner_HX

set_option autoImplicit false

namespace ErasureQTanner

variable {Δ : ℕ}

/-- The elements of `G` in the order of `enum`. -/
def allG (Γ : LRData Δ) : List Γ.G := List.ofFn fun i => Γ.enum.symm i

/-- The squares in lexicographic order of (`enum g`, `a`, `b`). -/
def allSquares (Γ : LRData Δ) : List Γ.Square :=
  (allG Γ).flatMap fun g => (List.finRange Δ).flatMap fun a => (List.finRange Δ).map fun b => (g, a, b)

/-- The position of a square in `allSquares`. -/
def squareIdx (Γ : LRData Δ) (s : Γ.Square) : ℕ :=
  (Γ.enum s.1 : ℕ) * Δ ^ 2 + (s.2.1 : ℕ) * Δ + (s.2.2 : ℕ)

/-- A bit as a machine word. -/
def bitWord (z : ZMod 2) : ℤ := (z.val : ℤ)

/-- The rows of `H_X`: the rows of `V00` by (`enum g`, basis index), then those of `V11`. -/
def xRows (Γ : LRData Δ) (L : LocalCodes Δ) : List ((Γ.G × Fin L.r00) ⊕ (Γ.G × Fin L.r11)) :=
  ((allG Γ).flatMap fun g => (List.finRange L.r00).map fun i => Sum.inl (g, i)) ++
    ((allG Γ).flatMap fun g => (List.finRange L.r11).map fun i => Sum.inr (g, i))

/-- The rows of `H_Z`: the rows of `V01` by (`enum g`, basis index), then those of `V10`. -/
def zRows (Γ : LRData Δ) (L : LocalCodes Δ) : List ((Γ.G × Fin L.r01) ⊕ (Γ.G × Fin L.r10)) :=
  ((allG Γ).flatMap fun g => (List.finRange L.r01).map fun i => Sum.inl (g, i)) ++
    ((allG Γ).flatMap fun g => (List.finRange L.r10).map fun i => Sum.inr (g, i))

/-- The decoder's input: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript sha256 bf7a84a5…), §2, p.4: "The
erasure decoder is then given the erasure vector `ε` together with the syndromes `H_X e_Zᵀ, H_Z e_Xᵀ`."

**Formalization Note.** The paper names no machine. The words are, in order: `m = |G|`; for `a < Δ`, `g < m` the index of
`A(a)·g`; for `b < Δ`, `g < m` the index of `g·B(b)`; the `N` bits of the erasure pattern by (`g`, `a`, `b`); the bits of
`H_X e_Zᵀ` and `H_Z e_Xᵀ`, each bit one word. The complex is input since one program serves all family members; `Δ` and the
local codes are in the program. The errors themselves are never in the input. -/
def inputWords (Γ : LRData Δ) (L : LocalCodes Δ) (x : Γ.Square → Bool)
    (sX : (Γ.G × Fin L.r00) ⊕ (Γ.G × Fin L.r11) → ZMod 2)
    (sZ : (Γ.G × Fin L.r01) ⊕ (Γ.G × Fin L.r10) → ZMod 2) : List ℤ :=
  [(Fintype.card Γ.G : ℤ)] ++
    ((List.finRange Δ).flatMap fun a => (allG Γ).map fun g => (((Γ.enum (Γ.A a * g) : ℕ) : ℤ))) ++
    ((List.finRange Δ).flatMap fun b => (allG Γ).map fun g => (((Γ.enum (g * Γ.B b) : ℕ) : ℤ))) ++
    (allSquares Γ).map (fun s => if x s then 1 else 0) ++
    (xRows Γ L).map (fun r => bitWord (sX r)) ++
    (zRows Γ L).map (fun r => bitWord (sZ r))

/-- The output cells: `start + squareIdx s` holds `e′_X(s)` and `start + N + squareIdx s` holds `e′_Z(s)`, as `0` or `1`,
read as signed words. "returning estimated errors `e′_Z, e′_X ∈ F₂ⁿ`" (§2, p.4). -/
def OutputIs {W : ℕ} (Γ : LRData Δ) (start : ℕ) (mem : ℤ → BitVec W) (e'X e'Z : Γ.Square → ZMod 2) : Prop :=
  ∀ s, (mem ((start + squareIdx Γ s : ℕ) : ℤ)).toInt = bitWord (e'X s) ∧
    (mem ((start + Γ.N + squareIdx Γ s : ℕ) : ℤ)).toInt = bitWord (e'Z s)

/-- A run of the program `P` from position `0` on the memory holding `inputWords` for the pattern `x` and the syndromes
of `e_X`, `e_Z`: it halts within `t` steps (the published word RAM `TrulySubcubicAPSP.exec`) and writes `e′_X`, `e′_Z` right
after the input. The verdict is ignored. -/
def RunOutput (Γ : LRData Δ) (L : LocalCodes Δ) (P : List TrulySubcubicAPSP.Instr) (W t : ℕ) (x : Γ.Square → Bool)
    (eX eZ e'X e'Z : Γ.Square → ZMod 2) : Prop :=
  let ws := inputWords Γ L x ((HX Γ L).mulVec eZ) ((HZ Γ L).mulVec eX)
  ∃ (verdict : Bool) (mem : ℤ → BitVec W),
    TrulySubcubicAPSP.exec P t 0 (TrulySubcubicAPSP.loadWords W ws) = some (verdict, mem) ∧
      OutputIs Γ ws.length mem e'X e'Z

/-- A vector supported on the erased coordinates ("`supp(e_X), supp(e_Z) ⊆ supp(ε)`", §6, p.14). -/
def SupportedOn {ι : Type*} (e : ι → ZMod 2) (x : ι → Bool) : Prop := ∀ i, x i = false → e i = 0

end ErasureQTanner


