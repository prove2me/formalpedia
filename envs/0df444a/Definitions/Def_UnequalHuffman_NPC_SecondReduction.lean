-- Prove2me | Definitions.Def_UnequalHuffman_NPC_SecondReduction
-- name    : UnequalHuffman_NPC_SecondReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:09.162203+00:00
-- url     : https://prove2.me/theorems/0ffcdc15-51e8-4c10-a95d-b4a1bbf54fd6
-- title:
--   The second reduction (13): frequencies, Γ, W, L₀, M, B₀, β, canonical codes, and codes of the output and of solutions
-- statement:
--   For a leaf-profile instance $I$ (§4.1), the symbols are the depth-position pairs, numbered $j(t,k) = \sum_{s<t} n_s + k$; symbol $j$ has prescribed depth $d_j = t$ and adjustment $\theta_j = u_{t,k}$ (`symDepths`, `theta`, listed in symbol order, 0-based). With
--   $$A = \sum_j |\theta_j|,\quad \Gamma = NA+1,\quad w_j = \Gamma\, 2^{H-d_j} + \theta_j \tag{13}$$
--   (`freqZ`, integers; `freq` are the same numbers as naturals), and
--   $$W = \sum_j w_j,\quad L_0 = \sum_j w_j d_j,\quad M = (N-1)W + 1,\quad B_0 = \sum_{t=0}^{H-1} I_t\,\Gamma\, 2^{H-t-1},\quad \beta = M L_0 + B_0,$$
--   with $I_t$ the internal counts. The output coding instance has frequencies $w_1,\dots,w_N$ and letter costs $(M, M+1)$.
--
--   A **canonical code** $C_T$ of a feasible tree $T$ (`IsCanonicalCode I T C`) assigns the symbols bijectively to the leaves of $T$, symbol $j$ to a leaf at depth $d_j$, so that within each depth the leaf coordinates are nondecreasing in the symbol number (symbol $j(t,k)$ gets a leaf of rank $k$, ties broken arbitrarily); the codewords are the root-to-leaf words.
--
--   `outCode I` is the binary code of $M$, $M+1$, $w_1,\dots,w_N$ followed by $\beta$; `encWords` codes a list of binary words (letters, then a separator per word).
--
--   Example (p. 32): rows $(0)$, $(2,-1)$ give $w = (20, 12, 9)$, $W = 41$, $M = 83$, $L_0 = 62$, $B_0 = 30$, $\beta = 5176$.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, pp. 31–32, §4.1 (eq. (13), canonical code), §4.2 (example)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_LeafProfile
import Definitions.Def_UnequalHuffman_NPC_Coding

set_option autoImplicit false

namespace UnequalHuffman.NPC

open ProjSchedTW.Complexity

namespace LPInstance

/-- The prescribed depths `d_j` of the symbols `j = j(t, k) = ∑_{s<t} n_s + k` (eq. (13)),
listed in symbol order (0-based list index `j - 1`): `n₁` copies of `1`, then `n₂` copies of
`2`, and so on. -/
def symDepths (I : LPInstance) : List ℕ :=
  (List.range I.length).flatMap fun i => List.replicate (I.getD i []).length (i + 1)

/-- The adjustments `θ_{j(t,k)} = u_{t,k}`, in symbol order. -/
def theta (I : LPInstance) : List ℤ := I.flatten

/-- `A = ∑_j |θ_j|`. -/
def bigA (I : LPInstance) : ℕ := ((I.theta).map Int.natAbs).sum

/-- `Γ = N·A + 1`. -/
def Gamma (I : LPInstance) : ℕ := I.numLeaves * I.bigA + 1

/-- The frequencies (13), `w_j = Γ·2^{H - d_j} + θ_j`, as integers, in symbol order. -/
def freqZ (I : LPInstance) : List ℤ :=
  List.zipWith (fun (d : ℕ) (θ : ℤ) => (I.Gamma : ℤ) * 2 ^ (I.length - d) + θ)
    I.symDepths I.theta

/-- The output frequencies `w₁, …, w_N` as natural numbers (`Int.toNat` of `freqZ`; Lemma 4.1
says these integers are positive). -/
def freq (I : LPInstance) : List ℕ := I.freqZ.map Int.toNat

/-- `W = ∑_j w_j`. -/
def bigW (I : LPInstance) : ℕ := I.freq.sum

/-- `L₀ = ∑_j w_j d_j`. -/
def L0 (I : LPInstance) : ℕ := (List.zipWith (· * ·) I.freq I.symDepths).sum

/-- The letter-cost scale `M = (N - 1)·W + 1`; the output letter costs are `(M, M + 1)`. -/
def bigM (I : LPInstance) : ℕ := (I.numLeaves - 1) * I.bigW + 1

/-- `B₀ = ∑_{t=0}^{H-1} I_t·Γ·2^{H-t-1}`, with `I_t` the internal counts of the profile. -/
def B0 (I : LPInstance) : ℤ :=
  ∑ t ∈ Finset.range I.length, intCount I.counts t * (I.Gamma : ℤ) * 2 ^ (I.length - t - 1)

/-- The offset `β = M·L₀ + B₀`. -/
def beta (I : LPInstance) : ℤ := (I.bigM : ℤ) * I.L0 + I.B0

/-- `C` is a canonical code `C_T` of the feasible tree `T` (§4.1): the symbols are assigned
bijectively to the leaves of `T`, symbol `j` to a leaf at its prescribed depth `d_j`, and within
each depth in sorted-coordinate order (symbol `j(t, k)` gets a leaf of rank `k`), ties broken
arbitrarily; codewords are root-to-leaf words. -/
def IsCanonicalCode (I : LPInstance) (T : OTree) (C : Fin I.freq.length → List Bool) : Prop :=
  Function.Injective C ∧
  (∀ j, C j ∈ T.leaves ∧ (C j).length = I.symDepths.getD j 0) ∧
  (∀ v ∈ T.leaves, ∃ j, C j = v) ∧
  ∀ j j' : Fin I.freq.length, I.symDepths.getD j 0 = I.symDepths.getD j' 0 → j ≤ j' →
    (C j).count true ≤ (C j').count true

/-- The binary code of the output coding instance `J` together with the offset: the letter costs
`M, M + 1`, the frequencies `w₁, …, w_N`, then `β`, all in binary. -/
def outCode (I : LPInstance) : List BSym :=
  encNats ([I.bigM, I.bigM + 1] ++ I.freq) ++ encInt I.beta

end LPInstance

/-- The code of a binary word: its letters (`0` ↦ `zero`, `1` ↦ `one`) and a separator. -/
def encWord (s : List Bool) : List BSym :=
  s.map (fun b => if b then BSym.one else BSym.zero) ++ [BSym.sep]

/-- The code of a list of binary words (codewords in symbol order, or the leaves of a tree). -/
def encWords (ws : List (List Bool)) : List BSym := ws.flatMap encWord

end UnequalHuffman.NPC


