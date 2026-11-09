-- Prove2me | Definitions.Def_CyclicForrelation_Even_multiShift
-- name    : CyclicForrelation_Even_multiShift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:30.202532+00:00
-- url     : https://prove2.me/theorems/2c9e4ad2-7951-47ab-8431-4f2d543dc9f5
-- title:
--   Construction 2 and its arbitrary-sign-function extension
-- statement:
--   Let $m\ge2$. Choose $m-1$ shifts $t_1,\ldots,t_{m-1}\in G$ and $m-1$ sign functions $A_1,\ldots,A_{m-1}:G\to\{-1,1\}$. Set $t_0=t_m=0$ and $a_j=t_{j-1}+t_j$. For any sign function $B$, set
--   $$F_B(x)=B(x)\prod_{j=1}^{m-1}A_j(x+t_j),$$
--   $$f_{2j-1}=\chi_{a_j}\ (1\le j\le m),\quad f_{2j}=A_j\ (1\le j<m),\quad f_{2m}=F_B.$$
--   Construction 2 takes $B\equiv\sigma$. Its law is the uniform distribution on the finite product of all shifts, all mask functions, and the sign $\sigma$. Hence all shifts, all mask entries, and $\sigma$ are independent and uniform. The deterministic construction is defined at every realization. The arbitrary $B$ version supplies the concrete objects used in Eq. (12), without assuming the identity proved there.
--
--   **Formalization Note** Interior shifts and masks use `Fin (m-1)`; the source's one-based oracle indices are translated to zero-based indices. XOR multiplies the encoded signs, and addition of cube elements is in $\mathbb F_2^n$. Shifts at the two boundaries are explicitly zero.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 10, Construction 2 and Eq. (8); p. 11, Theorem 4 proof and Eq. (12)

import Definitions.Def_CyclicForrelation_Even_cyclicTrace

namespace CyclicForrelation.Even

/-- Boundary shifts t_0=t_m=0; t contains the interior shifts in zero-based order. -/
def extendedShift {n m : ℕ} (t : Fin (m - 1) → Cube n) (j : ℕ) : Cube n :=
  if h : 0 < j ∧ j < m then t ⟨j - 1, by omega⟩ else 0

/-- The final oracle for arbitrary B; constant B is Construction 2. -/
def plantedFinal {n m : ℕ} (t : Fin (m - 1) → Cube n)
    (A : Fin (m - 1) → Cube n → Bool) (B : Cube n → Bool) (x : Cube n) : Bool :=
  Bool.xor (B x) ((List.ofFn (fun j => A j (x + t j))).foldl Bool.xor false)

/-- Eq. (8), with its last sign replaced by the sign function B as on p. 11. -/
def plantedTuple {n m : ℕ} (t : Fin (m - 1) → Cube n)
    (A : Fin (m - 1) → Cube n → Bool) (B : Cube n → Bool) : OracleTuple n (2 * m) :=
  fun j x =>
    if j.val % 2 = 0 then
      characterBit (extendedShift t (j.val / 2) + extendedShift t (j.val / 2 + 1)) x
    else if h : j.val / 2 < m - 1 then A ⟨j.val / 2, h⟩ x
    else plantedFinal t A B x

abbrev MultiShiftSeed (n m : ℕ) :=
  (Fin (m - 1) → Cube n) × (Fin (m - 1) → Cube n → Bool) × Bool

/-- Uniform law on the product: all shifts, mask entries, and the final sign are independent. -/
noncomputable def multiShiftLaw (n m : ℕ) : PMF (MultiShiftSeed n m) :=
  PMF.uniformOfFintype (MultiShiftSeed n m)

def constructionTwo {n m : ℕ} (s : MultiShiftSeed n m) : OracleTuple n (2 * m) :=
  plantedTuple s.1 s.2.1 (fun _ => s.2.2)

end CyclicForrelation.Even


