-- Prove2me | Definitions.Def_Zeta5_SourceArith
-- name    : Zeta5_SourceArith
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T14:18:06.882086+00:00
-- url     : https://prove2.me/theorems/a542e32c-cfd4-47bc-b23d-0693a872e83f
-- title:
--   Zeta5: the arithmetic layer of the normaliser (source `Apery/Arith/*`)
-- statement:
--   The arithmetic definitions underlying the normaliser $m_K$ of the source project `mo271/Zeta5`, module `Apery/Norm.lean` and its `Apery/Arith/*` dependencies:
--
--   * class counting: the class `ccls` of a residue mod $p = 2m+1$, the per-class count $S_X(p,c) = \#\{j \le X : j \equiv \pm c\}$ and the class constants $b_a = 5[a=0] + 6S_N(a) - S_K(a)$ (`Apery/Arith/ClassCount.lean`);
--
--   * the pole set $Pl_K = \{\pm 1, \dots, \pm K\}$ and the separation predicate $Sep_p(Pl)$ (poles in the same class differ by exactly one power of $p$) (`Apery/Arith/Pullback.lean`, `Apery/Arith/DirectBound.lean`);
--
--   * the water-filling allocation of the inner range: the row count $\ellrow(k,\beta) = \lceil (k-\beta)/2 \rceil^+$, the used rows $rowsK$, the chosen level $kfSel$ and the allocation $allocK$ (`Apery/Arith/InnerAlloc.lean`);
--
--   * the inner weights: $top_a = L_a + (b_a-4)/2$, its minimum $tmin$ over the ordinary classes, and the uncapped/capped weights $wraw$, $wcap$ (`Apery/Arith/InnerWeights.lean`);
--
--   * the outer basis: the class $jc$ of a natural number, the tail poles $N < j \le K$ of a class (`tailC`, with cardinality `LoC`), those above $p$ (`bigC`, `nbC`), and the outer weights $wO$ (`Apery/Arith/OuterBasis.lean`, `Apery/Arith/OuterEntryMain.lean`).
--
--   **Formalization Note** Nothing is proved in this module: the declarations are the definitions of the source, reproduced verbatim in the `Apery` namespace with all binder arguments explicit.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/ClassCount.lean#L24-L107 and the definition parts of Apery/Arith/Pullback.lean, Apery/Arith/DirectBound.lean, Apery/Arith/InnerAlloc.lean, Apery/Arith/InnerWeights.lean, Apery/Arith/OuterBasis.lean, Apery/Arith/OuterEntryMain.lean

import Mathlib

/-!
# The arithmetic layer of the normaliser (source `Apery/Arith/*`)

The definitions of the arithmetic chain underlying the normaliser `mN` of
"Apery/Norm.lean" of the source project `mo271/Zeta5`
(commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`):

* class counting (`Apery/Arith/ClassCount.lean`): the class of a residue, the per-class
  count `SX` and the class constants `Bse`;
* the pole set `PlK` (`Apery/Arith/Pullback.lean`) and the separation predicate `Sep`
  (`Apery/Arith/DirectBound.lean`);
* the inner-row allocation (`Apery/Arith/InnerAlloc.lean`): `lrow`, `rowsK`, `kfSel`,
  `allocK`;
* the inner weights (`Apery/Arith/InnerWeights.lean`): `topw`, `tmin`, `wraw`, `wcap`;
* the outer basis (`Apery/Arith/OuterBasis.lean`): `jc`, `tailO`, `tailC`, `LoC`, `bigC`,
  `nbC`;
* the outer weights (`Apery/Arith/OuterEntryMain.lean`): `ellC`, `delC`, `wO`.

Nothing is proved in this module; the definitions are reproduced verbatim from the source.
-/

open Finset

namespace Apery

/-! ### Class counting (`Apery/Arith/ClassCount.lean`) -/

/-- The class of a residue mod `p = 2m + 1`: the unique `a ≤ m` with `c = ±a`. -/
def ccls {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (c : ZMod p) : Fin (m + 1) :=
  if h : c.val ≤ m then ⟨c.val, by omega⟩ else ⟨p - c.val, by have := c.val_lt; omega⟩

/-- `#{j ≤ X : j ≡ c} + #{j ≤ X : j ≡ -c}`. -/
def SX (p X : ℕ) (c : ZMod p) : ℕ :=
  ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = c).card +
    ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = -c).card

/-- The class constant `5[a = 0] + 6 S_N(a) - S_K(a)`. -/
noncomputable def Bse (p K N : ℕ) (a : ℕ) : ℚ :=
  (if a = 0 then 5 else 0) + 6 * (SX p N (((a : ℤ) : ZMod p)) : ℚ) - SX p K (((a : ℤ) : ZMod p))

/-! ### The pole set (`Apery/Arith/Pullback.lean`) and separation (`Apery/Arith/DirectBound.lean`) -/

/-- The poles `±1, …, ±K`. -/
def PlK (K : ℕ) : Finset ℤ :=
  (Icc 1 K).image (fun j : ℕ => (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ => -(j : ℤ))

/-- Poles in the same class differ by exactly one power of `p`. -/
def Sep (p : ℕ) (Pl : Finset ℤ) : Prop :=
  ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → (r : ZMod p) = s → ¬ (p : ℤ) ^ 2 ∣ r - s

/-! ### The inner allocation (`Apery/Arith/InnerAlloc.lean`) -/

/-- The number of rows of offset `β` below the level `k`: `⌈(k - β)/2⌉⁺`. -/
def lrow (k β : ℤ) : ℕ := ((k - β + 1) / 2).toNat

/-- Rows used at level `k`. -/
def rowsK {m : ℕ} (β : Fin (m + 1) → ℤ) (k : ℤ) : ℕ :=
  ∑ c ∈ univ.erase (0 : Fin (m + 1)), lrow k (β c)

/-- The chosen level `kf ∈ [klo, ktop]`, the largest with at most `h - L0min` rows used. -/
noncomputable def kfSel {m : ℕ} (β : Fin (m + 1) → ℤ) (h L0min : ℕ) (klo ktop : ℤ) : ℤ :=
  klo + (Nat.findGreatest (fun j : ℕ => rowsK β (klo + j) + L0min ≤ h) (ktop - klo).toNat : ℤ)

/-- The allocation: class `0` receives the remaining rows, class `c ≠ 0` receives `lrow kf (β c)`. -/
noncomputable def allocK {m : ℕ} (β : Fin (m + 1) → ℤ) (h : ℕ) (kf : ℤ) (c : Fin (m + 1)) : ℕ :=
  if c = 0 then h - rowsK β kf else lrow kf (β c)

/-! ### The inner weights (`Apery/Arith/InnerWeights.lean`) -/

/-- `top a = L a + (b a - 4)/2`. -/
noncomputable def topw {m : ℕ} (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) (a : Fin (m + 1)) : ℚ :=
  L a + (b a - 4) / 2

/-- The minimum of `top` over the ordinary classes. -/
noncomputable def tmin {m : ℕ} (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) : ℚ :=
  (univ.erase (0 : Fin (m + 1))).inf' ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩ (topw L b)

/-- The uncapped weights. -/
noncomputable def wraw {m : ℕ} (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then 2 * (s.2 : ℚ) + (b 0 - 4) / 2 else (s.2 : ℚ) + (b s.1 - 4) / 2

/-- The capped weights `min (wraw) (min_{c ≠ 0} top c)`. -/
noncomputable def wcap {m : ℕ} (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  min (wraw L b s) (tmin hm L b)

/-! ### The outer basis (`Apery/Arith/OuterBasis.lean`) -/

/-- The class of a natural number. -/
def jc {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (j : ℕ) : Fin (m + 1) :=
  ccls hm (((j : ℤ) : ZMod p))

/-- The tail poles `N < j ≤ K` with `N = 3n`, `K = 40n`. -/
def tailO (n : ℕ) : Finset ℕ := Icc (3 * n + 1) (40 * n)

/-- The tail poles of class `c`. -/
def tailC {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (c : Fin (m + 1)) : Finset ℕ :=
  (tailO n).filter fun j => jc hm j = c

/-- `Lo c = #(tail poles of class c)`. -/
def LoC {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (c : Fin (m + 1)) : ℕ := (tailC hm n c).card

/-- The tail poles of class `c` above `p`. -/
def bigC {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (c : Fin (m + 1)) : Finset ℕ := (tailC hm n c).filter fun j => p < j

/-- `nb c = #(tail poles of class c above p)`. -/
def nbC {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (c : Fin (m + 1)) : ℕ := (bigC hm n c).card

/-! ### The outer weights (`Apery/Arith/OuterEntryMain.lean`) -/

/-- `ℓ(c) = #{j ≤ K : j ≡ ±c}`. -/
def ellC {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (c : Fin (m + 1)) : ℕ := ((Icc 1 (40 * n)).filter fun j => jc hm j = c).card

/-- `δ(c) = [c ≤ N]`. -/
def delC {m : ℕ} (n : ℕ) (c : Fin (m + 1)) : ℕ := if (c : ℕ) ≤ 3 * n then 1 else 0

/-- The outer weights (4.12). -/
noncomputable def wO {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ)
    (c : Fin (m + 1)) (i : ℕ) : ℚ :=
  if c = 0 then (if i < nbC hm n 0 then -2 else if nbC hm n 0 = 0 then -1 / 2 else 0)
  else (if i < nbC hm n c then min 0 ((i : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2)
    else 0)

end Apery


