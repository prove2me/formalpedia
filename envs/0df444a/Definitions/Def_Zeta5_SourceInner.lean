-- Prove2me | Definitions.Def_Zeta5_SourceInner
-- name    : Zeta5_SourceInner
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T20:17:59.050253+00:00
-- url     : https://prove2.me/theorems/e9c3b49c-0195-4322-862d-5050ac958210
-- title:
--   Inner-range chain definitions: numOf, cnt, plc, tpol, xroots, winner, classRoots, entryRoots, classCount, mu, nu
-- statement:
--   This module reproduces the definitions of the inner-range chain of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the numerator `numOf κ Z = κ ∏_{ζ ∈ Z}(x - ζ)`, the class counts `cnt p Z c` and `plc p Pl c` (`Apery/Arith/DirectBound.lean`); the polynomial `tpol M = ∏_{γ ∈ M}(t + γ²)` and the root multiset `xroots M = 5·{0} + M - M` (`Apery/Arith/TEntry.lean`); the capped minimizer `winner` (`Apery/Arith/InnerWeights.lean`); the class roots `classRoots`, the integer model `tpolZ`, the entry roots `entryRoots` and the per-class count `classCount` (`Apery/Arith/ClassFrame.lean`); and the class multiplicity `mu` and dimensions `nu` (`Apery/Arith/ClassCount.lean`). Nothing is proved here.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/{DirectBound,TEntry,InnerWeights,ClassFrame,ClassCount}.lean

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit

/-!
# The direct-bound / entry / class definitions of the inner-range chain

* `numOf κ Z = κ ∏_{ζ ∈ Z} (x - ζ)` (numerator), `cnt p Z c` (zeros in the class `c`),
  `plc p Pl c` (poles in the class `c`) — `Apery/Arith/DirectBound.lean`;
* `tpol M = ∏_{γ ∈ M} (t + γ²)` and `xroots M = 5·{0} + M - M` — `Apery/Arith/TEntry.lean`;
* the capped-class minimizer `winner` — `Apery/Arith/InnerWeights.lean`;
* `classRoots`, `tpolZ`, `entryRoots`, `classCount` — `Apery/Arith/ClassFrame.lean`;
* the class multiplicity `mu` and dimensions `nu` — `Apery/Arith/ClassCount.lean`.

Nothing is proved here; reproduced verbatim from mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Apery

noncomputable def numOf (κ : ℚ) (Z : Multiset ℤ) : ℚ[X] :=
  C κ * (Z.map fun ζ : ℤ => X - C (ζ : ℚ)).prod

def cnt (p : ℕ) (Z : Multiset ℤ) (c : ZMod p) : ℕ := (Z.filter fun ζ : ℤ => (ζ : ZMod p) = c).card

def plc (p : ℕ) (Pl : Finset ℤ) (c : ZMod p) : Finset ℤ := Pl.filter fun r : ℤ => (r : ZMod p) = c

noncomputable def tpol (M : Multiset ℤ) : ℚ[X] := (M.map fun γ : ℤ => X + C ((γ : ℚ) ^ 2)).prod

def xroots (M : Multiset ℤ) : Multiset ℤ := Multiset.replicate 5 0 + M + M.map (fun γ => -γ)

noncomputable def winner {m : ℕ} (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (s : Σ a : Fin (m + 1), Fin (L a)) : ℚ :=
  if s.1 = 0 then min (2 * (s.2 : ℚ) + (b 0 - 4) / 2) (tmin hm L b)
  else (s.2 : ℚ) + (b s.1 - 4) / 2

def classRoots {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) : Multiset ℤ :=
  (∑ c ∈ Finset.univ.erase a, Multiset.replicate (L c) ((c : ℕ) : ℤ)) +
    Multiset.replicate i ((a : ℕ) : ℤ)

noncomputable def tpolZ (M : Multiset ℤ) : ℤ[X] := (M.map fun γ : ℤ => X + C (γ ^ 2)).prod

def entryRoots {m : ℕ} (N : ℕ) (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    Multiset ℤ :=
  6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)) + classRoots L s.1 s.2 + classRoots L t.1 t.2

def mu (p : ℕ) (a : ℕ) (c : ZMod p) : ℕ :=
  (if ((a : ℤ) : ZMod p) = c then 1 else 0) + (if ((a : ℤ) : ZMod p) = -c then 1 else 0)

def nu {m : ℕ} (L : Fin (m + 1) → ℕ) (s : Σ a : Fin (m + 1), Fin (L a)) (b : Fin (m + 1)) : ℕ :=
  if b = s.1 then s.2 else L b

noncomputable def classCount (p : ℕ) (K : ℕ) (M : Multiset ℤ) (c : ZMod p) : ℚ :=
  (((if c = 0 then 5 else 0) + (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
    (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) : ℚ) - (plc p (PlK K) c).card

end Apery


