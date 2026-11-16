-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Hardness
-- name    : PooledTestingAdaptivity_Gap_Supplement_Hardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:37:18.325381+00:00
-- url     : https://prove2.me/theorems/369dd0ae-a78d-4739-a7f6-1043c9c074f2
-- title:
--   The decision language "$\mathrm{OPT}_{\mathrm{dyn}}(B,J)\ge\tau$" for a fixed pool cap $G$, binary encoded
-- statement:
--   Fix a natural number $G$. An input is a tuple $(n,q_1,\dots,q_n,u_1,\dots,u_n,B,\tau)$ with $n\ge1$, rational health probabilities $0<q_i\le1$, natural-number utilities $u_i$, a natural budget $B$ and a rational threshold $\tau$. It is written over the alphabet $\{0,1,\mathrm{sep},\#\}$: a natural number in binary followed by $\mathrm{sep}$, a rational in lowest terms as a sign bit, its numerator and its denominator, and the fields separated by $\#$.
--
--   The language $L_G$ consists of exactly the strings encoding such a tuple for which the standard-model instance $J$ (these $q_i$, $u_i$, pool cap $G$) satisfies
--   $$\mathrm{OPT}_{\mathrm{dyn}}(B,J)\ge\tau,$$
--   where $\mathrm{OPT}_{\mathrm{dyn}}$ is the real optimum over dynamic policies feasible for $\mathcal F_{B,G}$. Strings that encode no such tuple are not in $L_G$.
--
--   This is the decision problem whose NP-hardness for every fixed $G\ge3$ is Theorem 3.9.
--
--   **Formalization Note.** Languages and polynomial-time reductions are those of the published `CookPvsNP_defs`. The encoding follows the binary pattern of the published `PowerMinUncut_Threshold_Machine` on its own four-letter alphabet; it is injective, so each string encodes at most one tuple. For $G=0$ the language is empty (no instance has cap $0$).
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Theorem 3.9, printed p. 11, PDF p. 12; §8, printed p. 25, PDF p. 26

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Greedy

namespace PooledTestingAdaptivity.Gap.Supplement

/-- The input alphabet: binary digits, a number separator and a field separator. -/
inductive Sym where
  | zero
  | one
  | sep
  | hash
  deriving DecidableEq

instance : Fintype Sym where
  elems := {Sym.zero, Sym.one, Sym.sep, Sym.hash}
  complete := by intro x; cases x <;> simp

def bitSym (b : Bool) : Sym := if b then Sym.one else Sym.zero

/-- A natural number in binary (`Nat.bits`, least significant bit first), terminated by `sep`. -/
def encNat (m : ℕ) : List Sym := (Nat.bits m).map bitSym ++ [Sym.sep]

/-- An integer: a sign bit (`one` for negative) then its absolute value in binary. -/
def encInt (z : ℤ) : List Sym := bitSym (decide (z < 0)) :: encNat z.natAbs

/-- A rational in lowest terms: signed numerator, then denominator, both in binary. -/
def encRat (x : ℚ) : List Sym := encInt x.num ++ encNat x.den

/-- The input `(n, q_1, …, q_n, u_1, …, u_n, B, τ)`, fields separated by `hash`. -/
def encInput (n : ℕ) (q : Fin n → ℚ) (u : Fin n → ℕ) (B : ℕ) (τ : ℚ) : List Sym :=
  encNat n ++ [Sym.hash] ++ (List.finRange n).flatMap (fun i => encRat (q i)) ++ [Sym.hash] ++
    (List.finRange n).flatMap (fun i => encNat (u i)) ++ [Sym.hash] ++ encNat B ++ [Sym.hash] ++
    encRat τ

/-- The standard-model instance with `n ≥ 1` individuals, rational health probabilities
`0 < q_i ≤ 1`, natural-number utilities and pool cap `G ≥ 1`. -/
noncomputable def stdInstance (G n : ℕ) (hG : 0 < G) (hn : 0 < n) (q : Fin n → ℚ)
    (u : Fin n → ℕ) (hq : ∀ i, 0 < q i ∧ q i ≤ 1) : Instance n where
  population_pos := hn
  q := fun i => (q i : ℝ)
  u := fun i => (u i : ℝ)
  q_pos := fun i => by exact_mod_cast (hq i).1
  q_le_one := fun i => by exact_mod_cast (hq i).2
  u_nonneg := fun i => Nat.cast_nonneg _
  cap := G
  cap_pos := hG

/-- Theorem 3.9's decision problem for a fixed pool cap `G`: the strings encoding a
standard-model instance `(n, q, u)` with pool cap `G`, a budget `B` and a rational threshold `τ`
such that `OPT_dyn(B, J) ≥ τ`. Strings encoding no such tuple are not in the language. -/
def DynOptLang (G : ℕ) : CookPvsNP.Lang Sym :=
  {w | ∃ (n : ℕ) (q : Fin n → ℚ) (u : Fin n → ℕ) (B : ℕ) (τ : ℚ)
      (hG : 0 < G) (hn : 0 < n) (hq : ∀ i, 0 < q i ∧ q i ≤ 1),
      w = encInput n q u B τ ∧
        (τ : ℝ) ≤ optDynamic (standardFamily (stdInstance G n hG hn q u hq) B)}

end PooledTestingAdaptivity.Gap.Supplement


