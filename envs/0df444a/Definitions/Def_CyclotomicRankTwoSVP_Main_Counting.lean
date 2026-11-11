-- Prove2me | Definitions.Def_CyclotomicRankTwoSVP_Main_Counting
-- name    : CyclotomicRankTwoSVP_Main_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:09.73807+00:00
-- url     : https://prove2.me/theorems/557a95f8-ecd1-43bb-9569-61fd5523764f
-- title:
--   Binary syndrome fibers, Sidon differences, parameter domain and uniform relative error
-- statement:
--   The counting layer fixes
--
--   $$h=\lfloor21k/20\rfloor,\qquad H=h(q-h),\qquad L=2kq,\qquad c=h+\pi^{\lfloor k/2\rfloor}.$$
--
--   For a syndrome $u$, a field-position set $P$, and a Boolean assignment $\eta$ on $P$, the finite family $F(u;P,\eta)$ contains precisely the Boolean vectors with syndrome $u$, weight $h$, and restriction $\eta$. If $t$ is the number of prescribed ones, its relative error is $|(h-t)!\,|F|/q^{h-t-k+1}-1|$. The common error majorant is $q^{-ck}+3k^2/q$, for a positive absolute real $c$. Compatibility means that syndrome coordinate zero equals the specified integer coefficient sum modulo $q$.
--
--   The parameter domain is only $k\ge k_0$ and $q\ge(2k)^{C_0}$; it contains no count, separation, or complexity conclusion. A Sidon sequence is strictly increasing with injective nonzero ordered integer differences. These objects support the full uniform estimates and the separated checker positions. Natural subtractions in the relative-error formula occur only in the sufficiently large theorem regime, where their operands have the indicated order.
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), §§2.3,3.2–3.3, printed pp. 7,10–13 / PDF pp. 8,11–14, (6)–(11)

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

noncomputable section

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

def h (k : ℕ) : ℕ := 21 * k / 20

def H (q k : ℕ) : ℝ := (h k : ℝ) * ((q : ℝ) - h k)

def L (q k : ℕ) : ℝ := 2 * k * q

def center (q k : ℕ) [NeZero q] : K q := (h k : K q) + pi q ^ (k / 2)

def binaryFamily {q : ℕ} [NeZero q] (k : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : P → Bool) : Finset (ZMod q → Bool) :=
  Finset.univ.filter fun x =>
    syndrome k (fun a => if x a then 1 else 0) = u ∧
    (Finset.univ.filter fun a => x a).card = h k ∧ ∀ a : P, x a = η a

def fixedWeight {q : ℕ} [NeZero q] (P : Finset (ZMod q)) (η : P → Bool) : ℕ :=
  (Finset.univ.filter fun a : P => η a).card

def relativeError {q : ℕ} [NeZero q] (k : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : P → Bool) : ℝ :=
  |((Nat.factorial (h k - fixedWeight P η) : ℝ) * (binaryFamily k u P η).card) /
    (q : ℝ) ^ (h k - fixedWeight P η - k + 1) - 1|

def compatible {q : ℕ} (k : ℕ) (h' : ℤ) (u : Fin k → ZMod q) : Prop :=
  ∀ j : Fin k, j.val = 0 → u j = (h' : ZMod q)

def errorBound (c : ℝ) (k q : ℕ) : ℝ :=
  (q : ℝ) ^ (-c * k) + 3 * (k : ℝ) ^ 2 / q

/-- Source parameter domain, with no estimated conclusions included. -/
def parameterDomain (C₀ k₀ k q : ℕ) : Prop :=
  k₀ ≤ k ∧ (2 * k) ^ C₀ ≤ q

/-- Directed differences as integers, before reduction modulo q. -/
def IsSidon {n : ℕ} (α : Fin n → ℕ) : Prop :=
  StrictMono α ∧ ∀ j l r s : Fin n, j ≠ l → r ≠ s →
    (α l : ℤ) - α j = (α s : ℤ) - α r → j = r ∧ l = s

end CyclotomicRankTwoSVP.Main


