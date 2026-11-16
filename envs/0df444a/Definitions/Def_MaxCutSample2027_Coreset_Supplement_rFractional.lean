-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_Supplement_rFractional
-- name    : MaxCutSample2027_Coreset_Supplement_rFractional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:59:20.396918+00:00
-- url     : https://prove2.me/theorems/117bc123-4d4c-4745-9196-685bee5fe19e
-- title:
--   Fractional r-way cuts and comparison functionals
-- statement:
--   For $r\ge2$, a nonnegative vertex-mass vector $q$, and the base kernel $K$, put
--   $$Z_r(q)=\{a=(a^j)_j:a^j_v\ge0,\ \sum_ja^j_v=q_v\},\qquad
--   F_{K,r}(q)=\max_{a\in Z_r(q)}\sum_{j<\ell}(a^j)^\top Ka^\ell.$$
--   The linear comparison objective uses ordered distinct part pairs:
--   $$T_K(a,c)=\sum_{j\ne\ell}(a^j)^\top Kc^\ell,\qquad M_{q,r}(c)=\max_{a\in Z_r(q)}T_K(a,c).$$
--   Let $C_r(q,s)$ be the convex hull of $Z_r(q),-Z_r(q),Z_r(s),-Z_r(s)$ and define
--   $$\Delta_{K,r}(q,s)=\max_{c\in C_r(q,s)}|M_{q,r}(c)-M_{s,r}(c)|.$$
--   The matching error of $a,b$ on a region $C$ is $\max_{c\in C}|T_K(a-b,c)|$. These are the defining maxima, without substituting the closed form of $M$. Real suprema encode the maxima; all uses have nonnegative masses and hence nonempty compact feasible sets. This shared model supports both the matching and comparison statements.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §5.2–§5.3, eqs. (5.6)–(5.14), p. 26–27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rCuts
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

/-- Equation (5.6): nonnegative part masses whose sum is q. -/
def Zr {V : Type*} (r : ℕ) (q : V → ℝ) : Set (Fin r → V → ℝ) :=
  {a | (∀ j v, 0 ≤ a j v) ∧ ∀ v, ∑ j, a j v = q v}

/-- Part pairs j < l count the cut once. -/
def fractionalValueR {V : Type*} [Fintype V] {r : ℕ}
    (L : V → V → ℝ) (a : Fin r → V → ℝ) : ℝ :=
  ∑ j, ∑ l, if j < l then bilinear L (a j) (a l) else 0

def FKr {V : Type*} [Fintype V] (r : ℕ) (L : V → V → ℝ) (q : V → ℝ) : ℝ :=
  sSup (fractionalValueR L '' Zr r q)

/-- Ordered distinct part pairs in the linear objective (5.9). -/
def crossLinearR {V : Type*} [Fintype V] {r : ℕ}
    (L : V → V → ℝ) (a c : Fin r → V → ℝ) : ℝ :=
  ∑ j, ∑ l, if j ≠ l then bilinear L (a j) (c l) else 0

/-- Defining maximum, not the closed form (5.10). -/
def Mr {V : Type*} [Fintype V] (r : ℕ) (L : V → V → ℝ)
    (q : V → ℝ) (c : Fin r → V → ℝ) : ℝ :=
  sSup ((fun a => crossLinearR L a c) '' Zr r q)

def Cr {V : Type*} (r : ℕ) (q s : V → ℝ) : Set (Fin r → V → ℝ) :=
  convexHull ℝ (Zr r q ∪ ((fun a : Fin r → V → ℝ => -a) '' Zr r q) ∪
    Zr r s ∪ ((fun a : Fin r → V → ℝ => -a) '' Zr r s))

def DeltaKr {V : Type*} [Fintype V] (r : ℕ) (L : V → V → ℝ) (q s : V → ℝ) : ℝ :=
  sSup ((fun c => |Mr r L q c - Mr r L s c|) '' Cr r q s)

/-- Uniform matching error used in both directions of Lemma 5.6. -/
def matchingErrorR {V : Type*} [Fintype V] {r : ℕ} (L : V → V → ℝ)
    (a b : Fin r → V → ℝ) (C : Set (Fin r → V → ℝ)) : ℝ :=
  sSup ((fun c => |crossLinearR L (a - b) c|) '' C)

end MaxCutSample2027.Coreset.Supplement


