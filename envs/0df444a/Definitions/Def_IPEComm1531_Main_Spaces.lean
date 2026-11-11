-- Prove2me | Definitions.Def_IPEComm1531_Main_Spaces
-- name    : IPEComm1531_Main_Spaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:28.639944+00:00
-- url     : https://prove2.me/theorems/ee636274-10f0-43d6-b260-3c036b396de2
-- title:
--   Function-space families $V_b\subseteq\mathbb F_q^{[2r]}$, their conclusions in Theorem 3.2, and prescribed-zero functions (Lemma 3.3)
-- statement:
--   A family of spaces is given as raw data: for every level $j$ and index $b$ an ordered list $f_1,\dots,f_m$ of functions $[2r_j]\to\mathbb F_q$, and $V_b$ is their $\mathbb F_q$-span. The admissible indices are $\delta r\le b\le 2r$.
--
--   The family satisfies the conclusions of Theorem 3.2 when, at every level and for all admissible $b,c$:
--
--   1. the listed functions are linearly independent (a basis of $V_b$) and $b+1-\delta r/2\le\dim V_b\le b+1$;
--   2. $V_b\subseteq V_c$ whenever $b\le c$;
--   3. $fg\in V_{b+c}$ for $f\in V_b$, $g\in V_c$ whenever $b+c\le 2r$ (pointwise product);
--   4. every nonzero $f\in V_b$ has at most $b$ roots in $[2r]$.
--
--   It is effective when a single deterministic polynomial-time machine, given $r$ and $b$ (both in unary), outputs the listed basis of $V_b$ as the table of all its values, each value in 24 coefficient bits.
--
--   An assignment $x\mapsto p_x$ is correct (Lemma 3.3) when for every $x\in\{0,1\}^r$
--   $$p_x\in V_{|x|+\delta r}\setminus\{0\},\qquad p_x(i)=0\ \text{ for all } i\in[r]\text{ with }x(i)=1,$$
--   and effective when one polynomial-time machine, given $r$ in unary and the bits of $x$, outputs the value table $(p_x(1),\dots,p_x(2r))$.
--
--   These predicates are the interface between the algebraic-geometry construction and the communication problem.
--
--   **Formalization Note** Machines are the multi-stack Turing machines of Mathlib's `TM2ComputableInPolyTime`, through the published `PPSLattice.PolyTimeOn`; time is polynomial in the input code length, which is between $r$ and $3r+2$, so this is polynomial time in $r$. No property is built into the raw data.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Theorem 3.2, p.8; Lemma 3.3, p.8; Appendix A proof of Theorem 3.2, pp.16–17; Appendix C proof of Lemma 3.3, p.18

import Mathlib
import Definitions.Def_IPEComm1531_Main_Basic
import Definitions.Def_PPSLattice_PolyTimeOn

set_option autoImplicit false

namespace IPEComm1531.Main

open QAlgorithms.Complexity

/-- Raw data: for each level `j` and index `b`, an ordered list of `size j b` functions
`[2 r_j] → F_q`. No property is built in; correctness and effectivity are separate predicates. -/
structure Spaces where
  size : ℕ → ℕ → ℕ
  row : (j b : ℕ) → Fin (size j b) → (Fin (2 * radius j) → F)

/-- `V_b`: the `F_q`-span of the listed functions. -/
noncomputable def Spaces.space (S : Spaces) (j b : ℕ) :
    Submodule F (Fin (2 * radius j) → F) :=
  Submodule.span F (Set.range (S.row j b))

/-- The index range `δ r ≤ b ≤ 2 r` of Theorem 3.2. -/
def InRange (j b : ℕ) : Prop := slack j ≤ b ∧ b ≤ 2 * radius j

open Classical in
/-- The conclusions of Theorem 3.2 (p.8) at every level `j`: the listed functions are a basis of
`V_b`, `b + 1 − δr/2 ≤ dim V_b ≤ b + 1`, nesting, product closure for `b + c ≤ 2r`, and at most
`b` roots for nonzero `f ∈ V_b`. -/
noncomputable def Spaces.Good (S : Spaces) : Prop :=
  (∀ j b, InRange j b → LinearIndependent F (S.row j b) ∧
    (b : ℝ) + 1 - (slack j : ℝ) / 2 ≤ S.size j b ∧ S.size j b ≤ b + 1) ∧
  (∀ j b c, InRange j b → InRange j c → b ≤ c → S.space j b ≤ S.space j c) ∧
  (∀ j b c, InRange j b → InRange j c → b + c ≤ 2 * radius j →
    ∀ f ∈ S.space j b, ∀ g ∈ S.space j c, f * g ∈ S.space j (b + c)) ∧
  (∀ j b, InRange j b → ∀ f ∈ S.space j b, f ≠ 0 →
    (Finset.univ.filter fun i => f i = 0).card ≤ b)

/-- Code of the basis of `V_b`: its size in unary, then the values `f_a(i)` row by row
(`a` the basis index, `i ∈ [2r]`), each as 24 coefficient bits. -/
noncomputable def Spaces.encodedBasis (S : Spaces) (j b : ℕ) : Str :=
  encNat (S.size j b) ++
    (List.finRange (S.size j b)).flatMap fun a =>
      (List.finRange (2 * radius j)).flatMap fun i => encodeField (S.row j b a i)

/-- Input code of a pair `(r_j, b)`: both numbers in unary, so polynomial time in the code
length is polynomial time in `r`. -/
def levelIndexCode (jb : {jb : ℕ × ℕ // InRange jb.1 jb.2}) : Str :=
  encNat (radius jb.1.1) ++ encNat jb.1.2

/-- "For each function space, we can compute a basis deterministically in poly(r) time"
(Theorem 3.2, p.8): one polynomial-time machine outputs the listed basis of every `V_b`. -/
def Spaces.Effective (S : Spaces) : Prop :=
  PPSLattice.PolyTimeOn levelIndexCode (fun jb => S.encodedBasis jb.1.1 jb.1.2)

/-- An assignment `x ↦ p_x` of a function `[2 r_j] → F_q` to every `x ∈ {0,1}^{r_j}`. -/
abbrev Prescribed := (j : ℕ) → Bits (radius j) → (Fin (2 * radius j) → F)

/-- The conclusions of Lemma 3.3 (p.8): `p_x ∈ V_{|x|+δr} \ {0}` and `p_x(i) = 0` for every
`i ∈ [r]` with `x(i) = 1`. -/
def PrescribedCorrect (S : Spaces) (p : Prescribed) : Prop :=
  ∀ j (x : Bits (radius j)), p j x ∈ S.space j (weight x + slack j) ∧ p j x ≠ 0 ∧
    ∀ i : Fin (radius j), x i = 1 → p j x (Fin.castLE (by omega) i) = 0

/-- Input code of `x ∈ {0,1}^{r_j}`: `r_j` in unary, then the bits of `x`. -/
def stringCode (a : Σ j : ℕ, Bits (radius j)) : Str := encNat (radius a.1) ++ bitList a.2

/-- Code of the value table `(p_x(1), …, p_x(2r))`, each value as 24 coefficient bits. -/
noncomputable def valueTable (p : Prescribed) (a : Σ j : ℕ, Bits (radius j)) : Str :=
  (List.finRange (2 * radius a.1)).flatMap fun i => encodeField (p a.1 a.2 i)

/-- "The construction and evaluation of `p_x` can be executed deterministically in poly(r) time"
(Lemma 3.3, p.8): one polynomial-time machine outputs all `2r` values of `p_x` from `x`. -/
def PrescribedEffective (p : Prescribed) : Prop :=
  PPSLattice.PolyTimeOn stringCode (valueTable p)

end IPEComm1531.Main


