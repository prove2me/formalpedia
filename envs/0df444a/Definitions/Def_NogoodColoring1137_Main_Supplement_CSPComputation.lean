-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Supplement_CSPComputation
-- name    : NogoodColoring1137_Main_Supplement_CSPComputation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:57:26.770765+00:00
-- url     : https://prove2.me/theorems/600f761f-bc61-40fe-a35c-260d832ca90b
-- title:
--   Explicit binary CSP inputs, search outputs, and parameterized time
-- statement:
--   For an $n$-variable three-value binary CSP $I$ and a natural threshold $\ell$, the canonical input consists of a self-delimiting binary encoding of $n$, three unary membership bits per variable, nine relation membership bits for every pair $v<w$ in lexicographic order, and the self-delimiting binary encoding of $\ell$ last. Colors are ordered $0,1,2$ in every table. The total number of bits is
--
--   $$
--   (2\operatorname{size}(n)+1)+3n+9\binom n2+(2\operatorname{size}(\ell)+1),
--   $$
--
--   where $\operatorname{size}(a)$ is the binary bit length of the natural number $a$, with $\operatorname{size}(0)=0$. A decision answer is one bit. A search answer is the failure bit $0$ exactly on an unsatisfiable instance, or a success bit $1$ followed by the two-bit value of every color in an actual satisfying assignment.
--
--   For positive global constants $A,C$, define
--
--   $$
--   T_{A,C}(\ell,n)=A\exp\bigl(C\ell[\ln(n+1)]^2\bigr).
--   $$
--
--   This supplies only encodings and semantic answer predicates; it does not assume an algorithm or a running-time certificate.
--
--   **Formalization Note** `EncodeNat`, `EncodeColoring`, and the finite multitape execution predicate `Runs` are the published base interfaces. A run charges every transition, head movement and output step. Threshold-last encoding permits the unique empty assignment to be returned without scanning an arbitrarily long threshold. The logarithm is natural and $A,C$ are left quantified, as in the source O notation; no numerical implementation constant is asserted.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Section 8.1, p. 23–24 (printed = PDF)

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Computation
import Definitions.Def_NogoodColoring1137_Main_Supplement_CSPInstances

namespace NogoodColoring1137.Main.Supplement

/-- Explicit merged tables: n, three unary bits per variable, nine bits for
 each pair v<w in lexicographic order, then the binary threshold ell.
The threshold is last so the empty-instance branch need not read it. -/
def EncodeCSP {n : ℕ} (I : CSP n) (ell : ℕ) : List Bool :=
  EncodeNat n ++
    (List.finRange n).flatMap (fun v =>
      (List.finRange 3).map (fun a => decide (a ∈ I.unary v))) ++
    (List.finRange n).flatMap (fun v =>
      (List.finRange n).flatMap (fun w =>
        if h : v < w then
          (List.finRange 3).flatMap (fun a =>
            (List.finRange 3).map (fun b => decide ((a, b) ∈ I.relation ⟨(v, w), h⟩)))
        else [])) ++ EncodeNat ell

/-- Explicit failure, or an actual assignment satisfying every original constraint. -/
def CSPSearchAnswer {n : ℕ} (I : CSP n) (out : List Bool) : Prop :=
  (out = [false] ∧ ¬ (SolutionCode I).Nonempty) ∨
    ∃ x : Fin n → Color, I.Satisfies x ∧ out = true :: EncodeColoring x

/-- Uniform exp(O(ell log²(n+1))) bit-step bound; no cost oracle is supplied. -/
noncomputable def CSPTime (A C : ℝ) (ell n : ℕ) : ℝ :=
  A * Real.exp (C * (ell : ℝ) * Real.log ((n : ℝ) + 1) ^ 2)

end NogoodColoring1137.Main.Supplement


