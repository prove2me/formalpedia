-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_BooleanCore
-- name    : GoldreichAffine_Exponential_BooleanCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:01.675082+00:00
-- url     : https://prove2.me/theorems/445cc665-e9dd-40f5-bb9a-39e1191c0a69
-- title:
--   Boolean predicates, restrictions, affine agreement and advantage
-- statement:
--   Words and Hamming weights reuse the published `MatousekLP.Codes` definitions, which impose no additional hypotheses. A word of length $d$ is a Boolean function on the ordered positions $[d]=\{0,\ldots,d-1\}$, and a predicate $P$ is any Boolean-valued function on these words. The Hamming weight counts true coordinates. A residual with $j$ free inputs fixes every other position arbitrarily; an increasing map lists the free positions, and an auxiliary full word supplies the fixed values. Its unused free-position entries have no effect. All affine functions are included:
--   $$f_{c,A}(z)=c\oplus\bigoplus_{i\in A}z_i,\qquad c\in\{0,1\},\quad A\subseteq[j].$$
--   For a finite input mass function $\mu$, agreement is the sum of masses on the event $P(z)=f(z)$. Uniform agreement uses mass $2^{-j}$ on every word. The bit-fixing affine advantage is
--   $$\operatorname{adv}_j(P)=\max_{Q\in\mathcal R_j(P),\ f\in\mathcal A_j}\Pr[Q(U_j)=f(U_j)]-\tfrac12\qquad(0\le j\le d).$$
--   The maximum is finite and nonempty on this domain. In particular the empty cube has one word and $\operatorname{adv}_0(P)=1/2$. These definitions impose no symmetry, balance or nonlinearity on $P$ and are reusable for other Boolean predicate problems.
--
--   **Formalization Note** Words use `Fin d → Bool`; XOR is Boolean XOR, with parity computed by odd Hamming weight. Finite agreement values use nonnegative real numbers. A finite supremum computes the exact maximum. Outside the unused domain $j>d$, its candidate set is empty and the chosen maximum is zero, giving advantage $-1/2$; all statements use $j\le d$.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 4 (PDF p. 5), Definitions 1, 4 and 5 (Definitions 4–5 on p. 5 / PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic
open scoped BigOperators NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Predicates use the published Boolean-word and Hamming-weight definitions. -/
abbrev Predicate (d : ℕ) := Word d → Bool

/-- Every affine function, with both constants and every parity support. -/
def affine {j : ℕ} (c : Bool) (A : Finset (Fin j)) : Predicate j :=
  fun z => Bool.xor c (decide (Odd ((A.filter fun i => z i = true).card)))

noncomputable def IsAffine {j : ℕ} (f : Predicate j) : Prop :=
  ∃ c A, f = affine c A

/-- e lists the unfixed positions increasingly; v supplies all fixed bits.
    Values of v in the image of e are ignored. -/
noncomputable def residual {d j : ℕ} (P : Predicate d)
    (e : Fin j → Fin d) (v : Word d) : Predicate j := by
  classical
  exact fun z => P (fun p => if h : ∃ i, e i = p then z (Classical.choose h) else v p)

noncomputable def IsResidual {d j : ℕ} (P : Predicate d) (Q : Predicate j) : Prop :=
  ∃ e : Fin j → Fin d, StrictMono e ∧ ∃ v : Word d, Q = residual P e v

/-- A finite sum, so no measurability or integrability default occurs. -/
noncomputable def agreement {j : ℕ} (mass : Word j → ℝ≥0)
    (Q f : Predicate j) : ℝ≥0 := by
  classical
  exact ∑ z, if Q z = f z then mass z else 0

noncomputable def uniformMass (j : ℕ) (_ : Word j) : ℝ≥0 := 1 / (2 : ℝ≥0) ^ j

noncomputable def uniformAgreement {j : ℕ} (Q f : Predicate j) : ℝ :=
  agreement (uniformMass j) Q f

/-- Finite maximum, using bottom zero only if j > d (outside the source domain).
    For 0 ≤ j ≤ d the residual/affine candidate set is nonempty. -/
noncomputable def bestAgreement {d : ℕ} (P : Predicate d) (j : ℕ)
    (mass : Word j → ℝ≥0) : ℝ≥0 := by
  classical
  exact (Finset.univ.filter fun a : Predicate j × Predicate j =>
    IsResidual P a.1 ∧ IsAffine a.2).sup (fun a => agreement mass a.1 a.2)

noncomputable def advantage {d : ℕ} (P : Predicate d) (j : ℕ) : ℝ :=
  (bestAgreement P j (uniformMass j) : ℝ) - 1 / 2

end GoldreichAffine.Exponential


