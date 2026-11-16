-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions
-- name    : CatalyticTreeEval_Main_Supplement_UniformConstructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:31:49.652198+00:00
-- url     : https://prove2.me/theorems/206d1a19-9377-4e1d-939f-1bec9dc8dc4f
-- title:
--   Interval scores, least interval prime and optimal uniform vector sequences
-- statement:
--   For a modulus $m$ and an integer $D$, the interval score set is the image of $\{0,\ldots,D\}$ in $\mathbb Z_m$. A least interval prime is a prime $p$ strictly between $2D$ and $4D$ that is no larger than every prime in that interval.
--
--   A vector sequence supplies two families indexed by all $\ell$-bit labels and a dimension $d(\ell)$. At a fixed product of distinct odd primes, its optimality predicate asks for canonical-score matching, a single fixed vector printer, and uniform constants $C_d,C_s$ satisfying
--   $$d(\ell)\le C_d\ell\log_2(\ell+2),\qquad \operatorname{space}_{\mathrm{print}}(\ell)\le C_s\ell\quad(\ell\ge1).$$
--   The constants and printer are supplied before $\ell$; existence of an optimal sequence is not asserted. The positive logarithms $L(n)=1+\log_2(n+1)$, $L_2(n)=1+\log_2 L(n)$ and $L_3(n)=1+\log_2 L_2(n)$ fix the small-input convention in the input-length estimates.
--
--   These interfaces support the ordinary-space instantiations and their conditional variant.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Lemma 3.12, printed p. 17 (PDF p. 19); Lemma 3.14, printed p. 18 (PDF p. 20); Corollary 4.10, printed p. 28 (PDF p. 30); §3 base-two notation, printed p. 14 (PDF p. 16)

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

/-- The interval of squared-distance scores, interpreted as residues. -/
def intervalScores (m D : ℕ) : Set (ZMod m) := {z | ∃ a : ℕ, a ≤ D ∧ z = (a : ZMod m)}

/-- The unique least prime specified in Lemma 3.14, without assuming its existence. -/
def LeastIntervalPrime (D p : ℕ) : Prop :=
  Nat.Prime p ∧ 2 * D < p ∧ p < 4 * D ∧
    ∀ q : ℕ, Nat.Prime q → 2 * D < q → q < 4 * D → p ≤ q

/-- Data for a sequence; no success or existence theorem is built into this record. -/
structure VectorSequence (m : ℕ) where
  dimension : ℕ → ℕ
  left : (l : ℕ) → Label l → Vec m (dimension l)
  right : (l : ℕ) → Label l → Vec m (dimension l)

/-- The precise conditional hypothesis of Corollary 4.10. A single printer and both
constants are bound outside this predicate and hence outside every label length. -/
def OptimalSequence {t : ℕ} (p : Fin t → ℕ) (Q : VectorSequence (modulus p))
    (MV : Machine) (Cd Cs : ℝ) : Prop :=
  ∀ l : ℕ, 0 < l →
    SMatching (canonical p (modulus p)) (Q.left l) (Q.right l) ∧
    (Q.dimension l : ℝ) ≤ Cd * l * log₂ (l + 2) ∧
    VectorAccess MV (primeCode p ++ natCode l) (Q.left l) (Q.right l) (Cs * l)

/-- Positive iterated logarithms, equivalent to the source logarithms for large n. -/
noncomputable def loglog (n : ℕ) : ℝ := 1 + log₂ (lg n)
noncomputable def logloglog (n : ℕ) : ℝ := 1 + log₂ (loglog n)

end CatalyticTreeEval.Main.Supplement


