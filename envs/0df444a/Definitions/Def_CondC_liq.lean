-- Prove2me | Definitions.Def_CondC_liq
-- name    : CondC_liq
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T15:44:00.101814+00:00
-- url     : https://prove2.me/theorems/fa32e9b8-e46a-4150-9237-6ce26b40c492
-- title:
--   The liquid layer: p-summability, p-liquid vector spaces, and disc algebras
-- statement:
--   The liquid layer of Clausen and Scholze's "Condensed Mathematics and Complex Geometry" (lecture notes, May 2026 version): the propositional content of Lectures I-IV. LiqSummable p c is the paper's p-summability condition on a scalar family: for every 0 < q < p, the partial sums of the q-th powers of the norms are bounded, the condition defining the space S_q(C) of the liquid lectures. PLiquidStructure p V is the interface of a p-liquid C-vector space: a designated space of summable families containing the Dirac families and closed under pointwise addition, subtraction, and scalar multiplication; a designated space of null sequences containing the eventually zero families and closed under pointwise addition and scalar multiplication; and the integration functional on the null sequences, extending the Dirac evaluation and compatible with the operations, and uniquely determined by these requirements. IsPLiquid p V records that V carries such a structure. PowerDecay r a is the convergence condition of Theorem 1.1 in norm form: for every r' with 0 < r' < r, the norms of the coefficients times r' ^ n tend to zero. DiscAlgebraData r V identifies a C-vector space with the power series converging on the disc of radius r: a coefficient expansion that is bijective onto the decaying families, compatible with the vector space operations. PowerDecay2 and DiscAlgebraData2 are the two-variable analogues for the polydisc, with the decay in epsilon-N form. LiquidBilinear p V W U records that a bilinear map between p-liquid spaces carries designated null sequences to designated null sequences in each variable, the condition characterizing the bilinear maps descending to the liquid tensor product.
--
--   **Formalization Note** The paper's condensed and liquid infinity-categories are replaced by this interface; the existence of the designated structures on the concrete spaces of the paper is the proposed work of the mission. Profinite sets are idealized as the one-point compactification of the naturals, and the null sequences are designated abstractly, as in the paper's first formulation of liquidness.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (May 2026 version), Lectures I-IV.

import Mathlib

/-!
# The liquid layer: p-summability, p-liquid vector spaces, and disc algebras

The liquid layer of the CondC mission, carrying the propositional content of
Lectures I-IV of Clausen and Scholze, "Condensed Mathematics and Complex
Geometry" (May 2026 version): the p-summability condition on scalar families;
the interface of a p-liquid C-vector space, with its designated summable
families, its designated null sequences, and its unique integration
functional; the power-decay conditions and the disc algebra data identifying a
vector space with power series converging on a disc, in one and two
variables; and the liquid bilinear maps. Profinite sets are idealized as the
one-point compactification of N, and null sequences are designated
abstractly, as in the paper's first formulation of liquidness.
-/

namespace CondC

/-- The p-summability condition on a scalar family: for every 0 < q < p, the
partial sums of the q-th powers of the norms are bounded. This is the
condition defining the space S_q(C) of the paper's lectures on liquid
vector spaces. -/
def LiqSummable (p : ℝ) (c : ℕ → ℂ) : Prop :=
  ∀ q : ℝ, 0 < q → q < p → ∃ B : ℝ, ∀ N : ℕ, (∑ n ∈ Finset.range N, ‖c n‖ ^ q) ≤ B

/-- The Dirac family at index n with value v. -/
def DiracV {V : Type} [AddCommGroup V] (v : V) (n : ℕ) : ℕ → V :=
  fun m => if m = n then v else 0

/-- The interface of a p-liquid C-vector space: a designated space of
summable families containing the Dirac families and closed under the
operations; a designated space of null sequences containing the eventually
zero families and closed under the operations; and a unique integration
functional on the null sequences, extending the Dirac evaluation and
compatible with the operations. The existence of such a structure on a space
V is the content of the paper's liquidness results; the uniqueness of the
integration functional is part of the interface. -/
structure PLiquidStructure (p : ℝ) (V : Type) [AddCommGroup V] [Module ℂ V] where
  summable : (ℕ → V) → Prop
  dirac_summable : ∀ (v : V) (n : ℕ), summable (DiracV v n)
  summable_add : ∀ a b : ℕ → V, summable a → summable b → summable (fun n => a n + b n)
  summable_sub : ∀ a b : ℕ → V, summable a → summable b → summable (fun n => a n - b n)
  summable_smul : ∀ (k : ℂ) (a : ℕ → V), summable a → summable (fun n => k • a n)
  nullseq : (ℕ → V) → Prop
  null_add : ∀ a b : ℕ → V, nullseq a → nullseq b → nullseq (fun n => a n + b n)
  null_smul : ∀ (k : ℂ) (a : ℕ → V), nullseq a → nullseq (fun n => k • a n)
  null_eventually_zero : ∀ a : ℕ → V, (∃ N : ℕ, ∀ n ≥ N, a n = 0) → nullseq a
  integrate : ∀ a : ℕ → V, nullseq a → V
  integrate_dirac : ∀ (v : V) (n : ℕ) (h : nullseq (DiracV v n)),
    integrate (DiracV v n) h = v
  integrate_add : ∀ (a b : ℕ → V) (ha : nullseq a) (hb : nullseq b),
    integrate (fun n => a n + b n) (null_add a b ha hb) = integrate a ha + integrate b hb
  integrate_smul : ∀ (k : ℂ) (a : ℕ → V) (ha : nullseq a),
    integrate (fun n => k • a n) (null_smul k a ha) = k • integrate a ha
  integrate_unique : ∀ (I : ∀ a : ℕ → V, nullseq a → V),
    (∀ (v : V) (n : ℕ) (h : nullseq (DiracV v n)), I (DiracV v n) h = v) →
    (∀ (a b : ℕ → V) (ha : nullseq a) (hb : nullseq b),
      I (fun n => a n + b n) (null_add a b ha hb) = I a ha + I b hb) →
    (∀ (k : ℂ) (a : ℕ → V) (ha : nullseq a),
      I (fun n => k • a n) (null_smul k a ha) = k • I a ha) →
    ∀ (a : ℕ → V) (ha : nullseq a), I a ha = integrate a ha

/-- V is p-liquid: it carries a liquid structure. -/
def IsPLiquid (p : ℝ) (V : Type) [AddCommGroup V] [Module ℂ V] : Prop :=
  Nonempty (PLiquidStructure p V)

/-- Power decay with radius r, in the norm form of Theorem 1.1: for every
r' with 0 < r' < r, the coefficient norms times r' ^ n tend to zero. -/
def PowerDecay (r : ℝ) (a : ℕ → ℂ) : Prop :=
  ∀ r' : ℝ, 0 < r' → r' < r →
    Filter.Tendsto (fun n => ‖a n‖ * r' ^ n) Filter.atTop (nhds 0)

/-- Data identifying a C-vector space V with the power series converging on
the open disc of radius r: the coefficient expansion with the decay of
Theorem 1.1, bijective onto the decaying families, and compatible with the
vector space operations. -/
structure DiscAlgebraData (r : ℝ) (V : Type) [AddCommGroup V] [Module ℂ V] where
  coeffs : V → ℕ → ℂ
  decay : ∀ v : V, PowerDecay r (coeffs v)
  inj : ∀ (v w : V), coeffs v = coeffs w → v = w
  surj : ∀ f : ℕ → ℂ, PowerDecay r f → ∃ v : V, coeffs v = f
  coeffs_add : ∀ (v w : V) (n : ℕ), coeffs (v + w) n = coeffs v n + coeffs w n
  coeffs_zero : ∀ n : ℕ, coeffs 0 n = 0
  coeffs_smul : ∀ (k : ℂ) (v : V) (n : ℕ), coeffs (k • v) n = k * coeffs v n

/-- Two-variable power decay with radius r in each direction, in epsilon-N
form: for all radii r₁ and r₂ inside r and every positive epsilon, the
products of the norms with the radius powers are eventually below epsilon. -/
def PowerDecay2 (r : ℝ) (a : ℕ × ℕ → ℂ) : Prop :=
  ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r → 0 < r₂ → r₂ < r → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ‖a (i, j)‖ * r₁ ^ i * r₂ ^ j < ε

/-- The two-variable disc algebra data of the polydisc: the coefficient
expansion with two-variable power decay, bijective onto the decaying
families, and compatible with the vector space operations. -/
structure DiscAlgebraData2 (r : ℝ) (V : Type) [AddCommGroup V] [Module ℂ V] where
  coeffs : V → ℕ × ℕ → ℂ
  decay : ∀ v : V, PowerDecay2 r (coeffs v)
  inj : ∀ (v w : V), coeffs v = coeffs w → v = w
  surj : ∀ f : ℕ × ℕ → ℂ, PowerDecay2 r f → ∃ v : V, coeffs v = f
  coeffs_add : ∀ (v w : V) (i j : ℕ),
    coeffs (v + w) (i, j) = coeffs v (i, j) + coeffs w (i, j)
  coeffs_zero : ∀ (i j : ℕ), coeffs 0 (i, j) = 0
  coeffs_smul : ∀ (k : ℂ) (v : V) (i j : ℕ), coeffs (k • v) (i, j) = k * coeffs v (i, j)

/-- A bilinear map between p-liquid spaces is liquid when it carries
designated null sequences to designated null sequences in each variable; in
the paper this is the condition characterizing the bilinear maps descending
to the liquid tensor product. -/
def LiquidBilinear (p : ℝ) (V W U : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (lV : PLiquidStructure p V) (lW : PLiquidStructure p W) (lU : PLiquidStructure p U)
    (b : V →ₗ[ℂ] W →ₗ[ℂ] U) : Prop :=
  (∀ (a : ℕ → V), lV.nullseq a → ∀ w : W, lU.nullseq (fun n => (b (a n)) w)) ∧
  (∀ (a : ℕ → W), lW.nullseq a → ∀ v : V, lU.nullseq (fun n => (b v) (a n)))

end CondC


