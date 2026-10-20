-- Prove2me | Definitions.Def_Milne_world
-- name    : Milne_world
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T02:08:37.350249+00:00
-- url     : https://prove2.me/theorems/0539dd46-f61a-4fd7-a60e-01b42e08fc42
-- title:
--   The algebra of correspondences between nonsingular projective varieties
-- statement:
--   The raw material of the theory of motives, in the form of an interface. For nonsingular projective varieties over a fixed base field, the group of correspondences from X to Y is the group of algebraic cycles on X × Y, modulo the chosen adequate equivalence relation (rational or numerical), with rational coefficients. In the formalization the varieties, the cycles, and the equivalence relation are abstract: a CorrWorld package consists of a type of varieties carrying a product, a designated point, a projective line, and a curve of every genus; for each pair of varieties, a Q-vector space of correspondences equipped with a degree function into the integers, composition, diagonals, transposes, and exterior products; the two Künneth idempotents of the projective line and the three Künneth idempotents of the curve of every genus; and trace data for idempotent correspondences. The fields asserting equations — the abelian group and Q-module laws, the composition laws with the diagonal as a two-sided unit, the degree laws, the closure of the sandwiched subspaces under the operations, the Künneth diagonal decompositions, and the trace values of the Künneth pieces — are the deep inputs of intersection theory: every statement built on the world carries the world as a hypothesis.
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Sections 4-6 (pp. 5-7).

import Mathlib

universe u v

/-!
# Motives — Grothendieck's dream: the correspondence algebra

An abstract interface for the algebra of algebraic cycles on products of
nonsingular projective varieties, presented through correspondences: the
group of correspondences from X to Y is the group of algebraic cycles
on X × Y modulo the chosen equivalence relation (rational or numerical),
tensored with ℚ. The interface carries the abelian group structure, the
degree function, composition, the diagonal, the transpose, the exterior
product, and the trace data for idempotent correspondences, together with
the designated point, projective line, curves of every genus, and their
Künneth idempotents. This is the arena in which the category of effective
motives of the source is built (sections 4 to 6 and 8 of the paper).
-/

namespace Milne

/-- The world of correspondences of the source: nonsingular projective
varieties with a product, a designated point and projective line, curves of
every genus, and for each pair of varieties the ℚ-vector space of
correspondences between them — algebraic cycles on the product, modulo the
chosen equivalence relation, tensored with ℚ — with composition,
diagonals, transposes, exterior products, degrees, and trace data. The
fields asserting equations are hypotheses of every statement built on the
world: the deep inputs of intersection theory — the moving lemmas and the
well-definedness of the products of cycle classes — live in these
fields. -/
structure CorrWorld where
  /-- the nonsingular projective varieties -/
  Var : Type u
  /-- the product of two varieties -/
  prod : Var → Var → Var
  /-- a designated point -/
  pt : Var
  /-- a designated projective line -/
  P1 : Var
  /-- a curve of genus g, for every genus -/
  curve : ℕ → Var
  /-- the correspondences from X to Y: cycles on X × Y modulo the
  equivalence relation, tensored with ℚ -/
  Corr : Var → Var → Type v
  /-- the degree of a correspondence: codimension on X × Y minus the
  dimension of X -/
  deg : ∀ {X Y : Var}, Corr X Y → ℤ
  /-- the zero correspondence -/
  zero : ∀ (X Y : Var), Corr X Y
  /-- pointwise addition -/
  add : ∀ {X Y : Var}, Corr X Y → Corr X Y → Corr X Y
  /-- the additive inverse -/
  neg : ∀ {X Y : Var}, Corr X Y → Corr X Y
  /-- the ℚ-scalar multiplication -/
  smul : ∀ {X Y : Var}, ℚ → Corr X Y → Corr X Y
  /-- composition of correspondences: a correspondence from X to Y
  followed by a correspondence from Y to Z -/
  cc : ∀ {X Y Z : Var}, Corr X Y → Corr Y Z → Corr X Z
  /-- the diagonal correspondence -/
  delta : ∀ X : Var, Corr X X
  /-- the transpose of a correspondence -/
  transp : ∀ {X Y : Var}, Corr X Y → Corr Y X
  /-- the exterior product of correspondences -/
  cross : ∀ {X Y X' Y' : Var}, Corr X Y → Corr X' Y' → Corr (prod X X') (prod Y Y')
  /-- the ℚ-valued trace functional on the correspondences of the point -/
  trQ : Corr pt pt → ℚ
  /-- the evaluation correspondence attached to an idempotent on X -/
  evalC : ∀ (X : Var) (e : Corr X X), Corr (prod X X) pt
  /-- the coevaluation correspondence attached to an idempotent on X -/
  coevC : ∀ (X : Var) (e : Corr X X), Corr pt (prod X X)
  /-- the ℚ-valued trace of the identity endomorphism of the motive cut
  out by an idempotent correspondence -/
  trId : ∀ (X : Var) (e : Corr X X), ℚ
  /-- the two Künneth idempotents of the projective line (the classes of a
  point and of a line) -/
  e0 : Corr P1 P1
  e2 : Corr P1 P1
  /-- the Künneth idempotents of the curve of genus g -/
  pi0 : ∀ g : ℕ, Corr (curve g) (curve g)
  pi1 : ∀ g : ℕ, Corr (curve g) (curve g)
  pi2 : ∀ g : ℕ, Corr (curve g) (curve g)
  -- abelian group laws for the correspondence groups
  add_comm : ∀ {X Y : Var} (a b : Corr X Y), add a b = add b a
  add_assoc : ∀ {X Y : Var} (a b c : Corr X Y), add (add a b) c = add a (add b c)
  add_zero : ∀ {X Y : Var} (a : Corr X Y), add a (zero X Y) = a
  zero_add : ∀ {X Y : Var} (a : Corr X Y), add (zero X Y) a = a
  neg_add_cancel : ∀ {X Y : Var} (a : Corr X Y), add (neg a) a = zero X Y
  add_neg_cancel : ∀ {X Y : Var} (a : Corr X Y), add a (neg a) = zero X Y
  neg_neg : ∀ {X Y : Var} (a : Corr X Y), neg (neg a) = a
  neg_zero : ∀ (X Y : Var), neg (zero X Y) = zero X Y
  -- ℚ-module laws
  one_smul : ∀ {X Y : Var} (a : Corr X Y), smul 1 a = a
  smul_zero : ∀ (X Y : Var) (c : ℚ), smul c (zero X Y) = zero X Y
  smul_add : ∀ {X Y : Var} (c : ℚ) (a b : Corr X Y),
    smul c (add a b) = add (smul c a) (smul c b)
  add_smul : ∀ {X Y : Var} (c d : ℚ) (a : Corr X Y),
    smul (c + d) a = add (smul c a) (smul d a)
  mul_smul : ∀ {X Y : Var} (c d : ℚ) (a : Corr X Y), smul (c * d) a = smul c (smul d a)
  -- degrees
  deg_zero : ∀ (X Y : Var), deg (zero X Y) = 0
  deg_delta : ∀ (X : Var), deg (delta X) = 0
  deg_neg : ∀ {X Y : Var} (a : Corr X Y), deg (neg a) = deg a
  deg_add_eq : ∀ {X Y : Var} (a b : Corr X Y), deg a = deg b → deg (add a b) = deg a
  deg_smul_zero : ∀ {X Y : Var} (c : ℚ) (a : Corr X Y), deg a = 0 → deg (smul c a) = 0
  deg_cc_zero : ∀ {X Y Z : Var} (a : Corr X Y) (b : Corr Y Z),
    deg a = 0 → deg b = 0 → deg (cc a b) = 0
  deg_cross_zero : ∀ {X Y X' Y' : Var} (a : Corr X Y) (b : Corr X' Y'),
    deg a = 0 → deg b = 0 → deg (cross a b) = 0
  -- composition laws
  cc_assoc : ∀ {X Y Z W : Var} (a : Corr X Y) (b : Corr Y Z) (c : Corr Z W),
    cc (cc a b) c = cc a (cc b c)
  cc_id_left : ∀ {X Y : Var} (a : Corr X Y), cc (delta X) a = a
  cc_id_right : ∀ {X Y : Var} (a : Corr X Y), cc a (delta Y) = a
  cc_add_left : ∀ {X Y Z : Var} (a₁ a₂ : Corr X Y) (b : Corr Y Z),
    cc (add a₁ a₂) b = add (cc a₁ b) (cc a₂ b)
  cc_add_right : ∀ {X Y Z : Var} (a : Corr X Y) (b₁ b₂ : Corr Y Z),
    cc a (add b₁ b₂) = add (cc a b₁) (cc a b₂)
  cc_neg_left : ∀ {X Y Z : Var} (a : Corr X Y) (b : Corr Y Z), cc (neg a) b = neg (cc a b)
  cc_neg_right : ∀ {X Y Z : Var} (a : Corr X Y) (b : Corr Y Z), cc a (neg b) = neg (cc a b)
  cc_zero_left : ∀ (X Y Z : Var) (b : Corr Y Z), cc (zero X Y) b = zero X Z
  cc_zero_right : ∀ (X Y Z : Var) (a : Corr X Y), cc a (zero Y Z) = zero X Z
  cc_smul_left : ∀ {X Y Z : Var} (c : ℚ) (a : Corr X Y) (b : Corr Y Z),
    cc (smul c a) b = smul c (cc a b)
  cc_smul_right : ∀ {X Y Z : Var} (c : ℚ) (a : Corr X Y) (b : Corr Y Z),
    cc a (smul c b) = smul c (cc a b)
  -- closure of the sandwiched subspaces f ∘ Corr ∘ e under the operations
  comp_sandwich : ∀ {X Y Z : Var} (e : Corr X X) (f : Corr Y Y) (k : Corr Z Z)
      (a : Corr X Y) (b : Corr Y Z),
    cc e e = e → cc f f = f → cc k k = k →
    cc (cc e a) f = a → cc (cc f b) k = b →
    cc (cc e (cc a b)) k = cc a b
  add_sandwich : ∀ {X Y : Var} (e : Corr X X) (f : Corr Y Y) (a₁ a₂ : Corr X Y),
    cc (cc e (add a₁ a₂)) f = add (cc (cc e a₁) f) (cc (cc e a₂) f)
  zero_sandwich : ∀ (X Y : Var) (e : Corr X X) (f : Corr Y Y),
    cc (cc e (zero X Y)) f = zero X Y
  neg_sandwich : ∀ {X Y : Var} (e : Corr X X) (f : Corr Y Y) (a : Corr X Y),
    cc (cc e (neg a)) f = neg (cc (cc e a) f)
  smul_sandwich : ∀ {X Y : Var} (e : Corr X X) (f : Corr Y Y) (c : ℚ) (a : Corr X Y),
    cc (cc e (smul c a)) f = smul c (cc (cc e a) f)
  cross_sandwich : ∀ {X Y X' Y' : Var} (e : Corr X X) (f : Corr Y Y)
      (e' : Corr X' X') (f' : Corr Y' Y') (a : Corr X Y) (b : Corr X' Y'),
    cc (cc (cross e e') (cross a b)) (cross f f') = cross (cc (cc e a) f) (cc (cc e' b) f')
  -- exterior products compose componentwise
  cross_cc : ∀ {X Y Z X' Y' Z' : Var} (a₁ : Corr X Y) (b₁ : Corr Y Z)
      (a₂ : Corr X' Y') (b₂ : Corr Y' Z'),
    cc (cross a₁ a₂) (cross b₁ b₂) = cross (cc a₁ b₁) (cc a₂ b₂)
  cross_idem : ∀ {X X' : Var} (e : Corr X X) (f : Corr X' X'),
    cc e e = e → cc f f = f → cc (cross e f) (cross e f) = cross e f
  cross_delta : ∀ (X Y : Var), cross (delta X) (delta Y) = delta (prod X Y)
  -- the complement of a sandwiched idempotent is idempotent
  compl_idem : ∀ {X : Var} (e f : Corr X X),
    cc e e = e → cc f f = f → cc (cc e f) e = f →
    cc (add e (neg f)) (add e (neg f)) = add e (neg f)
  -- the Künneth idempotents of the projective line
  e0_idem : cc e0 e0 = e0
  e2_idem : cc e2 e2 = e2
  e0_deg : deg e0 = 0
  e2_deg : deg e2 = 0
  e0_e2_zero : cc e0 e2 = zero P1 P1
  e2_e0_zero : cc e2 e0 = zero P1 P1
  p1_diag : add e0 e2 = delta P1
  endP1_span : ∀ a : Corr P1 P1, deg a = 0 → cc (cc (delta P1) a) (delta P1) = a →
    ∃ c d : ℚ, a = add (smul c e0) (smul d e2)
  -- the Künneth idempotents of the curve of genus g
  pi0_idem : ∀ g : ℕ, cc (pi0 g) (pi0 g) = pi0 g
  pi1_idem : ∀ g : ℕ, cc (pi1 g) (pi1 g) = pi1 g
  pi2_idem : ∀ g : ℕ, cc (pi2 g) (pi2 g) = pi2 g
  pi0_deg : ∀ g : ℕ, deg (pi0 g) = 0
  pi1_deg : ∀ g : ℕ, deg (pi1 g) = 0
  pi2_deg : ∀ g : ℕ, deg (pi2 g) = 0
  pi01_zero : ∀ g : ℕ, cc (pi0 g) (pi1 g) = zero (curve g) (curve g)
  pi10_zero : ∀ g : ℕ, cc (pi1 g) (pi0 g) = zero (curve g) (curve g)
  pi02_zero : ∀ g : ℕ, cc (pi0 g) (pi2 g) = zero (curve g) (curve g)
  pi20_zero : ∀ g : ℕ, cc (pi2 g) (pi0 g) = zero (curve g) (curve g)
  pi12_zero : ∀ g : ℕ, cc (pi1 g) (pi2 g) = zero (curve g) (curve g)
  pi21_zero : ∀ g : ℕ, cc (pi2 g) (pi1 g) = zero (curve g) (curve g)
  curve_diag : ∀ g : ℕ, add (add (pi0 g) (pi1 g)) (pi2 g) = delta (curve g)
  -- the trace data
  trId_eval : ∀ (X : Var) (e : Corr X X),
    trId X e = trQ (cc (cc (coevC X e) (cross (transp e) e)) (evalC X e))
  trAdd : ∀ {X : Var} (e f : Corr X X),
    cc e e = e → cc f f = f → cc (cc e f) e = f →
    trId X e = trId X (add e (neg f)) + trId X f
  tr_pi0 : ∀ g : ℕ, trId (curve g) (pi0 g) = 1
  tr_pi1 : ∀ g : ℕ, trId (curve g) (pi1 g) = -(2 * (g : ℚ))
  tr_pi2 : ∀ g : ℕ, trId (curve g) (pi2 g) = 1

end Milne


