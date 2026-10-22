-- Prove2me | Definitions.Def_HGL_tor
-- name    : HGL_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:07:20.890755+00:00
-- url     : https://prove2.me/theorems/caa6831c-af8f-4bab-8eb7-b3560574ec53
-- title:
--   The world layer: generalized string links over a surface up to link homotopy
-- statement:
--   The idealized world of generalized string links on n strands over a closed orientable surface of genus g. The definition carries: the elementary link-homotopy moves on the monoid of generalized string links, with their one-sided compatibility with concatenation on either side; the braid group of the surface with its inclusion into the monoid; the reduction of every generalized string link to a braid up to link homotopy (Theorem 3.5); the mirror operation, whose concatenation with the mirrored link is link-homotopic to the identity; the group of link-homotopy classes with its class map, its kernel characterization - a link is trivial exactly when its class is the identity - its surjectivity, and the mirror inverse law (the group structure of Theorem 3.7); the standard generators of the class group - the sigma generators and the a-generators - and the fact that they generate it; and the permutation maps of the braid group and of the class group, compatible with the class map (Proposition 3.8). The definition also carries the word builders of the presentation - the partial products of the sigma and the a generators, the t-word built from the square of a sigma generator conjugated by the preceding ones, and the A-word built from the a generators with one factor omitted, flanked by the inverse of the first sigma generator - and the two relation predicates: the presentation predicate of the closed surface, with the link-homotopy relation LH and the relations R1 through R6 of the Gonzalez-Meneses presentation, and the punctured predicate, the same with the surface relation R3 omitted (Theorem 3.9 and Corollary 3.10).
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Theorem 3.5, Theorem 3.7, Proposition 3.8, Theorem 3.9, Corollary 3.10, and the word builders of the Gonzalez-Meneses presentation).

import Mathlib
import Definitions.Def_HGL_alg

/-!
# The world layer: generalized string links over a surface

The world layer of the HGL mission: the idealized world of generalized
string links on n strands over a closed orientable surface of genus g, as
in the source paper of Juliana R. T. Theodoro de Lima. The world carries:
the link-homotopy moves on the monoid of generalized string links and their
one-sided compatibility with concatenation; the braid group with its
inclusion; the reduction of every generalized string link to a braid up to
link-homotopy (Theorem 3.5); the mirror operation providing inverses; the
group of link-homotopy classes, with the class map, its kernel
characterization, and the mirror inverse law (the group structure of
Theorem 3.7); the standard generators of the class group and the fact that
they generate; the permutation map of the braid group and the induced
permutation map of the class group (Proposition 3.8); and the relation
predicates expressing the presentations of Theorem 3.9 and Corollary 3.10,
built from the t-words and the A-words of the Gonzalez-Meneses
presentation.
-/

namespace HGL

/-- The product of the first r sigma generators, ascending (the 0-based
index i stands for the generator sigma_(i+1) of the source). -/
def sigUpTo {n : ℕ} {G : Type*} [Group G] (sigma : Fin (n - 1) → G) (r : ℕ) (hr : r ≤ n - 1) : G :=
  ((List.finRange r).map (fun i => sigma (Fin.castLE hr i))).prod

/-- The product of the first r a-generators, ascending. -/
def aUpTo {g : ℕ} {G : Type*} [Group G] (a : Fin (2 * g) → G) (r : ℕ) (hr : r ≤ 2 * g) : G :=
  ((List.finRange r).map (fun i => a (Fin.castLE hr i))).prod

/-- The word t_(1,j) of the presentation of Theorem 3.9: with the 0-based
index i standing for the generator sigma_(i+1), this is the product of the
preceding generators, the square of the i-th generator, and the inverse of
the product of the preceding generators. -/
def tWord {n : ℕ} {G : Type*} [Group G] (sigma : Fin (n - 1) → G) (i : Fin (n - 1)) : G :=
  sigUpTo sigma (i : ℕ) (Nat.le_of_lt i.isLt) * sigma i * sigma i
    * (sigUpTo sigma (i : ℕ) (Nat.le_of_lt i.isLt))⁻¹

/-- The word A_(2,s) of the presentation of Theorem 3.9: the product of the
a-generators with the s-th factor omitted - the factors before s ascending,
the factors after s ascending with inverted exponents - flanked on both
sides by the inverse of the first sigma generator sig1. -/
def a2Word {g : ℕ} {G : Type*} [Group G] (a : Fin (2 * g) → G) (sig1 : G) (s : Fin (2 * g)) : G :=
  sig1⁻¹ * (((List.finRange (2 * g)).filter (fun i => i.val < s.val)).map a).prod
    * (((List.finRange (2 * g)).filter (fun i => s.val < i.val)).map (fun i => (a i)⁻¹)).prod
    * sig1⁻¹

/-- The relations of the presentation of Theorem 3.9: the link-homotopy
relation (LH) - the commutator of the t-word with each of its conjugates by
an element of the subgroup generated by all the generators - together with
the relations R1 through R6 of the Gonzalez-Meneses presentation. -/
def SatisfiesPresentation {n g : ℕ} {G : Type*} [Group G] (hn : 2 ≤ n)
    (sigma : Fin (n - 1) → G) (a : Fin (2 * g) → G) : Prop :=
  (-- (LH)
    ∀ j : Fin (n - 1), ∀ h ∈ Subgroup.closure (Set.range a ∪ Set.range (tWord sigma)),
      tWord sigma j * (h⁻¹ * tWord sigma j * h) * (tWord sigma j)⁻¹
        * (h⁻¹ * tWord sigma j * h)⁻¹ = 1) ∧
  (-- (R1)
    ∀ i j : Fin (n - 1), i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val →
      sigma i * sigma j = sigma j * sigma i) ∧
  (-- (R2)
    ∀ (i : ℕ) (hi : i + 3 ≤ n),
      sigma ⟨i, by omega⟩ * sigma ⟨i + 1, by omega⟩ * sigma ⟨i, by omega⟩
        = sigma ⟨i + 1, by omega⟩ * sigma ⟨i, by omega⟩ * sigma ⟨i + 1, by omega⟩) ∧
  (-- (R3)
    ((List.finRange (2 * g)).map a).prod
        * ((List.finRange (2 * g)).map (fun i => (a i)⁻¹)).prod
      = sigUpTo sigma (n - 2) (by omega) * sigma ⟨n - 2, by omega⟩
        * sigma ⟨n - 2, by omega⟩ * sigUpTo sigma (n - 2) (by omega)) ∧
  (-- (R4)
    ∀ r : Fin (2 * g), ∀ s : Fin (2 * g), s.val + 1 ≤ 2 * g - 1 → r.val ≠ s.val →
      a r * a2Word a (sigma ⟨0, by omega⟩) s = a2Word a (sigma ⟨0, by omega⟩) s * a r) ∧
  (-- (R5)
    ∀ r : Fin (2 * g - 1),
      aUpTo a (r.val + 1) (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (by omega))
        * a2Word a (sigma ⟨0, by omega⟩) (Fin.castLE (by omega) r)
      = sigma ⟨0, by omega⟩ * sigma ⟨0, by omega⟩
        * a2Word a (sigma ⟨0, by omega⟩) (Fin.castLE (by omega) r)
        * aUpTo a (r.val + 1) (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (by omega))) ∧
  (-- (R6)
    ∀ r : Fin (2 * g), ∀ i : Fin (n - 1), 1 ≤ i.val → a r * sigma i = sigma i * a r)

/-- The relations of the presentation of Corollary 3.10 for the punctured
surface: the same relations as Theorem 3.9 with the relation (R3) omitted. -/
def SatisfiesPuncturedPresentation {n g : ℕ} {G : Type*} [Group G] (hn : 2 ≤ n)
    (sigma : Fin (n - 1) → G) (a : Fin (2 * g) → G) : Prop :=
  (-- (LH)
    ∀ j : Fin (n - 1), ∀ h ∈ Subgroup.closure (Set.range a ∪ Set.range (tWord sigma)),
      tWord sigma j * (h⁻¹ * tWord sigma j * h) * (tWord sigma j)⁻¹
        * (h⁻¹ * tWord sigma j * h)⁻¹ = 1) ∧
  (-- (R1)
    ∀ i j : Fin (n - 1), i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val →
      sigma i * sigma j = sigma j * sigma i) ∧
  (-- (R2)
    ∀ (i : ℕ) (hi : i + 3 ≤ n),
      sigma ⟨i, by omega⟩ * sigma ⟨i + 1, by omega⟩ * sigma ⟨i, by omega⟩
        = sigma ⟨i + 1, by omega⟩ * sigma ⟨i, by omega⟩ * sigma ⟨i + 1, by omega⟩) ∧
  (-- (R4)
    ∀ r : Fin (2 * g), ∀ s : Fin (2 * g), s.val + 1 ≤ 2 * g - 1 → r.val ≠ s.val →
      a r * a2Word a (sigma ⟨0, by omega⟩) s = a2Word a (sigma ⟨0, by omega⟩) s * a r) ∧
  (-- (R5)
    ∀ r : Fin (2 * g - 1),
      aUpTo a (r.val + 1) (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (by omega))
        * a2Word a (sigma ⟨0, by omega⟩) (Fin.castLE (by omega) r)
      = sigma ⟨0, by omega⟩ * sigma ⟨0, by omega⟩
        * a2Word a (sigma ⟨0, by omega⟩) (Fin.castLE (by omega) r)
        * aUpTo a (r.val + 1) (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (by omega))) ∧
  (-- (R6)
    ∀ r : Fin (2 * g), ∀ i : Fin (n - 1), 1 ≤ i.val → a r * sigma i = sigma i * a r)

/-- The idealized world of generalized string links on n strands over a
closed orientable surface of genus g: the monoid of generalized string
links with the link-homotopy moves; the braid group with its inclusion; the
reduction of every generalized string link to a braid up to link-homotopy
(Theorem 3.5); the mirror operation; the group of link-homotopy classes
with its class map, kernel characterization, surjectivity, and mirror
inverse law; the standard generators of the class group and the fact that
they generate it; and the permutation maps of the braid group and of the
class group. -/
structure LinkHomotopyWorld (n g : ℕ) (B S Cl : Type*) [Group B] [Monoid S] [Group Cl] where
  hn : 2 ≤ n
  moves : S → S → Prop
  move_mul : ∀ s t u : S, moves s t → moves (s * u) (t * u)
  move_mul_left : ∀ s t u : S, moves s t → moves (u * s) (u * t)
  incl : B →* S
  to_braid : ∀ s : S, ∃ b : B, EqvGen moves s (incl b)
  mirror : S → S
  mirror_compat : ∀ s : S, EqvGen moves (s * mirror s) 1
  cls : S →* Cl
  cls_moves : ∀ s t : S, EqvGen moves s t → cls s = cls t
  cls_trivial : ∀ s : S, cls s = 1 ↔ EqvGen moves s 1
  cls_surj : ∀ c : Cl, ∃ s : S, cls s = c
  cls_mirror : ∀ s : S, cls s * cls (mirror s) = 1
  gen_sigma : Fin (n - 1) → Cl
  gen_a : Fin (2 * g) → Cl
  gen_span : Subgroup.closure (Set.range gen_sigma ∪ Set.range gen_a) = ⊤
  perm : B →* Equiv.Perm (Fin n)
  perm_surj : ∀ p : Equiv.Perm (Fin n), ∃ b : B, perm b = p
  permCl : Cl →* Equiv.Perm (Fin n)
  permCl_compat : ∀ b : B, permCl (cls (incl b)) = perm b

end HGL


