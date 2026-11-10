-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid
-- name    : EdgeSublinearMWIS_Main_Ellipsoid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:43:20.541845+00:00
-- url     : https://prove2.me/theorems/bd4ce977-ee6d-4579-8830-69f7fedfc96f
-- title:
--   Exact rational feasibility dialogues for finite 0–1 hulls
-- statement:
--   A rational halfspace consists of a coefficient vector and a bound. A transcript records the program-generated rational queries and the supplied cuts, each valid for one fixed convex hull of Boolean vectors and strictly violated by its query. The program receives the dimension, a fixed polynomial description bound and the cut history, without the vertices of the target hull.
--
--   The same polynomial description bound must actually describe every binary hull by a finite list of rational halfspaces with individually bounded encodings. It cannot be chosen merely to exclude possible oracle answers.
--
--   The contract requires polynomially many queries and polynomial work and query encodings. At its final permitted query the point must belong to the target, unless the program certifies that the target is empty:
--   $$\operatorname{empty\ output}\Longrightarrow P=\varnothing.$$
--   This includes lower-dimensional and empty hulls. The contract is a proposition to be established by a separate theorem. It is not an oracle instruction or a constructor property of a program. Replaying the finite transcript provides a deterministic implementation of the source's stateful dialogue with only polynomial overhead.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §5.1, GLS Theorem 6.4.1 and Lemma 6.2.4 as cited, p.15 (PDF p.15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_RoundOrCut

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- General rational halfspaces, independent of graphs or MWIS. -/
structure RationalHalfspace (d : ℕ) where
  normal : Fin d → ℚ
  bound : ℚ

def RationalHalfspace.eval {d : ℕ} (c : RationalHalfspace d) (y : Fin d → ℚ) : ℚ :=
  ∑ i, c.normal i * y i

noncomputable def RationalHalfspace.evalReal {d : ℕ} (c : RationalHalfspace d)
    (y : Fin d → ℝ) : ℝ := ∑ i, (c.normal i : ℝ) * y i

def vectorBits {d : ℕ} (y : Fin d → ℚ) : List Bool :=
  ((List.ofFn (fun i => encodeRat (y i))).flatten)

def RationalHalfspace.bits {d : ℕ} (c : RationalHalfspace d) : List Bool :=
  vectorBits c.normal ++ encodeRat c.bound

def ellipsoidWord (bound : Polynomial ℕ) (d : ℕ) (cuts : List (RationalHalfspace d)) : List Bool :=
  encodeNat d ++ encodeNat (bound.eval (d + 1)) ++ encodeNat cuts.length ++
    cuts.flatMap RationalHalfspace.bits

noncomputable def binaryHull {d : ℕ} (V : Finset (Fin d → Bool)) : Set (Fin d → ℝ) :=
  convexHull ℝ {z | ∃ v ∈ V, ∀ i, z i = if v i then 1 else 0}

/-- A transcript records real program queries, followed by supplied rational cuts.
Validity is with respect to the same fixed target polytope throughout. -/
def AdmissibleDialogue (E : Program) (bound : Polynomial ℕ) (d : ℕ)
    (V : Finset (Fin d → Bool)) (qs : List (Fin d → ℚ))
    (cs : List (RationalHalfspace d)) : Prop :=
  qs.length = cs.length ∧ ∀ i (hi : i < cs.length),
    ∃ y : Fin d → ℚ, qs[i]? = some y ∧
      Evaluates E (ellipsoidWord bound d (cs.take i)) (true :: vectorBits y) ∧
      (cs[i]).bound < (cs[i]).eval y ∧
      (∀ z ∈ binaryHull V, (cs[i]).evalReal z ≤ ((cs[i]).bound : ℝ)) ∧
      (cs[i]).bits.length ≤ bound.eval (d + 1)

/-- A genuine bounded description of each target hull. The bound is an obligation,
not a freely chosen cutoff that can exclude every possible oracle answer. -/
def BinaryHullDescriptions (bound : Polynomial ℕ) : Prop :=
  ∀ (d : ℕ) (V : Finset (Fin d → Bool)),
    ∃ hs : List (RationalHalfspace d),
      (∀ c ∈ hs, c.bits.length ≤ bound.eval (d + 1)) ∧
      ∀ z : Fin d → ℝ, z ∈ binaryHull V ↔
        ∀ c ∈ hs, c.evalReal z ≤ (c.bound : ℝ)

/-- Exact oracle feasibility for 0–1 hulls, including empty and lower-dimensional
hulls. This is a specification to be established by a theorem, never a Program field
or an input hypothesis of the MWIS goal. Polynomials are fixed before d, V and cuts. -/
def ExactEllipsoid (E : Program) (bound queries work coordinates : Polynomial ℕ) : Prop :=
  BinaryHullDescriptions bound ∧
  ∀ (d : ℕ) (V : Finset (Fin d → Bool)) (qs : List (Fin d → ℚ))
    (cs : List (RationalHalfspace d)),
    AdmissibleDialogue E bound d V qs cs → cs.length ≤ queries.eval (d + 1) →
    ∃ t : ℕ, t ≤ work.eval (d + 1) ∧
      ((Runs E (ellipsoidWord bound d cs) [false] t ∧ binaryHull V = ∅) ∨
        ∃ y : Fin d → ℚ, Runs E (ellipsoidWord bound d cs) (true :: vectorBits y) t ∧
          (vectorBits y).length ≤ coordinates.eval (d + 1) ∧
          (cs.length = queries.eval (d + 1) → (fun i => (y i : ℝ)) ∈ binaryHull V))

end EdgeSublinearMWIS.Main


