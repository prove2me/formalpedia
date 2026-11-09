-- Prove2me | Definitions.Def_BarelyTestable_LowerBound_Cube
-- name    : BarelyTestable_LowerBound_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:33.285562+00:00
-- url     : https://prove2.me/theorems/eeb92c07-60f3-4d6e-85c3-35cdbfc949d9
-- title:
--   Boolean cubes, square slacks, exact Hamming farness and finite laws
-- statement:
--   A vertex is a subset of a finite coordinate set. For an arbitrary real function $f$, a valid square has distinct coordinates $u,v$ outside its base $S$. Its slack is
--
--   $$f(S\cup\{u\})+f(S\cup\{v\})-f(S)-f(S\cup\{u,v\}).$$
--
--   Modular functions have zero slack on every valid square; constants are allowed. Restriction fixes an arbitrary assignment outside the free coordinates. Normalized Hamming distance counts exact unequal values and divides by the number of cube vertices. For an arbitrary property $P$, $f$ is $\varepsilon$-far precisely when $\varepsilon\le\operatorname{dist}(f,g)$ for every repair $g\in P$. For submodularity, the zero repair makes this class nonempty, and the minimum mismatch count is attained because only finitely many integer counts are possible.
--
--   Uniform means and probabilities are finite sums and counts divided by the cardinality of the whole sampling space; all uses have nonempty sampling spaces. Independent Bernoulli probabilities use the exact product weights, including parameters zero and one. The minimum bias is a finite minimum, initialized at one, which leaves the nonempty minimum unchanged. Coordinate projection and padding ignore extra coordinates. These operations impose no restriction on real oracle values or repairs.
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Definition 2.1, square/modular conventions, Definitions 2.4–2.5, p. 9–10 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

namespace BarelyTestable.LowerBound

abbrev Cube (ι : Type) := Finset ι
abbrev Oracle (ι : Type) := Cube ι → ℝ

/-- A valid square has distinct coordinates absent from its base. -/
def ValidSquare {ι : Type} [DecidableEq ι] (S : Cube ι) (u v : ι) : Prop :=
  u ≠ v ∧ u ∉ S ∧ v ∉ S

def slack {ι : Type} [DecidableEq ι] (f : Oracle ι) (S : Cube ι) (u v : ι) : ℝ :=
  f (insert u S) + f (insert v S) - f S - f (insert u (insert v S))

def NonnegativeSquares {ι : Type} [DecidableEq ι] (f : Oracle ι) : Prop :=
  ∀ S u v, ValidSquare S u v → 0 ≤ slack f S u v

def Modular {ι : Type} [DecidableEq ι] (f : Oracle ι) : Prop :=
  ∀ S u v, ValidSquare S u v → slack f S u v = 0

def DiminishingReturns {ι : Type} [DecidableEq ι] (f : Oracle ι) : Prop :=
  ∀ S T u, S ⊆ T → u ∉ T → f (insert u T) - f T ≤ f (insert u S) - f S

/-- Fix coordinates outside R according to Z. -/
def restriction {ι : Type} [DecidableEq ι] (f : Oracle ι) (R Z : Cube ι)
    (T : Finset {i // i ∈ R}) : ℝ :=
  f ((Z \ R) ∪ T.image Subtype.val)

noncomputable def mismatch {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : Oracle ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S => f S ≠ g S)).card

noncomputable def distance {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : Oracle ι) : ℝ := (mismatch f g : ℝ) / Fintype.card (Cube ι)

/-- Universal comparison with every repair avoids an empty/unbounded real infimum. -/
def Far {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Oracle ι → Prop) (ε : ℝ) (f : Oracle ι) : Prop :=
  ∀ g, P g → ε ≤ distance f g

/-- Exact finite uniform law, used only on inhabited finite sampling spaces. -/
noncomputable def uniformMean {α : Type} [Fintype α] [Nonempty α] (h : α → ℝ) : ℝ :=
  (∑ a, h a) / Fintype.card α

noncomputable def uniformProb {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card α

noncomputable def bernoulliProb {ℓ : ℕ} (q : Fin ℓ → ℝ) (P : Cube (Fin ℓ) → Prop) : ℝ := by
  classical
  exact ∑ S : Cube (Fin ℓ), if P S then ∏ i : Fin ℓ, (if i ∈ S then q i else 1 - q i) else 0

/-- Minimum including 1, which does not change the minimum of nonempty numbers in [0,1]. -/
noncomputable def minBias {ℓ : ℕ} (q : Fin ℓ → ℝ) : ℝ :=
  (List.ofFn (fun i => min (q i) (1 - q i))).foldl min 1

/-- Incidence-vector projection to the first d coordinates, used with d ≤ N. -/
def projectVertex {d N : ℕ} (S : Cube (Fin N)) : Cube (Fin d) :=
  Finset.univ.filter (fun i : Fin d => ∃ j ∈ S, j.val = i.val)

/-- Padding ignores the coordinates numbered d,...,N-1; requires d ≤ N at uses. -/
def pad {d N : ℕ} (f : Oracle (Fin d)) (S : Cube (Fin N)) : ℝ :=
  f (projectVertex S)

end BarelyTestable.LowerBound


