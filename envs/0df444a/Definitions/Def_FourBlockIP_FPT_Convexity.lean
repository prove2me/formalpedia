-- Prove2me | Definitions.Def_FourBlockIP_FPT_Convexity
-- name    : FourBlockIP_FPT_Convexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:38.768191+00:00
-- url     : https://prove2.me/theorems/5394be05-7e46-4396-a5cd-7483c954ad6c
-- title:
--   Separable convex objectives, midpoint convexity and extensions
-- statement:
--   A finite separable convex objective is a sum of real-valued univariate functions convex on the whole real line. An extended separable convex objective is a sum of univariate functions into $\mathbb R\cup\{+\infty\}$, each with a convex epigraph. Negative infinity is excluded from these coordinate functions.
--
--   Integer midpoint convexity means
--
--   $$h(z)\le\frac{h(z-q)+h(z+q)}2\quad(z,q\in\mathbb Z^m).$$
--
--   Convex extensibility on a lattice subset means that a function on the real ambient space has a convex epigraph and agrees on that subset. The ordinary extension cannot take $-\infty$; the variant for Lemma 4 may take either infinity (reading R3). Comparison oracles expose only the order of objective values at two integer vectors, including vectors outside the box. Wrong-length queries receive false; noninteger queries cannot occur in the integer-list interface.
--
--   These definitions distinguish the finite goal objective, the extended objectives used in value functions, and the two extension conventions without adding continuity or closedness assumptions.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), p. 3, definitions before Lemma 1 and Theorem 2; p. 6, Lemma 4 (reading R3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Data
import Definitions.Def_FourBlockIP_FPT_Machine

namespace FourBlockIP.FPT

/-- Finite separable convexity over the whole real space (p. 3). -/
def SepConvex {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ g : ι → ℝ → ℝ, (∀ j, ConvexOn ℝ Set.univ (g j)) ∧
    ∀ x, f x = ∑ j, g j (x j)

/-- R ∪ {+∞}, encoded in EReal with bottom excluded. Convexity means convex epigraph. -/
structure SepConvexExt (n : ℕ) where
  coord : Fin n → ℝ → EReal
  no_bot : ∀ j x, coord j x ≠ ⊥
  convex_epi : ∀ j, Convex ℝ {q : ℝ × ℝ | coord j q.1 ≤ (q.2 : EReal)}

noncomputable def SepConvexExt.eval {n : ℕ} (f : SepConvexExt n)
    (x : Fin n → ℝ) : EReal := ∑ j, f.coord j (x j)

/-- Integer midpoint convexity (p. 3); every lattice direction is tested. -/
def IntMidpointConvex {m : ℕ} (f : (Fin m → ℤ) → ℝ) : Prop :=
  ∀ x p, f x ≤ (f (x - p) + f (x + p)) / 2

/-- The p. 3 extension notion, never taking -∞. -/
def ConvexExtensibleOn {m : ℕ} (h : (Fin m → ℤ) → EReal)
    (S : Set (Fin m → ℤ)) : Prop :=
  ∃ F : (Fin m → ℝ) → EReal, (∀ x, F x ≠ ⊥) ∧
    Convex ℝ {q : (Fin m → ℝ) × ℝ | F q.1 ≤ (q.2 : EReal)} ∧
    ∀ z ∈ S, F (castVec z) = h z

/-- Lemma 4's extended-real convention (reading R3): bottom is allowed. -/
def ConvexExtensibleOnExt {m : ℕ} (h : (Fin m → ℤ) → EReal)
    (S : Set (Fin m → ℤ)) : Prop :=
  ∃ F : (Fin m → ℝ) → EReal,
    Convex ℝ {q : (Fin m → ℝ) × ℝ | F q.1 ≤ (q.2 : EReal)} ∧
    ∀ z ∈ S, F (castVec z) = h z

/-- Only a comparison bit is exposed; malformed lengths receive false.
There can be no noninteger coordinate in a list of integers. -/
noncomputable def vectorOracle {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ComparisonOracle := by
  classical
  exact fun a b => if a.length = n ∧ b.length = n then
    decide (f (fun j => (a.getD j.val 0 : ℝ)) ≤ f (fun j => (b.getD j.val 0 : ℝ)))
    else false

noncomputable def blockOracle (I : Instance) (f : (Var I → ℝ) → ℝ) : ComparisonOracle := by
  classical
  exact fun a b => if a.length = I.p + I.n * I.t ∧ b.length = I.p + I.n * I.t then
    decide (f (castVec (decodeBlockVec I a)) ≤ f (castVec (decodeBlockVec I b))) else false

end FourBlockIP.FPT


