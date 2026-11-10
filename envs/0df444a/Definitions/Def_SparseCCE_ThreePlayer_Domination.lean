-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_Domination
-- name    : SparseCCE_ThreePlayer_Domination
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:04:34.2122+00:00
-- url     : https://prove2.me/theorems/c6400d82-cfbe-495f-99a9-11bced1427bc
-- title:
--   Domination by few laws (the conclusion of Lemma 3.2) and codes of finite sets of rational laws
-- statement:
--   For a finite set $C$ of laws on a finite set $S$, a family $c_1,\dots,c_r$ is **dominating** if every $c_s\in C$ and $c\le 2(c_1+\dots+c_r)$ pointwise for every $c\in C$.
--
--   A finite list of rational laws on $\mathrm{Fin}\,n$ is coded by the number of laws followed by each law as a rational vector (`encRatVec`); `lawSet l` is the set of the listed laws as real functions.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.2, p. 15.

import Mathlib
import Definitions.Def_CardinalMatching_encRatMatrix

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- `c₁, …, c_r ∈ C` dominate every law of `C` up to the factor `2` (Lemma 3.2, p. 15):
`c ≤ 2(c₁ + ⋯ + c_r)` pointwise for every `c ∈ C`. -/
def IsDominatingFamily {S : Type*} [Fintype S] (C : Finset (S → ℝ)) (r : ℕ) (c : Fin r → S → ℝ) :
    Prop :=
  (∀ s, c s ∈ C) ∧ ∀ d ∈ C, ∀ x, d x ≤ 2 * ∑ s, c s x

/-- The binary code of a finite list of rational laws on `Fin n`: the number of laws, then each
law as a rational vector (`encRatVec`). -/
def lawsCode (n : ℕ) (l : List (Fin n → ℚ)) : List Bool :=
  QAlgorithms.LocalHamiltonian.encBin l.length ++ l.flatMap (CardinalMatching.encRatVec n)

/-- A rational law on `Fin n`, as a real function. -/
def ratLawToReal {n : ℕ} (c : Fin n → ℚ) : Fin n → ℝ := fun x => (c x : ℝ)

/-- The finite set of (real) laws listed in `l`. -/
def lawSet {n : ℕ} (l : List (Fin n → ℚ)) : Finset (Fin n → ℝ) := (l.map ratLawToReal).toFinset

end SparseCCE.ThreePlayer


