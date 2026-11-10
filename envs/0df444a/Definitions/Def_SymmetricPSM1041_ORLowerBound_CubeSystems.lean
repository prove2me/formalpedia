-- Prove2me | Definitions.Def_SymmetricPSM1041_ORLowerBound_CubeSystems
-- name    : SymmetricPSM1041_ORLowerBound_CubeSystems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:01.144172+00:00
-- url     : https://prove2.me/theorems/9c29c67b-f265-4373-9afe-5b81aa1bd968
-- title:
--   §2.4 — ordered Boolean cubes and f-cube systems
-- statement:
--   Fix a family of alphabets $\mathcal M_i$ and the product $\Omega=\prod_i\mathcal M_i$. A cube $Q$ specifies ordered endpoints $Q_{i,0},Q_{i,1}\in\mathcal M_i$, with coincidences permitted. For $S$ a coordinate subset, its corner is
--
--   $$Q(S)_i=Q_{i,\chi_S(i)}.$$
--
--   An $f$-cube system consists of disjoint sets $Z_0,Z_1\subseteq\Omega$ and a nonempty family $\mathcal Q$ of cubes satisfying both conditions: for every $Q\in\mathcal Q$, bit $b$ and subset $S$, $f(\chi_S)=b$ if and only if $Q(S)\in Z_b$; and for every $v\in Z_b$ and every $S$ with $f(\chi_S)=b$, some $Q\in\mathcal Q$ has $Q(S)=v$.
--
--   For a protocol, the canonical family is the image of the seed map $r\mapsto((M_i(0,r),M_i(1,r)))_i$, and $Z_b$ is the set of transcripts realized on inputs with output $b$. These definitions record the exact witnesses used in Lemma 12, without asserting that they satisfy the cube-system axioms. Ordered endpoints are retained even if vertex sets coincide. Neither ambient coverage, endpoint distinctness nor nonempty output sets for a constant function is required.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), pp. 10–12, §2.4, definition of f-cube system and proof of Lemma 12

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_PSM

namespace SymmetricPSM1041.ORLowerBound

/-- Ordered local endpoints, retained even when endpoints or vertex sets coincide. -/
abbrev Cube {ι : Type*} (M : ι → Type*) := (i : ι) → Bool → M i

noncomputable def characteristic {ι : Type*} (S : Set ι) : ι → Bool := by
  classical
  exact fun i => decide (i ∈ S)

noncomputable def corner {ι : Type*} {M : ι → Type*} (Q : Cube M)
    (S : Set ι) : (i : ι) → M i := fun i => Q i (characteristic S i)

/-- The two source axioms plus disjoint output sets and a nonempty cube family.
There is no ambient coverage or nondegeneracy requirement. -/
def IsCubeSystem {ι : Type*} {M : ι → Type*} (f : (ι → Bool) → Bool)
    (cubes : Set (Cube M)) (Z : Bool → Set ((i : ι) → M i)) : Prop :=
  Disjoint (Z false) (Z true) ∧ cubes.Nonempty ∧
  (∀ Q ∈ cubes, ∀ b S, f (characteristic S) = b ↔ corner Q S ∈ Z b) ∧
  (∀ b v, v ∈ Z b → ∀ S, f (characteristic S) = b →
    ∃ Q ∈ cubes, corner Q S = v)

def protocolCubes {ι : Type*} (P : PSM ι) :
    Set (Cube (fun i => {w : Message // w ∈ P.alphabet i})) :=
  Set.range (fun r i b => P.message i b r)

def protocolOutputSupports {ι : Type*} (P : PSM ι)
    (f : (ι → Bool) → Bool) (b : Bool) : Set (Transcript P) :=
  {v | ∃ x r, f x = b ∧ transcript P x r = v}

end SymmetricPSM1041.ORLowerBound


