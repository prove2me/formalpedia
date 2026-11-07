-- Prove2me | Definitions.Def_TimeSpaceMA_SubsetSumCode
-- name    : TimeSpaceMA_SubsetSumCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:11.255842+00:00
-- url     : https://prove2.me/theorems/90e8c722-92a3-4097-a6d2-73142ebaeae6
-- title:
--   Subset-sum code
-- statement:
--   A **subset-sum code** of message length $q$ and block length $L$ is a list $S_1,\dots,S_L$ of nonempty subsets of $[q]$, the supports. For an abelian group $A$ it defines $G:A^q\to A^L$, $G(z)_\ell=\sum_{j\in S_\ell}z_j$; a codeword is a word in the image.
--
--   The code is **systematic** if every $j$ has an index $\sigma(j)$ with $S_{\sigma(j)}=\{j\}$. The relative distance is $\delta=q/L$. The property of Lemma 3.10(b) is that for every abelian group $A$ and every nonzero $z\in A^q$, the word $G(z)$ has at least $q$ nonzero coordinates.
--
--   **Formalization Note** $A$ ranges over abelian groups in Lean's `Type`, which contains $\mathbb Q/\mathbb Z$ and the number fields the proof uses.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definition 3.9, p.11; Lemma 3.10(b), p.12

import Mathlib

namespace TimeSpaceMA

/-- A subset-sum code of message length `q` and block length `L` (Williams, Xi, STOC 2027 submission,
manuscript sha256 184c2f95…, Definition 3.9, p.11): a list `S₁, …, S_L` of nonempty subsets of `[q]`,
the supports. -/
structure SubsetSumCode (q L : ℕ) where
  supp : Fin L → Finset (Fin q)
  nonempty : ∀ ℓ, (supp ℓ).Nonempty

namespace SubsetSumCode

variable {q L : ℕ}

/-- The encoding map `G : A^q → A^L`, `G(z)_ℓ = Σ_{j ∈ S_ℓ} z_j`. -/
def encode (G : SubsetSumCode q L) {A : Type*} [AddCommMonoid A] (z : Fin q → A) : Fin L → A :=
  fun ℓ => ∑ j ∈ G.supp ℓ, z j

/-- A codeword is a word in the image of `G`. -/
def IsCodeword (G : SubsetSumCode q L) {A : Type*} [AddCommMonoid A] (y : Fin L → A) : Prop :=
  ∃ z : Fin q → A, y = G.encode z

/-- Systematic, with chosen indices `σ`: the support at `σ j` is `{j}`. -/
def IsSystematic (G : SubsetSumCode q L) (σ : Fin q → Fin L) : Prop :=
  ∀ j, G.supp (σ j) = {j}

/-- The relative distance `δ := q / L`. -/
noncomputable def delta (_G : SubsetSumCode q L) : ℝ := (q : ℝ) / L

open Classical in
/-- Lemma 3.10(b), p.12: for every abelian group `A` and every nonzero `z ∈ A^q`, the codeword `G(z)`
has at least `q` nonzero coordinates.

**Formalization Note** `A` ranges over abelian groups in `Type`; the proof applies it at `ℚ/ℤ` and at a
number field. -/
def HasGroupDistance (G : SubsetSumCode q L) : Prop :=
  ∀ (A : Type) [AddCommGroup A] (z : Fin q → A), z ≠ 0 →
    q ≤ (Finset.univ.filter fun ℓ => G.encode z ℓ ≠ 0).card

end SubsetSumCode

end TimeSpaceMA


