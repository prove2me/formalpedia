-- Prove2me | Definitions.Def_StreamColour_Sketch
-- name    : StreamColour_Sketch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:00.892232+00:00
-- url     : https://prove2.me/theorems/bc415371-711c-4f55-a9c5-c8f0c9942b8a
-- title:
--   §3.2 — the capacity-$b$ sketch and its decoder
-- statement:
--   Let $p$ be a prime with $n^{50}<p<2n^{50}$ and $\xi\in\mathbb F_p$. For capacity $1\le b\le n$ the sketch of $x\in\mathbb Z^n$ is
--
--   $$\mathsf{sk}_{b,\xi}(x)=\Bigl(\bigl(\textstyle\sum_{u=1}^n x_uu^j\bigr)_{0\le j<2b},\ \sum_{u=1}^n x_u\xi^u\Bigr),$$
--
--   computed over $\mathbb F_p$. The first entries are the **moments**, the last the **fingerprint**.
--
--   A **candidate** for given moments is a vector in $\{-1,0,1\}^n$ with at most $b$ nonzero coordinates that agrees with all $2b$ moments. The **decoder** looks for a candidate, using no seed, and accepts it exactly when its fingerprint agrees with the measured one; otherwise it rejects. A sketch and its seed are $2b+2$ field elements.
--
--   **Formalization Note** A candidate is taken by choice when one exists; Lemma 3.2 shows it is unique when $p$ is in the stated range. Coordinate $u$ of `Fin n` has label $u+1$, so no label is $0$.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), §3.2, p.22 (PDF 24)

import Mathlib

namespace StreamColour

/-! # The capacity-`b` sketch and its decoder

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), §3.2, p.22 (PDF 24):
"Choose a prime p with n^50 < p < 2n^50 and a uniform seed ξ ∈ F_p. For capacity 1 ≤ b ≤ n, use
sk_{b,ξ}(x) = ((Σ_u x_u u^j)_{0≤j<2b}, Σ_u x_u ξ^u)", and the decoder of the proof of Lemma 3.2.

**Formalization Note.** Vectors are `Fin n → ℤ` with signed vectors valued in `{-1,0,1}`, and coordinate
`u : Fin n` has label `u + 1` in `1..n`, so no label is `0`. The decoder finds the signed vector of support
at most `b` that agrees with all `2b` moments, which is unique by Lemma 3.2 when the moments come from
the sketch, and accepts it exactly when its fingerprint agrees. `candidate` uses no seed. -/

variable {n : ℕ}

/-- The support of a vector. -/
def supp (x : Fin n → ℤ) : Finset (Fin n) := Finset.univ.filter fun u => x u ≠ 0

/-- The vector has entries in `{-1,0,1}`. -/
def IsSigned (x : Fin n → ℤ) : Prop := ∀ u, x u = -1 ∨ x u = 0 ∨ x u = 1

/-- The moment `Σ_u x_u u^j` over `F_p`, with labels `1..n`. -/
def moment (p : ℕ) (x : Fin n → ℤ) (j : ℕ) : ZMod p :=
  ∑ u : Fin n, (x u : ZMod p) * (((u.val + 1 : ℕ) : ZMod p)) ^ j

/-- The fingerprint `Σ_u x_u ξ^u` over `F_p`, with labels `1..n`. -/
def fingerprint (p : ℕ) (ξ : ZMod p) (x : Fin n → ℤ) : ZMod p :=
  ∑ u : Fin n, (x u : ZMod p) * ξ ^ (u.val + 1)

/-- The measurements of a capacity-`b` sketch: `2b` moments and a fingerprint. -/
abbrev Measurements (p b : ℕ) : Type := (Fin (2 * b) → ZMod p) × ZMod p

/-- The moments alone. -/
def moments (p b : ℕ) (x : Fin n → ℤ) : Fin (2 * b) → ZMod p := fun j => moment p x j.val

/-- The sketch `sk_{b,ξ}(x)`. -/
def sk (p b : ℕ) (ξ : ZMod p) (x : Fin n → ℤ) : Measurements p b :=
  (moments p b x, fingerprint p ξ x)

/-- `y` is a signed vector of support at most `b` that agrees with the moments `m`. -/
def IsCandidate (p b : ℕ) (m : Fin (2 * b) → ZMod p) (y : Fin n → ℤ) : Prop :=
  IsSigned y ∧ (supp y).card ≤ b ∧ moments p b y = m

open Classical in
/-- A candidate for the moments `m`, if there is one. No seed is used. -/
noncomputable def candidate (n p b : ℕ) (m : Fin (2 * b) → ZMod p) : Option (Fin n → ℤ) :=
  if h : ∃ y : Fin n → ℤ, IsCandidate p b m y then some h.choose else none

open Classical in
/-- The decoder: the candidate, accepted exactly when its fingerprint agrees. `none` is a rejection. -/
noncomputable def decode (n p b : ℕ) (ξ : ZMod p) (meas : Measurements p b) : Option (Fin n → ℤ) :=
  (candidate n p b meas.1).bind fun y => if fingerprint p ξ y = meas.2 then some y else none

/-- The number of bits of a sketch and its seed: `2b + 2` field elements of `⌈log₂ p⌉` bits. -/
def sketchBits (b p : ℕ) : ℕ := (2 * b + 2) * Nat.clog 2 p

/-- The input of the decoding program: `n`, `b`, `p`, the seed, the moments, the fingerprint. -/
def decoderInput (n b p : ℕ) [NeZero p] (ξ : ZMod p) (meas : Measurements p b) : List ℕ :=
  [n, b, p, ξ.val] ++ (List.finRange (2 * b)).map (fun j => (meas.1 j).val) ++ [meas.2.val]

/-- The output of the decoding program: `0` for a rejection; `1` and then `y_u + 1 ∈ {0,1,2}` for each
coordinate on accepting `y`. -/
def decodeOutput (n : ℕ) : Option (Fin n → ℤ) → List ℕ
  | none => [0]
  | some y => 1 :: (List.finRange n).map fun u => (y u + 1).toNat

end StreamColour


