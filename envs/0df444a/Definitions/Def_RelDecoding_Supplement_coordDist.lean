-- Prove2me | Definitions.Def_RelDecoding_Supplement_coordDist
-- name    : RelDecoding_Supplement_coordDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:11:35.891121+00:00
-- url     : https://prove2.me/theorems/317c33c3-1313-4677-9203-2cb0f0b1d1e0
-- title:
--   Coordinate distances $d_{A\to B}=\min\{|c|:c\in K_B\setminus K_A\}$ and $d_B=\min\{|c|:0\ne c\in K_B\}$
-- statement:
--   Let $K_A\subseteq K^s$ and $K_B\subseteq K^s$ be subspaces (relation codes) and write $|c|$ for the Hamming weight of $c\in K^s$, the number of its nonzero coordinates.
--
--   1. The **coordinate relative distance** is
--   $$d_{A\to B}=\min\{|c|:\ c\in K_B\setminus K_A\}.$$
--   2. The **ordinary distance** of the target relation code is
--   $$d_B=\min\{|c|:\ 0\neq c\in K_B\}.$$
--
--   Both take values in $\mathbb N_0\cup\{+\infty\}$ with the empty minimum equal to $+\infty$; in particular $K_A=K_B$ gives $d_{A\to B}=+\infty$ (eqs. (13), (18), (88), (93)). For Pauli sources $d_{A\to B}$ is the coordinate formula for the intrinsic relative distance, and $d_B$ is the distance governing ordinary (relation-free) decoding.
--
--   **Formalization Note** Values lie in `ℕ∞` and `sInf ∅ = ⊤`; `hammingNorm` is Mathlib's Hamming weight.
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), eq. (13), p.9; eq. (18), p.9; eq. (88), p.24; eq. (93), p.24 (pdf_pages 9, 24)

import Mathlib

set_option autoImplicit false

namespace RelDecoding.Supplement

/-- The **coordinate relative distance** `d_{A→B} := min{|c| : c ∈ K_B \ K_A}`, with `|c|` the
Hamming weight and the empty minimum `+∞` (so `K_A = K_B` gives `d_{A→B} = +∞`). Shang, Stilck
França, *From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via
Relative Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…), eq. (13), p.9, and eq. (88),
p.24.

**Formalization Note.** The value lies in `ℕ∞` and `sInf ∅ = ⊤`. `hammingNorm c` is the number of
nonzero coordinates of `c`. The kernels are given as subspaces of `K^s`. -/
noncomputable def coordDist {K : Type*} [Field K] [DecidableEq K] {s : ℕ}
    (KA KB : Submodule K (Fin s → K)) : ℕ∞ :=
  sInf ((fun c : Fin s → K => (hammingNorm c : ℕ∞)) '' ((KB : Set (Fin s → K)) \ KA))

/-- The **ordinary distance** of the target relation code `d_B := min{|c| : 0 ≠ c ∈ K_B}`, with
the empty minimum `+∞`. Shang, Stilck França, arXiv:2609.35101 (held version, sha256 d2be7859…),
eq. (18), p.9, and eq. (93), p.24.

**Formalization Note.** The value lies in `ℕ∞` and `sInf ∅ = ⊤`. -/
noncomputable def ordDist {K : Type*} [Field K] [DecidableEq K] {s : ℕ}
    (KB : Submodule K (Fin s → K)) : ℕ∞ :=
  sInf ((fun c : Fin s → K => (hammingNorm c : ℕ∞)) '' {c | c ∈ KB ∧ c ≠ 0})

end RelDecoding.Supplement


