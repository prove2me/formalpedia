-- Prove2me | Definitions.Def_RandLatEnum_dualBasis
-- name    : RandLatEnum_dualBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:22.08417+00:00
-- url     : https://prove2.me/theorems/9b19fcfe-31c5-4961-aae5-26b5298939c6
-- title:
--   Dual basis $b^\vee_i=\sum_j(G^{-1})_{ij}b_j$
-- statement:
--   For a basis $b=(b_1,\dots,b_m)$ of a lattice $L$ with Gram matrix $G_{ij}=\langle b_i,b_j\rangle$, the **dual basis** is
--   $$
--   b^\vee_i=\sum_{j=1}^{m}(G^{-1})_{ij}\,b_j ,
--   $$
--   the unique family in $\mathrm{span}\,L$ with $\langle b^\vee_i,b_j\rangle=\delta_{ij}$. It is a basis of the dual lattice $L^*$, and the dual basis of $b^\vee$ is $b$.
--
--   Together with reversal it produces the reversed dual-HKZ bases used to reduce the left block in the proof of Theorem 1.5.
--
--   **Formalization Note** Used only for linearly independent $b$, where $G$ is invertible.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, p.19; §2.3, p.16

import Mathlib

namespace RandLatEnum

/-- The dual basis `b^∨` of a basis `b = (b_1, …, b_m)` of a lattice, in its span (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1,
p.19, "dualizing an HKZ basis of the dual lattice"; §2.3, p.16): `b^∨_i = Σ_j (G⁻¹)_{ij} b_j` with
the Gram matrix `G_{ij} = ⟨b_i, b_j⟩`, so that `⟨b^∨_i, b_j⟩ = δ_{ij}` and `b^∨` is a basis of
`L*` in `span L`.

**Formalization Note.** Used only for linearly independent `b`, where `G` is invertible (for a
singular `G` Lean's inverse is `0`). -/
noncomputable def dualBasis {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) :
    Fin m → EuclideanSpace ℝ (Fin k) :=
  fun i => ∑ j, ((Matrix.of fun p q : Fin m => inner ℝ (b p) (b q))⁻¹ i j) • b j

end RandLatEnum


