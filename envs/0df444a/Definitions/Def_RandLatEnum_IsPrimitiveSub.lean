-- Prove2me | Definitions.Def_RandLatEnum_IsPrimitiveSub
-- name    : RandLatEnum_IsPrimitiveSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:07.241368+00:00
-- url     : https://prove2.me/theorems/fc41d284-a576-4edc-993a-44e517db4888
-- title:
--   Primitive sublattice: $M=L\cap\mathrm{span}_{\mathbb R}M$
-- statement:
--   A sublattice $M$ of a lattice $L$ is **primitive** if a basis of $M$ can be extended to a basis of $L$; equivalently,
--   $$
--   M=L\cap\mathrm{span}_{\mathbb R}M .
--   $$
--   The prefixes $M_k=\mathbb Zb_1+\dots+\mathbb Zb_k$ of any basis of $L$ are primitive and form a nested chain, which is what the area rule counts.
--
--   **Formalization Note** The page's second characterization: $M\subseteq L$, and every vector of $L$ in the real span of $M$ lies in $M$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14

import Mathlib

namespace RandLatEnum

/-- `M` is a primitive sublattice of `L` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14: "It is primitive if a basis of M can be
extended to a basis of L. Equivalently, it is primitive if M = L ∩ span_R M"): `M ⊆ L` and every
vector of `L` in the real span of `M` lies in `M`.

**Formalization Note.** The page's second (equivalent) characterization `M = L ∩ span_ℝ M`. -/
def IsPrimitiveSub {k : ℕ} (L M : Submodule ℤ (EuclideanSpace ℝ (Fin k))) : Prop :=
  M ≤ L ∧ ∀ v ∈ L, v ∈ Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin k))) → v ∈ M

end RandLatEnum


