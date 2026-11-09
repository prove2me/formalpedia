-- Prove2me | Definitions.Def_RestrictedDec_qCoord
-- name    : RestrictedDec_qCoord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:00.765714+00:00
-- url     : https://prove2.me/theorems/4183824c-4d78-40d7-b5e1-26b3a35842a2
-- title:
--   Fixed-coordinate observation $q_S$
-- statement:
--   Let $S_\lambda\subseteq[n(\lambda)]=\{1,\dots,n(\lambda)\}$ be a public set of bit positions. For $S_\lambda\neq\emptyset$ the **fixed-coordinate observation** is
--
--   $$q_S(m)=(0,\ m|_S)\quad(m\in\{0,1\}^n),\qquad q_S(\perp)=(1,\ 0^{|S|}),$$
--
--   where $m|_S$ lists the bits of $m$ at the positions of $S$ in increasing order. For $S_\lambda=\emptyset$, $q_\emptyset$ is constant on all decryption outputs. The leading bit distinguishes decryption failure from a valid message.
--
--   This is the observation family of the mission: Corollary 2 compares $\mathrm{Sec}^{ad}(q_S)$ with $\mathrm{Sec}^{na}(q_T)$.
--
--   **Formalization Note** The pair $(\beta,z)$ is the string $\beta z$; positions are numbered from $1$; $q_\emptyset$ is the empty string.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §1.2, p.9

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- `m|_S`: the bits of `m` at the positions of `S` (numbered from `1`), in increasing order of
position. -/
def restrictBits (S : Finset ℕ) (m : Str) : Str :=
  ((List.range m.length).zip m).filterMap fun p => if p.1 + 1 ∈ S then some p.2 else none

/-- The **fixed-coordinate observation** `q_S` of a sequence of coordinate sets `S_λ ⊆ [n(λ)]`:
for `S_λ ≠ ∅`,
`q_S(m) = (0, m|_S)` for a message `m ∈ {0,1}ⁿ` and `q_S(⊥) = (1, 0^{|S|})`;
for `S_λ = ∅`, `q_∅` is constant (the empty string) on all decryption outputs.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §1.2, p.9 ("For S ≠ ∅, define
qS(m) = (0, m|S) (m ∈ {0, 1}n), qS(⊥) = (1, 0|S|), where m|S lists the selected bits in increasing
order. For the empty set take q∅ to be constant on all decryption outputs.").

**Formalization Note.** Positions are `1, …, n` as printed; position `p` is list index `p − 1`.
The pair `(β, z)` is the string `β :: z`. On strings that are not messages of length `n(λ)` the
formula is applied as is; decryption never outputs them (`PKE.IsScheme`). -/
def qCoord (S : ℕ → Finset ℕ) (lam : ℕ) : Option Str → Str := fun x =>
  if S lam = ∅ then []
  else
    match x with
    | none => true :: List.replicate (S lam).card false
    | some m => false :: restrictBits (S lam) m

end RestrictedDec


