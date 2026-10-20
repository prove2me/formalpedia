-- Prove2me | Definitions.Def_HardyLittlewood_constellation
-- name    : HardyLittlewood_constellation
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T21:30:38.594814+00:00
-- url     : https://prove2.me/theorems/cc9a3805-fe84-496e-99e9-56ff3a50a0b2
-- title:
--   Prime constellations, admissibility, and residue counting
-- statement:
--   The arena of the Hardy–Littlewood conjectures. A prime constellation with offsets m = (m₀, m₁, ..., m_k) at the base point p is the tuple of primes (p, p + 2m₁, ..., p + 2m_k): m₀ is 0, every other offset is positive, and every entry p + 2m_i is prime. The constellation is admissible when its entries do not form a complete set of residue classes modulo any prime: for every prime q, the residues of the entries p + 2m_i modulo q fail to cover all of Z/q. The doubled-offset tuple itself is admissible when for no prime q do the residues of 2m_i cover all of Z/q — the parameter-independent form, equivalent to the constellation-level condition because translation by p permutes the residue classes. The residue counter w(q; m) returns the number of distinct residues occupied by the offsets m₀, ..., m_k modulo q, the local data from which the singular series is built.
-- source:
--   Formal Conjectures (2025), HardyLittlewood.lean, definitions IsPrimeConstellation, IsAdmissiblePrimeConstellation, and Nat.numResidues

import Mathlib

namespace HardyLittlewood

/-- A prime constellation with offset tuple m at the base point p: the entries
(p, p + 2·m₀, ..., p + 2·m_k) satisfy m₀ = 0, every other offset is positive,
and every entry is prime. The gaps between constellation points are the even
numbers 2·m i (the source's convention). -/
def IsPrimeConstellation {k : ℕ} (m : Fin k.succ → ℕ) (p : ℕ) : Prop :=
  m 0 = 0 ∧ (∀ i : Fin k.succ, i ≠ 0 → 0 < m i) ∧
    ∀ i : Fin k.succ, (p + 2 * m i).Prime

/-- The constellation is admissible: its entries do not form a complete set
of residue classes with respect to any prime — for every prime q, the
residues of p + 2·m i modulo q do not cover all of ZMod q. -/
def IsAdmissiblePrimeConstellation {k : ℕ} (m : Fin k.succ → ℕ) (p : ℕ) : Prop :=
  IsPrimeConstellation m p ∧
    ∀ q : ℕ, q.Prime → ¬ Function.Surjective
      (fun i : Fin k.succ => (p + 2 * m i : ZMod q))

/-- The tuple of doubled offsets is admissible: for no prime q do the
residues of 2·m i modulo q cover all of ZMod q. Residue coverage is invariant
under translation by the base point, so this is the parameter-independent
form of admissibility. -/
def IsAdmissibleTuple {k : ℕ} (m : Fin k.succ → ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → ¬ Function.Surjective
    (fun i : Fin k.succ => (2 * m i : ZMod q))

/-- The number w(q; m) of distinct residues occupied by the offsets
m₀, ..., m_k modulo q. -/
noncomputable def numResidues (q : ℕ) {k : ℕ} (m : Fin k.succ → ℕ) : ℕ :=
  (Set.range (fun i : Fin k.succ => (m i : ZMod q))).ncard

end HardyLittlewood


