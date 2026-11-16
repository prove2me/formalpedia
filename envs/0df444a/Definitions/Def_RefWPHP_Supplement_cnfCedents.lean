-- Prove2me | Definitions.Def_RefWPHP_Supplement_cnfCedents
-- name    : RefWPHP_Supplement_cnfCedents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:23:49.421385+00:00
-- url     : https://prove2.me/theorems/336b8a94-0e57-47f5-8bba-ea6e854f2d2a
-- title:
--   A CNF formula as a set of cedents, and its minimum PK$_d$ refutation size $\mathrm{size}_{\mathrm{PK}_d}(\varphi)$
-- statement:
--   For a CNF formula $\varphi = C_1 \wedge \dots \wedge C_m$ over $x_1, \dots, x_n$, the cedents of $\varphi$ are the clauses $C_A$, each written as the cedent of its literals; "PK refutes $\varphi$" means that PK refutes this set of cedents. The **minimum refutation size** $\mathrm{size}_{\mathrm{PK}_d}(\varphi)$ is the least size of a $\mathrm{PK}_d$-refutation of the cedents of $\varphi$; it is defined when $\varphi$ is unsatisfiable.
--
--   These enter the definition of automatability (§2.1.4) used in Theorem 5.1.
--
--   **Formalization Note** A clause is a set of literals, so its cedent may list them in any order: every permutation of the clause's literals is a cedent of $\varphi$ (a single order fixed by `Finset.toList` is not computable from the clause, and an automating algorithm could not be asked to reproduce it). Size is the base `derivSize`, and the minimum is an `sInf` over the sizes of refutations; the set is nonempty when $\varphi$ is unsatisfiable, since $\mathrm{PK}_0$ is complete for CNFs.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, p.15 (PDF p.17); §2.1.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_LayeredRef

namespace RefWPHP

namespace Supplement

open PKFormula

/-- The literal `(i, true) = x_i` as the formula `pos i`, and `(i, false) = ¬x_i` as `neg i`. -/
def litFormula {n : ℕ} (ℓ : Lit n) : PKFormula (Fin n) :=
  if ℓ.2 then pos ℓ.1 else neg ℓ.1

/-- A CNF formula as a set of cedents, N. Arteche, *Resolution Lower Bounds versus the Weak
Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, p.15
(PDF 17): "For a CNF formula `φ`, we consider its representation as a conjunction of disjunctions,
and collect these into a set `Φ`; we then write `PK ⊢ ¬φ` to indicate that PK refutes `Φ`". Each
clause `C_A` becomes the cedent of its literals.

**Formalization Note.** A clause is a set of literals, so its cedent is the list of its literals
in **any** order: every permutation of `(φ A).toList.map litFormula` is a cedent of `φ`. (A single
fixed order chosen by `Finset.toList` is not computable from the clause, so an automating machine
could not be required to reproduce it; with every order allowed, an algorithm may list the literals
as it reads them. The orders differ by one weakening step, `PKStep.weak`.) -/
noncomputable def cnfCedents {n m : ℕ} (φ : Fin m → Finset (Lit n)) : Set (Cedent (Fin n)) :=
  {Γ | ∃ A : Fin m, Γ.Perm ((φ A).toList.map litFormula)}

/-- `size_{PK_d}(φ)` (p.17, PDF 19): the minimum size (`derivSize`) of a `PK_d`-refutation of the
cedents of `φ`. The set is nonempty when `φ` is unsatisfiable. -/
noncomputable def pkSize {n m : ℕ} (d : ℕ) (φ : Fin m → Finset (Lit n)) : ℕ :=
  sInf {T | ∃ ρ : List (Cedent (Fin n)), IsPKRefutation d (cnfCedents φ) ρ ∧ derivSize ρ = T}

end Supplement

end RefWPHP


