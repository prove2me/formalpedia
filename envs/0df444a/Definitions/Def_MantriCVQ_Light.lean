-- Prove2me | Definitions.Def_MantriCVQ_Light
-- name    : MantriCVQ_Light
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:48.174751+00:00
-- url     : https://prove2.me/theorems/2099e719-87b3-41ea-b338-7de8ae85730b
-- title:
--   Light blocks of a term
-- statement:
--   For height-one blocks of dimension $m$ and a threshold $t\ge0$, a block is **light** for a term if the term contains the block's free leaf (the data entry at its secret) and at most $t$ code literals of that block. The set of light blocks depends on the secrets. The event of Theorem 6.1 is that a DNF accepts $\rho(z)$ and at least $\ell$ blocks are light for its first satisfied term.
--
--   **Formalization Note** Code literals are counted without repetition, as after the paper's normalization.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §6.1, p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_MantriCVQ_Forest
import Definitions.Def_MantriCVQ_firstSatTerm
import Definitions.Def_SamplingAC0_DNF

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

open Classical in
/-- Block `i` is light for the term `T` when its secret is `S` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §6.1, p. 23 (PDF p. 25): "a block is light for a term if the term contains the
block's free leaf and at most `t` code literals in that block"). The blocks have height one, so the
free leaf is the data entry at `S`.

**Formalization Note** Code literals are counted without repetition, as after the paper's
normalization. -/
def IsLight {ι : Type} {m : ℕ} (t : ℕ) (T : Term (ι × Addr [m])) (i : ι) (S : Bits m) : Prop :=
  (∃ b : Bool, (((i, (true, S, ())) : ι × Addr [m]), b) ∈ T) ∧
    (T.filter fun l => decide (l.1.1 = i ∧ l.1.2.1 = false)).toFinset.card ≤ t

open Classical in
/-- The blocks light for the term `T` under the seeds `s`. -/
noncomputable def lightBlocks {ι : Type} [Fintype ι] {m : ℕ} (t : ℕ) (T : Term (ι × Addr [m]))
    (s : ι → Seed [m]) : Finset ι :=
  Finset.univ.filter fun i => IsLight t T i (s i).1.1

/-- The event of Theorem 6.1 (§6.1, p. 23): `Φ` accepts `ρ(z)` and at least `ℓ` blocks are light for
the first satisfied term. -/
def lightEvent (C : (m : ℕ) → Bits m → Bits m → Bool) {ι : Type} [Fintype ι] {m : ℕ} (t ℓ : ℕ)
    (Φ : DNF (ι × Addr [m])) (z : ι → Bool) (s : ι → Seed [m]) : Prop :=
  DNF.eval Φ (forestInput C [m] s z) = true ∧
    ∃ T, firstSatTerm Φ (forestInput C [m] s z) = some T ∧ ℓ ≤ (lightBlocks t T s).card

end MantriCVQ


