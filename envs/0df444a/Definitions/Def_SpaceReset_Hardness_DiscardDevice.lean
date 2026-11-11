-- Prove2me | Definitions.Def_SpaceReset_Hardness_DiscardDevice
-- name    : SpaceReset_Hardness_DiscardDevice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:01.84698+00:00
-- url     : https://prove2.me/theorems/66634f67-28df-4c53-9a53-edbebd813605
-- title:
--   Online circuit with a discard budget (Definition 4)
-- statement:
--   **Definition 4.** Let $q,g$ be nonnegative integers. An online circuit with memory budget $q$ and discard budget $g$ receives a qubit at each slot, applies a quantum operation to it and a private memory, and returns the qubit before the next slot. The memory has dimension at most $2^q$ and counts every retained private classical or quantum record; its initial state $\sigma$ is independent of the user and may be mixed. Each slot operation is realized with fresh pure ancillas, a unitary and discarded systems; equivalently by an isometry
--   $$V_j:\ \mathrm{carrier}\otimes M\to\mathrm{carrier}\otimes M\otimes E_j$$
--   followed by discarding $E_j$, with
--   $$\prod_{j=1}^n\dim E_j\le 2^g .$$
--   Discarded systems are never accessed again. The initial-rank budget $h$ requires $\operatorname{rank}\sigma\le 2^h$; pure initialization requires $\operatorname{rank}\sigma=1$.
--
--   This is the operation model of the space–discard and initial-rank frontiers (Theorems 1 and 8), whose lower bounds hold against arbitrary CPTP slot operations, intermediate measurements, resets and classical control encoded in the counted memory.
--
--   **Formalization Note** One memory type $M$ with $|M|\le 2^q$ is used at every cut; a smaller memory at some cut embeds into it isometrically without extra discard.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), Definition 4, p. 12; §1.5.1, p. 6; §2.4, p. 16; §2.5, p. 20

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Quantum

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026), Definition 4 (Online circuit with a
discard budget), p. 12, with the resource conventions of §1.5.1 (p. 6), §2.4 (p. 16) and §2.5
(p. 20).

At each slot the device receives a qubit, applies a quantum operation to it and its private
memory, and returns the qubit before the next slot. The memory has dimension at most `2^q` and
counts every retained private classical or quantum record. Its initial state is independent of
the user and may be mixed. Each slot operation is realized with fresh pure ancillas, a unitary and
discarded systems; equivalently by a Stinespring isometry `V_j : carrier ⊗ M → carrier ⊗ M ⊗ E_j`
followed by discarding `E_j`. The tensor product of all discarded spaces has dimension at most
`2^g`. Discarded systems are never accessed again.

**Formalization Note.** One memory type `M` with `|M| ≤ 2^q` serves at every cut (a smaller
memory at some cut embeds isometrically, with no extra discard). Arbitrary CPTP operations,
intermediate measurements, resets and classical control within the counted memory are all
covered by the isometries `V_j`. The initial-rank budget `h` and pure initialization are
predicates on `σ`, stated where they are used.
-/

open Matrix

/-- Definition 4: an online circuit with `n` slots, memory budget `q` and discard budget `g`. -/
structure DiscardDevice (n q g : ℕ) where
  M : Type
  [fM : Fintype M]
  [dM : DecidableEq M]
  card_le : Fintype.card M ≤ 2 ^ q
  σ : Matrix M M ℂ
  σ_density : IsDensity σ
  E : Fin n → Type
  [fE : ∀ j, Fintype (E j)]
  [dE : ∀ j, DecidableEq (E j)]
  V : (j : Fin n) → Matrix ((Bool × M) × E j) (Bool × M) ℂ
  isometry : ∀ j, (V j)ᴴ * V j = 1
  discard_le : ∏ j, Fintype.card (E j) ≤ 2 ^ g

attribute [instance] DiscardDevice.fM DiscardDevice.dM DiscardDevice.fE DiscardDevice.dE

/-- Slot `j`'s operation `ρ ↦ Tr_{E_j}(V_j ρ V_j†)`. -/
def DiscardDevice.slot {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n)
    (ρ : Matrix (Bool × D.M) (Bool × D.M) ℂ) : Matrix (Bool × D.M) (Bool × D.M) ℂ :=
  ptraceRight (D.V j * ρ * (D.V j)ᴴ)

/-- The online process of a Definition 4 device. -/
def DiscardDevice.toProcess {n q g : ℕ} (D : DiscardDevice n q g) : Process n where
  M := D.M
  σ := D.σ
  Φ := D.slot

/-- The initial memory state has rank at most `2^h` (the initial-rank budget, p. 6, p. 20). -/
def DiscardDevice.RankLE {n q g : ℕ} (D : DiscardDevice n q g) (h : ℕ) : Prop :=
  D.σ.rank ≤ 2 ^ h

/-- Pure initialization: the initial memory state has rank one (pp. 16–17). -/
def DiscardDevice.PureInit {n q g : ℕ} (D : DiscardDevice n q g) : Prop :=
  D.σ.rank = 1

end SpaceReset.Hardness


