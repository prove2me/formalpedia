-- Prove2me | Definitions.Def_ChapterSirkCertifiedGap
-- name    : ChapterSirkCertifiedGap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T09:13:01.447101+00:00
-- url     : https://prove2.me/theorems/3a07d669-c4f9-4f01-bd14-ca97b63082d2
-- title:
--   `CONSOLIDATED_PLAN.md` §13.3 (T6, T7 and the nested-selection lemma), `MASS_GAP_CERTIFIED.md` §3.3/§3.4. With the finite ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkCertifiedGap`, source chapter `BookProof/ChapterSirkCertifiedGap.lean`).
--
--   `CONSOLIDATED_PLAN.md` §13.3 (T6, T7 and the nested-selection lemma), `MASS_GAP_CERTIFIED.md` §3.3/§3.4. With the finite-precision layer of `ChapterSirkFinitePrecision` in place, this chapter proves the certified-gap theorem for the **truncated** (Krylov/Galerkin) Hamiltonian `H_m` — the object the kernel diagonalises — together with the stopping rule that makes a computation a proof.
--
--   **Object of record (no lattice).** The Hamiltonian of the mass-gap formalization is the 3D **gauge-fixed nested-Fock QYM Hamiltonian** `qcd_ym_hamiltonian(g)` (`H_final = ½π² + ½B²`), all numerics running the SIRK–Hashimoto algorithm. The abstract theorem below is stated for *any* symmetric involution commuting with `H` — on the gauge-fixed Hamiltonian of record that involution is the reflection `R : (A₀, A₁) → (−A₁, −A₀)`, an exact `Z₂` for all `g` (verified numerically to `1e-16`); the occupation parity of the lattice-era fixture is not a symmetry at `g > 0` and is retained only as a historical instance.
--
--   **Honesty boundary (fixed in `CONSOLIDATED_PLAN.md` §13.1).** Every statement here is about the finite-dimensional operator. The continuum Millennium claim needs a gap-preserving norm-resolvent convergence of the truncation family; that leg is *not* proved here and is not assumed anywhere.
--
--   The sector involution `P` is an exact symmetry: it is a symmetric involution commuting with `H` (for the gauge-fixed QYM Hamiltonian of record: the reflection `R`), so the space splits into the two sector eigenspaces `paritySector P (±1)`, each `H`-invariant. The observable of §3.3 is the difference of the two *sector ground energies* — the infimum of the Rayleigh quotient over unit vectors of a sector, `sectorGround`. The certificate delivers, for each sector, a computed Ritz value `θˢ` and a width `δˢ`; the theorem `certified_parity_gap` turns the two enclosures into a lower bound for the gap, and `certified_parity_gap_pos` into a *positive* gap once the certified intervals separate.
--
--   * `paritySector`, `mem_paritySector`, `paritySector_invariant`, `sectorRestrict`, `sectorRestrict_isSymmetric` — **the parity split is exact**: the sectors are invariant subspaces and the restricted operators are symmetric. * `sectorRayleighSet`, `sectorGround` — the sector ground energy, with `sectorRayleighSet_bddBelow`, the unconditional Ritz upper bound `sectorGround_le_rayleigh`, the lower bound `le_sectorGround`, and the spectral identification `sectorGround_eq_inf_eigenvalues`. * **T6** `certified_parity_gap`: `λᵒ₀ − λᵉ₀ ≥ θᵒ₀ − θᵉ₀ − (δᵒ + δᵉ)`, with `certified_parity_gap_pos` (a proof-carrying *positive* gap for the truncated operator) and `certified_parity_gap_of_data`, which assembles the bound from the raw certificate data (a computed even-sector Ritz vector and a certified odd-sector lower bound), and `certified_parity_gap_strong_coupling`, the same bound written against the analytic strong-coupling value `g²/2` with the excluded `O(g⁴)` magnetic correction kept explicit. * `sectorGround_ge_temple` — Temple's inequality inside a sector: the honest route to the odd-sector lower bound that T6 consumes. * **The nested-selection lemma** `resolvent_commutes_parity` / `resolvent_mapsTo_paritySector`: the resolvent of the operator restricted to a sector is the resolvent of the restriction — the block fact behind the two-level (nested Fock) selection. * **T7** the stopping rule: `certifiedGap` and `certifiedGap_tendsto`, `certifiedGap_eventually_pos` (completeness: if the true sector gap is positive the certificate eventually detects it) and `certifiedGap_sound` (soundness: a positive certified value *proves* a positive gap, and nothing is ever claimed that was not certified).
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertifiedGap.lean

import Definitions.Def_ChapterSirkFinitePrecision
import Mathlib

import Mathlib

/-!
# Chapter SirkCertifiedGap — the certified mass gap of the truncated Hamiltonian (T6, T7)

`CONSOLIDATED_PLAN.md` §13.3 (T6, T7 and the nested-selection lemma),
`MASS_GAP_CERTIFIED.md` §3.3/§3.4.  With the finite-precision layer of
`ChapterSirkFinitePrecision` in place, this chapter proves the certified-gap theorem
for the **truncated** (Krylov/Galerkin) Hamiltonian `H_m` — the object the kernel
diagonalises — together with the stopping rule that makes a computation a proof.

**Object of record (no lattice).**  The Hamiltonian of the mass-gap formalization
is the 3D **gauge-fixed nested-Fock QYM Hamiltonian** `qcd_ym_hamiltonian(g)`
(`H_final = ½π² + ½B²`), all numerics running the SIRK–Hashimoto algorithm.  The
abstract theorem below is stated for *any* symmetric involution commuting with `H`
— on the gauge-fixed Hamiltonian of record that involution is the reflection
`R : (A₀, A₁) → (−A₁, −A₀)`, an exact `Z₂` for all `g` (verified numerically to
`1e-16`); the occupation parity of the lattice-era fixture is not a symmetry at
`g > 0` and is retained only as a historical instance.

**Honesty boundary (fixed in `CONSOLIDATED_PLAN.md` §13.1).**  Every statement here
is about the finite-dimensional operator.  The continuum Millennium claim needs a
gap-preserving norm-resolvent convergence of the truncation family; that leg is *not*
proved here and is not assumed anywhere.

## The structure of the argument

The sector involution `P` is an exact symmetry: it is a symmetric involution commuting
with `H` (for the gauge-fixed QYM Hamiltonian of record: the reflection `R`), so the space
splits into the two sector eigenspaces `paritySector P (±1)`, each
`H`-invariant.  The observable of §3.3 is the difference of the two *sector ground
energies* — the infimum of the Rayleigh quotient over unit vectors of a sector,
`sectorGround`.  The certificate delivers, for each sector, a computed Ritz value `θˢ`
and a width `δˢ`; the theorem `certified_parity_gap` turns the two enclosures into a
lower bound for the gap, and `certified_parity_gap_pos` into a *positive* gap once the
certified intervals separate.

## Deliverables

* `paritySector`, `mem_paritySector`, `paritySector_invariant`, `sectorRestrict`,
  `sectorRestrict_isSymmetric` — **the parity split is exact**: the sectors are
  invariant subspaces and the restricted operators are symmetric.
* `sectorRayleighSet`, `sectorGround` — the sector ground energy, with
  `sectorRayleighSet_bddBelow`, the unconditional Ritz upper bound
  `sectorGround_le_rayleigh`, the lower bound `le_sectorGround`, and the spectral
  identification `sectorGround_eq_inf_eigenvalues`.
* **T6** `certified_parity_gap`: `λᵒ₀ − λᵉ₀ ≥ θᵒ₀ − θᵉ₀ − (δᵒ + δᵉ)`, with
  `certified_parity_gap_pos` (a proof-carrying *positive* gap for the truncated
  operator) and `certified_parity_gap_of_data`, which assembles the bound from the
  raw certificate data (a computed even-sector Ritz vector and a certified
  odd-sector lower bound), and `certified_parity_gap_strong_coupling`, the same bound
  written against the analytic strong-coupling value `g²/2` with the excluded `O(g⁴)`
  magnetic correction kept explicit.
* `sectorGround_ge_temple` — Temple's inequality inside a sector: the honest route to
  the odd-sector lower bound that T6 consumes.
* **The nested-selection lemma** `resolvent_commutes_parity` /
  `resolvent_mapsTo_paritySector`: the resolvent of the operator restricted to a
  sector is the resolvent of the restriction — the block fact behind the two-level
  (nested Fock) selection.
* **T7** the stopping rule: `certifiedGap` and `certifiedGap_tendsto`,
  `certifiedGap_eventually_pos` (completeness: if the true sector gap is positive the
  certificate eventually detects it) and `certifiedGap_sound` (soundness: a positive
  certified value *proves* a positive gap, and nothing is ever claimed that was not
  certified).

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.SirkCertifiedGap

open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## 1. The parity sectors: the split is exact -/

/-- The `s`-eigenspace of the sector involution `P` (`s = ±1`; on the gauge-fixed
QYM Hamiltonian of record, `P` is the reflection `R: (A₀,A₁) → (−A₁,−A₀)`). -/
def paritySector (P : E →ₗ[ℂ] E) (s : ℝ) : Submodule ℂ E where
  carrier := {x | P x = (s : ℂ) • x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb, smul_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hx, smul_comm]

omit [FiniteDimensional ℂ E] in
@[simp]
theorem mem_paritySector {P : E →ₗ[ℂ] E} {s : ℝ} {x : E} :
    x ∈ paritySector P s ↔ P x = (s : ℂ) • x := Iff.rfl

omit [FiniteDimensional ℂ E] in
/-- **The parity split is exact**: a sector is invariant under any operator commuting
with the parity. -/
theorem paritySector_invariant {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x)) :
    ∀ x ∈ paritySector P s, T x ∈ paritySector P s := by
  intro x hx
  rw [mem_paritySector] at hx ⊢
  rw [← hcomm, hx, map_smul]

/-- The restriction of `T` to a parity sector. -/
def sectorRestrict (T P : E →ₗ[ℂ] E) (s : ℝ) (hcomm : ∀ x, T (P x) = P (T x)) :
    paritySector P s →ₗ[ℂ] paritySector P s :=
  T.restrict (paritySector_invariant hcomm)







/-! ## 2. The sector ground energy -/

/-- The Rayleigh quotients of the unit vectors of the sector `s`. -/
def sectorRayleighSet (T P : E →ₗ[ℂ] E) (s : ℝ) : Set ℝ :=
  {r | ∃ x : E, ‖x‖ = 1 ∧ x ∈ paritySector P s ∧ r = rayleigh T x}

/-- The sector ground energy `λˢ₀`: the infimum of the Rayleigh quotient over the unit
vectors of the sector.  This is the quantity the SIRK sector solve approximates from
above. -/
def sectorGround (T P : E →ₗ[ℂ] E) (s : ℝ) : ℝ := sInf (sectorRayleighSet T P s)











/-! ## 3. T6 — the certified-gap theorem -/











/-! ## 4. The nested-selection lemma: resolvents respect the sectors -/





/-! ## 5. T7 — the observable and the stopping rule -/

/-- The certified lower bound delivered at Krylov dimension `m`:
`g(m) = θᵒ₀(m) − θᵉ₀(m) − (δᵒ(m) + δᵉ(m))`. -/
def certifiedGap (thetaE thetaO deltaE deltaO : ℕ → ℝ) (m : ℕ) : ℝ :=
  thetaO m - thetaE m - (deltaO m + deltaE m)







/-! ## 6. Instantiating T6 from an emitted certificate

The kernel's certificate emitter delivers, per parity sector, a value `θ` and a width
`δ = residual + roundoff + enclosure`.  What the Lean side consumes is only the pair
(sector Ritz difference, assembled width) — no floating-point value is trusted, and no
numerical claim is *verified* here: the numbers below are the emitted data, and the
theorems are conditional on the enclosures the certificate asserts. -/

/-- The two numbers a gap certificate delivers: the measured sector ground-Ritz
difference `θᵒ₀ − θᵉ₀` and the assembled width `δᵒ + δᵉ` of `MASS_GAP_CERTIFIED.md`
§4.4. -/
structure GapCertificate where
  /-- The measured sector ground-Ritz difference `θᵒ₀ − θᵉ₀`. -/
  gap : ℝ
  /-- The assembled certified width `δᵒ + δᵉ`. -/
  width : ℝ
  /-- Widths are nonnegative. -/
  width_nonneg : 0 ≤ width

/-- The certified lower bound carried by a certificate. -/
def GapCertificate.lower (c : GapCertificate) : ℝ := c.gap - c.width





/-- The certificate emitted by the kernel for the `g = 2`, `m = 4` run of the
lattice-era cross-benchmark (`yang_mills_lattice`) — retained as a historical
fixture; the object of record for the mass gap is the gauge-fixed QYM
Hamiltonian's reflection-sector certificate (`docs/MASS_GAP_SPEC.md`).
run (`MASS_GAP_CERTIFIED.md`, `CONSOLIDATED_PLAN.md` §13.2): measured sector gap
`1.9875`, assembled width `δᵒ + δᵉ = 0.0555`.  These two numbers are *data* transcribed
from the emitted NDJSON; Lean checks only what follows from them. -/
def qcdG2M4 : GapCertificate where
  gap := 1.9875
  width := 0.0555
  width_nonneg := by norm_num







end BookProof.SirkCertifiedGap


