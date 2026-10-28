-- Prove2me | Definitions.Def_ChapterQgManifoldModeInstance
-- name    : ChapterQgManifoldModeInstance
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T09:39:59.503983+00:00
-- url     : https://prove2.me/theorems/157b0118-6448-402e-a713-f9adb05ae948
-- title:
--   The Lean 4 theorem `one_le_sigOf` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgManifoldModeInstance`, source chapter `BookProof/ChapterQgManifoldModeInstance.lean`): Chapter ChapterQgManifoldModeInstance
--
--   Generated def bundle for ChapterQgManifoldModeInstance. See BookProof/ChapterQgManifoldModeInstance.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgManifoldModeInstance.lean

import Definitions.Def_ChapterQgTimeStepping
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterStoneBridge
import Mathlib
import Theorems.Thm_BookProof_QgTruncationResolvent_qgOuterFock_truncation_flow_convergence
import Theorems.Thm_BookProof_QgTimeStepping_qgOuterFock_fullyDiscrete_convergence


/-!
# The quantum-gravity Hamiltonian on a general spatial manifold

The earlier mode instances of this project fix the spatial manifold to a periodic box, so
that the modes are the Fourier modes and the momenta run over `ℤ³`
(`BookProof.ChapterQgContinuumModeInstance`).  Nothing in the Faris–Lavine analysis needs
that: in the **vielbein variables** the gravitational field is a global orthonormal coframe,
i.e. a triple of one-forms on the spatial slice, and the whole construction only sees

* the spectrum of the Laplace-type operator that defines the mode energies, and
* the fact that the torsion self-interaction `½ Σ ‖d e^i‖²` is **diagonal** in a mode basis
  adapted to the Hodge decomposition — `δd` acts as `0` on the closed part and as the Hodge
  eigenvalue on the co-closed part — together with the elementary bound `λ_a ≤ μ_a`.

Both are available on *any* closed Riemannian three-manifold that carries a global
orthonormal frame (every closed orientable three-manifold does), with *any* spectrum: no
periodicity, no lattice, no flatness, no bound on the eigenvalue multiplicities, no
homogeneity.  This module packages exactly that geometric input as
`VielbeinSpectrum` and shows it satisfies all five Faris–Lavine Schur bounds, so the whole
chain — essential self-adjointness, the mode cutoff, and the fully discrete Crank–Nicolson
evolution — holds verbatim on a general manifold.

## What is proved

* `VielbeinSpectrum` — the geometric mode data on a general spatial manifold: mode energies
  `μ_a ≥ 0` (the Laplace-type spectrum), the diagonal torsion eigenvalues `0 ≤ λ_a ≤ μ_a`
  (Hodge), the finite coupling block of each mode and the trace weights `|tr_a| ≤ 1` through
  which the scalaron couples, with the two Schur bounds on the blocks.
* `manifoldModes` — the resulting `QgModeData`, with Faris–Lavine constant `K = 1 + |g|·W`.
* **`qgManifold_essentiallySelfAdjointOn`**, **`starobinsky_qgManifold_esa`** — the
  quantum-gravity Hamiltonian on the outer Fock space over a general spatial manifold, with
  the full exponential Einstein-frame Starobinsky wall and arbitrary coupling constant, is
  essentially self-adjoint.
* `energyWindow`, `energyWindow_exhausts` — the **spectral cutoff** `μ_a ≤ n`, the general
  manifold's replacement for the momentum cutoff of the box.
* **`starobinsky_qgManifold_cutoff_flow_convergence`** — the spectrally truncated flows
  converge to the exact flow, uniformly on compact time intervals.
* **`starobinsky_qgManifold_fullyDiscrete_convergence`** — the fully discrete statement:
  spectral cutoff *and* Crank–Nicolson time stepping converge to the exact quantum-gravity
  flow.
* `ofSpectrumSeq` — non-vacuity with an *arbitrary* non-negative eigenvalue sequence: the
  instance does not constrain the geometry of the manifold through its spectrum.

Honest boundary: the geometric input (parallelizability, the Hodge decomposition of the
one-form modes, finiteness of the coupling blocks) enters as the data of
`VielbeinSpectrum`; the Riemannian geometry that produces it on a given manifold is not
itself formalized here.  No spectral information about the Hamiltonian, no mass gap and no
claim beyond the flow convergence is made.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgManifoldModeInstance

open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgOuterFockCoreFL BookProof.QgTruncationResolvent
open BookProof.QgTimeStepping

noncomputable section

variable {ι : Type*}

/-! ## 1. The geometric mode data on a general spatial manifold -/

/-- **The vielbein mode spectrum of a general spatial manifold.**

`mu a` is the Laplace-type eigenvalue of the mode `a` (the mode energy is `σ_a = 1 + μ_a`);
`lam a` is the eigenvalue of the torsion form `δd` on that mode, which by the Hodge
decomposition is diagonal in this basis and bounded by `μ_a`; `block a` is the finite set of
modes the scalaron–vielbein coupling connects `a` to, and `tr a` is the trace weight of the
mode, through which the scalaron couples.  The two sums are the Schur bounds the
Faris–Lavine theorem needs; on the periodic box they hold with `W = 9`, on a general
manifold they hold whenever the coupling blocks are summable against the trace weights. -/
structure VielbeinSpectrum (ι : Type*) where
  /-- The Laplace-type eigenvalue of the mode. -/
  mu : ι → ℝ
  /-- The eigenvalues are non-negative. -/
  mu_nonneg : ∀ a, 0 ≤ mu a
  /-- The torsion (`δd`) eigenvalue of the mode. -/
  lam : ι → ℝ
  /-- Torsion eigenvalues are non-negative: `δd` is a positive operator. -/
  lam_nonneg : ∀ a, 0 ≤ lam a
  /-- Torsion eigenvalues are dominated by the Hodge eigenvalues. -/
  lam_le_mu : ∀ a, lam a ≤ mu a
  /-- The finite block of modes the scalaron coupling connects a mode to. -/
  block : ι → Finset ι
  /-- Blocks are symmetric. -/
  mem_block_comm : ∀ a b, b ∈ block a ↔ a ∈ block b
  /-- Every mode lies in its own block. -/
  self_mem_block : ∀ a, a ∈ block a
  /-- The trace weight of the mode. -/
  tr : ι → ℝ
  /-- The trace weights are normalized. -/
  abs_tr_le_one : ∀ a, |tr a| ≤ 1
  /-- The Schur constant of the coupling blocks. -/
  W : ℝ
  /-- The Schur constant is non-negative. -/
  W_nonneg : 0 ≤ W
  /-- Schur bound: the trace weights are summable across each block. -/
  tr_sum : ∀ a, ∑ b ∈ block a, |tr b| ≤ W
  /-- Schur bound for the commutator: the energy spread across a block, weighted by the
  trace weights, is bounded. -/
  tr_spread : ∀ a, ∑ b ∈ block a, |mu a - mu b| * |tr b| ≤ W

namespace VielbeinSpectrum

variable (S : VielbeinSpectrum ι)

/-- The mode energy `σ_a = 1 + μ_a`. -/
def sigOf (a : ι) : ℝ := 1 + S.mu a

theorem one_le_sigOf (a : ι) : 1 ≤ S.sigOf a := by
  have := S.mu_nonneg a
  simp only [sigOf]
  linarith

theorem lam_le_sigOf (a : ι) : S.lam a ≤ S.sigOf a := by
  have := S.lam_le_mu a
  simp only [sigOf]
  linarith

open Classical in
/-- **The vielbein self-interaction on a general manifold**: the torsion Gram matrix, which
the Hodge decomposition makes diagonal, with the `δd` eigenvalues on the diagonal. -/
def Amat (a b : ι) : ℂ := if a = b then ((S.lam a : ℝ) : ℂ) else 0

open Classical in
/-- **The scalaron–vielbein coupling on a general manifold** at coupling constant `g`: the
scalaron couples through the trace weights, inside the coupling blocks. -/
def Bmat (g : ℝ) (a b : ι) : ℂ :=
  if b ∈ S.block a then ((g * S.tr a * S.tr b : ℝ) : ℂ) else 0

theorem Amat_herm (a b : ι) : S.Amat b a = (starRingEnd ℂ) (S.Amat a b) := by
  classical
  by_cases h : a = b
  · subst h; simp [Amat, Complex.conj_ofReal]
  · simp [Amat, h, Ne.symm h]

theorem Bmat_herm (g : ℝ) (a b : ι) : S.Bmat g b a = (starRingEnd ℂ) (S.Bmat g a b) := by
  classical
  by_cases h : b ∈ S.block a
  · have h' : a ∈ S.block b := (S.mem_block_comm a b).mp h
    simp only [Bmat, if_pos h, if_pos h', Complex.conj_ofReal]
    norm_cast
    ring
  · have h' : a ∉ S.block b := fun hh => h ((S.mem_block_comm a b).mpr hh)
    simp [Bmat, h, h']

theorem norm_Amat_diag (a : ι) : ‖S.Amat a a‖ = S.lam a := by
  simp [Amat, abs_of_nonneg (S.lam_nonneg a)]

theorem Amat_off_diag {a b : ι} (h : a ≠ b) : S.Amat a b = 0 := by
  simp [Amat, h]

theorem norm_Bmat_le (g : ℝ) (a b : ι) : ‖S.Bmat g a b‖ ≤ |g| * |S.tr a| * |S.tr b| := by
  classical
  by_cases h : b ∈ S.block a
  · simp only [Bmat, if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact le_rfl
  · simp only [Bmat, if_neg h, norm_zero]
    positivity

/-- **The mode data of the quantum-gravity Hamiltonian on a general spatial manifold.** -/
def modes (g : ℝ) : QgModeData ι where
  sig := S.sigOf
  one_le_sig := S.one_le_sigOf
  A := S.Amat
  B := S.Bmat g
  nbr := S.block
  mem_nbr_comm := S.mem_block_comm
  A_off := by
    intro a b hb
    have hne : a ≠ b := by
      rintro rfl
      exact hb (S.self_mem_block a)
    exact S.Amat_off_diag hne
  B_off := by
    classical
    intro a b hb
    simp [Bmat, hb]
  A_herm := S.Amat_herm
  B_herm := S.Bmat_herm g
  K := 1 + |g| * S.W
  K_nonneg := by
    have hW := S.W_nonneg
    have : 0 ≤ |g| * S.W := mul_nonneg (abs_nonneg g) hW
    linarith
  A_rel_row := by
    intro a
    classical
    have hsum : ∑ b ∈ S.block a, ‖S.Amat a b‖ / S.sigOf b
        = ‖S.Amat a a‖ / S.sigOf a := by
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (S.self_mem_block a) h)
      rw [S.Amat_off_diag (Ne.symm hb)]
      simp
    rw [hsum, S.norm_Amat_diag a]
    have h1 : S.lam a ≤ S.sigOf a := S.lam_le_sigOf a
    have h2 : (0 : ℝ) < S.sigOf a := lt_of_lt_of_le zero_lt_one (S.one_le_sigOf a)
    have h3 : S.lam a / S.sigOf a ≤ 1 := by
      rw [div_le_one h2]; exact h1
    have h4 : 0 ≤ |g| * S.W := mul_nonneg (abs_nonneg g) S.W_nonneg
    linarith
  A_rel_col := by
    intro a
    classical
    have hsum : ∑ b ∈ S.block a, ‖S.Amat a b‖ = ‖S.Amat a a‖ := by
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (S.self_mem_block a) h)
      rw [S.Amat_off_diag (Ne.symm hb)]
      simp
    rw [hsum, S.norm_Amat_diag a]
    have h1 : S.lam a ≤ S.sigOf a := S.lam_le_sigOf a
    have h2 : (0 : ℝ) ≤ S.sigOf a := le_trans zero_le_one (S.one_le_sigOf a)
    have h4 : 0 ≤ |g| * S.W := mul_nonneg (abs_nonneg g) S.W_nonneg
    nlinarith
  A_comm := by
    intro a
    classical
    have hsum : ∑ b ∈ S.block a, |S.sigOf a - S.sigOf b| * ‖S.Amat a b‖ = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : a = b
      · subst hb; simp
      · rw [S.Amat_off_diag hb]; simp
    rw [hsum]
    have h2 : (0 : ℝ) ≤ S.sigOf a := le_trans zero_le_one (S.one_le_sigOf a)
    have h4 : 0 ≤ |g| * S.W := mul_nonneg (abs_nonneg g) S.W_nonneg
    nlinarith
  B_rel := by
    intro a
    have hterm : ∀ b ∈ S.block a, ‖S.Bmat g a b‖ ≤ |g| * |S.tr b| := by
      intro b _
      refine le_trans (S.norm_Bmat_le g a b) ?_
      calc |g| * |S.tr a| * |S.tr b| ≤ |g| * 1 * |S.tr b| := by
            gcongr
            exact S.abs_tr_le_one a
        _ = |g| * |S.tr b| := by ring
    calc ∑ b ∈ S.block a, ‖S.Bmat g a b‖ ≤ ∑ b ∈ S.block a, |g| * |S.tr b| :=
          Finset.sum_le_sum hterm
      _ = |g| * ∑ b ∈ S.block a, |S.tr b| := by rw [Finset.mul_sum]
      _ ≤ |g| * S.W := by
          exact mul_le_mul_of_nonneg_left (S.tr_sum a) (abs_nonneg g)
      _ ≤ 1 + |g| * S.W := by linarith
  B_comm := by
    intro a
    have hterm : ∀ b ∈ S.block a, |S.sigOf a - S.sigOf b| * ‖S.Bmat g a b‖
        ≤ |g| * (|S.mu a - S.mu b| * |S.tr b|) := by
      intro b _
      have hsig : |S.sigOf a - S.sigOf b| = |S.mu a - S.mu b| := by
        simp only [sigOf]
        congr 1
        ring
      rw [hsig]
      have h5 : ‖S.Bmat g a b‖ ≤ |g| * |S.tr b| := by
        refine le_trans (S.norm_Bmat_le g a b) ?_
        calc |g| * |S.tr a| * |S.tr b| ≤ |g| * 1 * |S.tr b| := by
              gcongr
              exact S.abs_tr_le_one a
          _ = |g| * |S.tr b| := by ring
      calc |S.mu a - S.mu b| * ‖S.Bmat g a b‖
          ≤ |S.mu a - S.mu b| * (|g| * |S.tr b|) :=
            mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
        _ = |g| * (|S.mu a - S.mu b| * |S.tr b|) := by ring
    calc ∑ b ∈ S.block a, |S.sigOf a - S.sigOf b| * ‖S.Bmat g a b‖
        ≤ ∑ b ∈ S.block a, |g| * (|S.mu a - S.mu b| * |S.tr b|) := Finset.sum_le_sum hterm
      _ = |g| * ∑ b ∈ S.block a, |S.mu a - S.mu b| * |S.tr b| := by rw [Finset.mul_sum]
      _ ≤ |g| * S.W := mul_le_mul_of_nonneg_left (S.tr_spread a) (abs_nonneg g)
      _ ≤ 1 + |g| * S.W := by linarith

/-! ## 2. The spectral cutoff -/

/-- **The spectral cutoff** on a general manifold: all modes with Laplace eigenvalue at most
`n`.  On the periodic box this is the momentum cutoff `|k|² ≤ n`. -/
def energyWindow (n : ℕ) : Set ι := {a | S.mu a ≤ (n : ℝ)}

/-- The spectral cutoffs exhaust the modes. -/
theorem energyWindow_exhausts (F : Finset ι) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ F, a ∈ S.energyWindow n := by
  classical
  refine eventually_atTop.mpr ⟨F.sup fun a => ⌈S.mu a⌉₊, fun n hn a ha => ?_⟩
  have h1 : S.mu a ≤ ((⌈S.mu a⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : (⌈S.mu a⌉₊ : ℕ) ≤ F.sup fun a => ⌈S.mu a⌉₊ :=
    Finset.le_sup (f := fun a : ι => ⌈S.mu a⌉₊) ha
  have h3 : ((⌈S.mu a⌉₊ : ℕ) : ℝ) ≤ ((F.sup fun a => ⌈S.mu a⌉₊ : ℕ) : ℝ) := Nat.cast_le.mpr h2
  have h4 : ((F.sup fun a => ⌈S.mu a⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  simp only [energyWindow, Set.mem_setOf_eq]
  linarith

end VielbeinSpectrum

/-! ## 3. Essential self-adjointness on a general manifold -/

/-- **The quantum-gravity Hamiltonian over a general spatial manifold is essentially
self-adjoint on the outer Fock space.**  The manifold enters only through the spectral data:
any spectrum, any coupling blocks, arbitrary coupling constant, and an arbitrary smooth
non-negative wall for the scalaron. -/
theorem qgManifold_essentiallySelfAdjointOn (W : WallPot) (S : VielbeinSpectrum ι) (g : ℝ) :
    EssentiallySelfAdjointOn (secN W (S.modes g)).dom (secData W (S.modes g)).ext :=
  secHam_essentiallySelfAdjointOn W _

/-- **The physical instance on a general manifold**: the full exponential Einstein-frame
Starobinsky wall. -/
theorem starobinsky_qgManifold_esa (M alpha : ℝ) (halpha : 0 < alpha)
    (S : VielbeinSpectrum ι) (g : ℝ) :
    EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (S.modes g)).dom
      (secData (starobinskyWall M alpha halpha) (S.modes g)).ext :=
  qgManifold_essentiallySelfAdjointOn (starobinskyWall M alpha halpha) S g

/-! ## 4. The spectrally truncated flows converge -/

/-- **The spectral cutoff converges on a general manifold.**  The Hamiltonians with the
scalaron–vielbein interactions switched off above the spectral cutoff `μ_a ≤ n` have unique
self-adjoint realizations whose flows converge to the exact quantum-gravity flow, uniformly
on every compact time interval. -/
theorem starobinsky_qgManifold_cutoff_flow_convergence (M alpha : ℝ) (halpha : 0 < alpha)
    (S : VielbeinSpectrum ι) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (Sn : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (S.modes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (S.modes g) (S.energyWindow n))) (Sn n).op) ∧
        StrongResolventConvergence T Sn ∧
        ∀ (v : Sec ι) (T₀ : ℝ), 0 ≤ T₀ →
          TendstoUniformlyOn (fun n t => (Sn n).stoneU t v) (fun t => T.stoneU t v) atTop
              (Set.Icc (-T₀) T₀) ∧
            ∀ t : ℝ, Tendsto (fun n => (Sn n).stoneU t v) atTop (𝓝 (T.stoneU t v)) :=
  qgOuterFock_truncation_flow_convergence (starobinskyWall M alpha halpha) (S.modes g)
    S.energyWindow S.energyWindow_exhausts

/-! ## 5. The fully discrete evolution on a general manifold -/

/-- **The fully discrete quantum-gravity evolution on a general spatial manifold.**  Both
halves of a concrete scheme: the spectral (mode) cutoff in space, and the Crank–Nicolson
(Cayley) step in time.  For every initial state and every time there is a number of time
steps per cutoff for which the fully discrete unitary evolution converges to the exact
quantum-gravity flow. -/
theorem starobinsky_qgManifold_fullyDiscrete_convergence (M alpha : ℝ) (halpha : 0 < alpha)
    (S : VielbeinSpectrum ι) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (Sn : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (S.modes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (S.modes g) (S.energyWindow n))) (Sn n).op) ∧
        ∀ (v : Sec ι) (t : ℝ), 0 < t →
          ∃ k : ℕ → ℕ, (∀ n, 0 < k n) ∧
            Tendsto (fun n => (cnStep (Sn n) (t / (k n)))^[k n] v) atTop
              (𝓝 (T.stoneU t v)) :=
  qgOuterFock_fullyDiscrete_convergence (starobinskyWall M alpha halpha) (S.modes g)
    S.energyWindow S.energyWindow_exhausts

/-! ## 6. Non-vacuity: an arbitrary spectrum is admissible -/

open Classical in
/-- **Any non-negative eigenvalue sequence is admissible.**  The construction constrains
neither the geometry nor the spectrum of the spatial manifold: given any sequence of
Laplace-type eigenvalues, the vielbein mode data exists (here with the torsion eigenvalues
saturating the Hodge bound and singleton coupling blocks). -/
def ofSpectrumSeq (mu : ℕ → ℝ) (hmu : ∀ a, 0 ≤ mu a) : VielbeinSpectrum ℕ where
  mu := mu
  mu_nonneg := hmu
  lam := mu
  lam_nonneg := hmu
  lam_le_mu := fun _ => le_rfl
  block := fun a => {a}
  mem_block_comm := fun a b => by simp [eq_comm]
  self_mem_block := fun a => Finset.mem_singleton_self a
  tr := fun _ => 1
  abs_tr_le_one := fun _ => by norm_num
  W := 1
  W_nonneg := zero_le_one
  tr_sum := fun a => by simp
  tr_spread := fun a => by simp

/-- The mode set of such an instance is infinite, and the torsion self-interaction is
present at every mode with a non-zero eigenvalue. -/
theorem ofSpectrumSeq_Amat (mu : ℕ → ℝ) (hmu : ∀ a, 0 ≤ mu a) (a : ℕ) :
    (ofSpectrumSeq mu hmu).Amat a a = ((mu a : ℝ) : ℂ) := by
  simp [VielbeinSpectrum.Amat, ofSpectrumSeq]

end

end BookProof.QgManifoldModeInstance


