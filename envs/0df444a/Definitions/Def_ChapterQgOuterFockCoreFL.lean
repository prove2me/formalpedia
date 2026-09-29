-- Prove2me | Definitions.Def_ChapterQgOuterFockCoreFL
-- name    : ChapterQgOuterFockCoreFL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T20:00:04.004506+00:00
-- url     : https://prove2.me/theorems/ded9ea52-7b03-4cfb-9ee8-6d9dac3ab08d
-- title:
--   From a graph core to the whole comparison domain What is proved
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgOuterFockCoreFL`, source chapter `BookProof/ChapterQgOuterFockCoreFL.lean`): From a graph core to the whole comparison domain What is proved
--
--   Theorem 1 of Faris–Lavine, as formalized in `BookProof.ChapterFarisLavine` and packaged with a comparison operator in `BookProof.ChapterQgOuterFockFarisLavine`, wants the Hamiltonian `H` defined on the **whole** domain `𝒟(N)` of the comparison operator. A concrete Hamiltonian, however, is handed to us on a small core — for the quantum-gravity sectors, the Gauss–polynomial core of `L²(ℝᴰ)`, which is much smaller than the Friedrichs domain of the oscillator. This module closes that gap once and for all.
--
--   The mechanism is the relative bound itself. If `‖H₀u‖ ≤ K‖(N+1)u‖` on the core `C₀`, then `H₀ ∘ (N+1)|_{C₀}⁻¹` is a **bounded** operator on the range of `(N+1)|_{C₀}`; that range is dense (`coreRange_dense`), so the bounded operator extends continuously to the whole space (`extCLM`), and composing back with `N + 1` on `𝒟(N)` produces the extension `ext`. The extension automatically satisfies the *same* relative bound (`ext_norm_le`), restricts to `H₀` on the core (`ext_core`), and — this is the point — inherits symmetry and the Faris–Lavine commutator bound from the core, by approximating an arbitrary domain vector in the graph norm of `N` (`gcSeq` and the continuity lemmas around it).
--
--   The hypothesis that makes the approximation available is `IsGraphCore`: every vector of `𝒟(N)` is approximated by core vectors *together with* their images under `N`.
--
--   * `shiftOp`, `shiftOp_injective` — the shift `N + 1` of a comparison operator and its injectivity (a consequence of positivity); * `commForm_congr`, `quadForm_congr` — the two Faris–Lavine forms depend only on the values of the operators, not on the domain they are presented on; * `IsGraphCore` — a subspace of `𝒟(N)` dense in the graph norm of `N`; * `CoreData` — the package: a comparison operator, a graph core, a symmetric operator on the core, and a relative bound `‖H₀u‖ ≤ K‖(N+1)u‖`; * `CoreData.coreRange`, `coreRange_dense`, `coreEquiv`, `resolvedMap`, `resolvedCLM`, `extCLM` — the bounded-extension construction; * **`CoreData.ext`**, `ext_core`, `ext_norm_le`, `ext_symmetricOn`, `ext_commForm_le` — the extension of the Hamiltonian to the whole comparison domain, with the relative bound, symmetry and the commutator bound all transported from the core with the *same* constants; * **`CoreData.ext_essentiallySelfAdjointOn`** — Faris–Lavine for the extension: the Hamiltonian extended from a graph core is essentially self-adjoint on `𝒟(N)`.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

import Definitions.Def_ChapterQgOuterFockFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterYangMillsFriedrichs


/-!
# From a graph core to the whole comparison domain

Theorem 1 of Faris–Lavine, as formalized in `BookProof.ChapterFarisLavine` and packaged
with a comparison operator in `BookProof.ChapterQgOuterFockFarisLavine`, wants the
Hamiltonian `H` defined on the **whole** domain `𝒟(N)` of the comparison operator.  A
concrete Hamiltonian, however, is handed to us on a small core — for the quantum-gravity
sectors, the Gauss–polynomial core of `L²(ℝᴰ)`, which is much smaller than the Friedrichs
domain of the oscillator.  This module closes that gap once and for all.

The mechanism is the relative bound itself.  If `‖H₀u‖ ≤ K‖(N+1)u‖` on the core `C₀`, then
`H₀ ∘ (N+1)|_{C₀}⁻¹` is a **bounded** operator on the range of `(N+1)|_{C₀}`; that range is
dense (`coreRange_dense`), so the bounded operator extends continuously to the whole space
(`extCLM`), and composing back with `N + 1` on `𝒟(N)` produces the extension `ext`.  The
extension automatically satisfies the *same* relative bound (`ext_norm_le`), restricts to
`H₀` on the core (`ext_core`), and — this is the point — inherits symmetry and the
Faris–Lavine commutator bound from the core, by approximating an arbitrary domain vector
in the graph norm of `N` (`gcSeq` and the continuity lemmas around it).

The hypothesis that makes the approximation available is `IsGraphCore`: every vector of
`𝒟(N)` is approximated by core vectors *together with* their images under `N`.

## What is proved

* `shiftOp`, `shiftOp_injective` — the shift `N + 1` of a comparison operator and its
  injectivity (a consequence of positivity);
* `commForm_congr`, `quadForm_congr` — the two Faris–Lavine forms depend only on the
  values of the operators, not on the domain they are presented on;
* `IsGraphCore` — a subspace of `𝒟(N)` dense in the graph norm of `N`;
* `CoreData` — the package: a comparison operator, a graph core, a symmetric operator on
  the core, and a relative bound `‖H₀u‖ ≤ K‖(N+1)u‖`;
* `CoreData.coreRange`, `coreRange_dense`, `coreEquiv`, `resolvedMap`, `resolvedCLM`,
  `extCLM` — the bounded-extension construction;
* **`CoreData.ext`**, `ext_core`, `ext_norm_le`, `ext_symmetricOn`, `ext_commForm_le` —
  the extension of the Hamiltonian to the whole comparison domain, with the relative
  bound, symmetry and the commutator bound all transported from the core with the *same*
  constants;
* **`CoreData.ext_essentiallySelfAdjointOn`** — Faris–Lavine for the extension: the
  Hamiltonian extended from a graph core is essentially self-adjoint on `𝒟(N)`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgOuterFockCoreFL

open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.EsaClosure
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore
open Filter Topology

noncomputable section

/-! ## 1. Extending a relatively bounded operator from a graph core -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The shift `N + 1` of a comparison operator. -/
def shiftOp (C : Comparison F) : C.dom →ₗ[ℂ] F := C.op + C.dom.subtype

omit [CompleteSpace F] in
@[simp] theorem shiftOp_apply (C : Comparison F) (x : C.dom) :
    shiftOp C x = C.op x + (x : F) := rfl





omit [CompleteSpace F] in
theorem shiftOp_injective (C : Comparison F) : Function.Injective (shiftOp C) := by
  intro a b hab
  have hz : shiftOp C (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h := norm_le_norm_shift C.op C.pos (a - b)
  rw [← shiftOp_apply, hz, norm_zero] at h
  have h0 : ((a - b : C.dom) : F) = 0 := by
    have := norm_nonneg ((a - b : C.dom) : F)
    exact norm_le_zero_iff.mp h
  exact sub_eq_zero.mp (Subtype.ext (by simpa using h0))

/-- `C₀` is a **graph core** for the comparison operator `C`: it sits inside the domain and
every domain vector is approximated by a core vector simultaneously in the norm of `F` and
in the norm of its image under `N`. -/
structure IsGraphCore (C : Comparison F) (C₀ : Submodule ℂ F) : Prop where
  /-- The core sits inside the domain. -/
  le : C₀ ≤ C.dom
  /-- Approximation in the graph norm. -/
  approx : ∀ (x : C.dom) (ε : ℝ), 0 < ε → ∃ y : C.dom, (y : F) ∈ C₀ ∧
    ‖(y : F) - (x : F)‖ < ε ∧ ‖C.op y - C.op x‖ < ε

/-- The data needed to extend a symmetric operator from a graph core to the whole domain of
a comparison operator: a relative bound with respect to `N + 1`. -/
structure CoreData (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] where
  /-- The comparison operator. -/
  C : Comparison F
  /-- The graph core. -/
  C₀ : Submodule ℂ F
  /-- The core is a graph core. -/
  gc : IsGraphCore C C₀
  /-- The operator, defined on the core only. -/
  H₀ : C₀ →ₗ[ℂ] F
  /-- The relative bound constant. -/
  K : ℝ
  /-- The relative bound constant is nonnegative. -/
  hK : 0 ≤ K
  /-- The relative bound `‖H₀ p‖ ≤ K‖(N + 1)p‖` on the core. -/
  rel : ∀ p : C₀, ‖H₀ p‖ ≤ K * ‖C.op ⟨(p : F), gc.le p.2⟩ + (p : F)‖

namespace CoreData

variable (d : CoreData F)

/-- The comparison operator restricted to the core. -/
def coreN : d.C₀ →ₗ[ℂ] F := d.C.op.comp (Submodule.inclusion d.gc.le)



/-- The shift `N + 1` restricted to the core. -/
def coreShift : d.C₀ →ₗ[ℂ] F := (shiftOp d.C).comp (Submodule.inclusion d.gc.le)

@[simp] theorem coreShift_apply (p : d.C₀) :
    d.coreShift p = d.C.op ⟨(p : F), d.gc.le p.2⟩ + (p : F) := rfl

theorem coreShift_injective : Function.Injective d.coreShift := by
  intro a b hab
  have h1 : (Submodule.inclusion d.gc.le) a = (Submodule.inclusion d.gc.le) b :=
    shiftOp_injective d.C hab
  have h2 : (a : F) = (b : F) := by
    simpa using congrArg (fun z : d.C.dom => (z : F)) h1
  exact Subtype.ext h2

/-- The image of the core under `N + 1`. -/
def coreRange : Submodule ℂ F := LinearMap.range d.coreShift







/-- The core, identified with its image under `N + 1`. -/
def coreEquiv : d.C₀ ≃ₗ[ℂ] d.coreRange :=
  LinearEquiv.ofInjective _ d.coreShift_injective

@[simp] theorem coreEquiv_coe (p : d.C₀) : ((d.coreEquiv p : d.coreRange) : F) = d.coreShift p :=
  rfl

/-- `H₀ ∘ (N+1)⁻¹` on the image of the core: a *bounded* operator, by the relative bound. -/
def resolvedMap : d.coreRange →ₗ[ℂ] F := d.H₀.comp d.coreEquiv.symm.toLinearMap

theorem resolvedMap_bound (w : d.coreRange) : ‖d.resolvedMap w‖ ≤ d.K * ‖(w : F)‖ := by
  have h := d.rel (d.coreEquiv.symm w)
  have hw : d.coreShift (d.coreEquiv.symm w) = (w : F) := by
    rw [← coreEquiv_coe, LinearEquiv.apply_symm_apply]
  rw [← coreShift_apply, hw] at h
  exact h

/-- The bounded operator `H₀ ∘ (N+1)⁻¹`, on the dense subspace `(N+1)C₀`. -/
def resolvedCLM : d.coreRange →L[ℂ] F := d.resolvedMap.mkContinuous d.K d.resolvedMap_bound



/-- Its extension to the whole space, by density. -/
def extCLM : F →L[ℂ] F := d.resolvedCLM.extend d.coreRange.subtypeL



/-- **The extension of `H₀` from the graph core to the whole comparison domain.** -/
def ext : d.C.dom →ₗ[ℂ] F := (d.extCLM : F →ₗ[ℂ] F).comp (shiftOp d.C)







/-! ### Graph-core approximating sequences -/

/-- A sequence in the core converging to `x` in the graph norm. -/
def gcSeq (x : d.C.dom) (k : ℕ) : d.C.dom :=
  (d.gc.approx x (1 / (k + 1)) (by positivity)).choose



















/-! ### The extension inherits symmetry and the commutator bound -/











end CoreData

end Abstract

end

end BookProof.QgOuterFockCoreFL


