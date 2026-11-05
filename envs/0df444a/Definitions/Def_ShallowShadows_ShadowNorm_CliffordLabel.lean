-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_CliffordLabel
-- name    : ShallowShadows_ShadowNorm_CliffordLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:14.951639+00:00
-- url     : https://prove2.me/theorems/94121c42-8361-4d24-8955-aa872c9d6365
-- title:
--   Clifford group modulo global phase
-- statement:
--   Two Clifford unitaries $U, V$ on $k$ qubits are identified when $UXU^\dagger = VXV^\dagger$ for every matrix $X$, i.e. when they differ by a global phase. The set of classes is the **Clifford group modulo phase**; each class has a chosen representative unitary.
--
--   A uniformly random Clifford gate, as used for the single-qubit layer, the two-qubit brickwork gates and the global ensemble $\mathcal U_\infty$, is a uniformly random element of this finite set.
--
--   **Formalization Note** The Clifford group including all $U(1)$ phases is infinite, but every quantity of the shadow protocol depends on $U$ only through $X\mapsto UXU^\dagger$. Finiteness of the quotient is not proved here; statements take a `Fintype` instance on it as an argument (the pattern of the published `QAlgorithms.Clifford.ProjectiveGroup`). The module also provides the representative `CliffordLabel.rep` (via `Quotient.out`), the fact that it is Clifford, and nonemptiness (the identity class).
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §III, p. 3; §V, p. 4

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_IsClifford

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Two Clifford unitaries are identified when they act identically by conjugation,
`U X U† = V X V†` for every operator `X`, i.e. when they differ by a global phase. -/
def cliffordPhaseSetoid (k : ℕ) : Setoid {U : Matrix.unitaryGroup (Bits k) ℂ // IsClifford U} where
  r U V := ∀ X : Op k, (U.1 : Op k) * X * star (U.1 : Op k) = (V.1 : Op k) * X * star (V.1 : Op k)
  iseqv := ⟨fun _ _ => rfl, fun h X => (h X).symm, fun h1 h2 X => (h1 X).trans (h2 X)⟩

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §III, p. 3 and §V,
p. 4: the `k`-qubit Clifford group modulo global phase, the set over which "uniformly random"
Clifford gates (single-qubit, two-qubit, and the global `n`-qubit Cliffords of `𝒰_∞`) are drawn.

**Formalization Note.** The Clifford group with all `U(1)` phases is infinite; the measurement
channel, `t_{λ,d}`, `τ_{(λ,λ'),d}` and both shadow norms depend on a unitary `U` only through the
conjugation `X ↦ U X U†`. The uniform distribution over Cliffords is therefore the uniform
distribution over this quotient, which is finite. Its finiteness is not proved here: every
statement takes `[Fintype (CliffordLabel k)]` as an instance argument (the published pattern of
`QAlgorithms.Clifford.uniformGlobalEnsemble`), and since `Fintype` is a subsingleton the uniform
law does not depend on the instance supplied. Pattern: `QAlgorithms.Clifford.ProjectiveGroup`,
on `Bits k` instead of `Fin k → Bool`. -/
def CliffordLabel (k : ℕ) : Type := Quotient (cliffordPhaseSetoid k)

/-- A representative unitary of a Clifford label (`Quotient.out`). Every quantity of the mission
uses it only through `X ↦ U X U†` or `U† X U`, which do not depend on the representative. -/
noncomputable def CliffordLabel.rep {k : ℕ} (c : CliffordLabel k) : Matrix.unitaryGroup (Bits k) ℂ :=
  (Quotient.out c).1

/-- The representative of a label is a Clifford unitary. -/
theorem CliffordLabel.rep_isClifford {k : ℕ} (c : CliffordLabel k) : IsClifford c.rep :=
  (Quotient.out c).2

/-- The identity class: `CliffordLabel k` is nonempty. -/
instance CliffordLabel.instNonempty (k : ℕ) : Nonempty (CliffordLabel k) :=
  ⟨Quotient.mk (cliffordPhaseSetoid k) ⟨1, fun lam => ⟨lam, Or.inl (by simp)⟩⟩⟩

end ShallowShadows.ShadowNorm


