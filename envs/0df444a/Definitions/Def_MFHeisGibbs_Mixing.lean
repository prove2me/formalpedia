-- Prove2me | Definitions.Def_MFHeisGibbs_Mixing
-- name    : MFHeisGibbs_Mixing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:18.172485+00:00
-- url     : https://prove2.me/theorems/c9832579-a426-40b5-9e0b-687c5c8db3a1
-- title:
--   The adjoint $\mathcal L^\dagger$, the semigroup $e^{t\mathcal L^\dagger}$, the state $\rho_\infty$, $d_{\mathcal L}(t)$ and $t_{\mathrm{mix},\mathcal L}(\varepsilon)$
-- statement:
--   $\mathcal L^\dagger$ is the Hilbert–Schmidt adjoint of $\mathcal L$, and $\mathcal T_t=e^{t\mathcal L^\dagger}$ is the Schrödinger-picture semigroup. The zero-temperature state $\rho_\infty$ is the maximally mixed state on the ground space of $H_n$. Then
--
--   $$d_{\mathcal L}(t)=\sup_{\eta\text{ a state}}\frac12\|\mathcal T_t\eta-\rho_\infty\|_1,\qquad t_{\mathrm{mix},\mathcal L}(\varepsilon)=\inf\{t\ge0:d_{\mathcal L}(t)\le\varepsilon\}.$$
--
--   These quantify the convergence in Theorem 3, the zero-temperature statement.
--
--   **Formalization Note** The trace norm is the published `WildeQIT.traceNorm`. The exponential is that of a matrix indexed by pairs of basis labels, since `Module.End` has no default topology. The file also packages the conclusion of Theorem 3 for one generator as `ZeroTempBounds`.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (2), p.3 (PDF 4); p.36 (PDF 37)

import Definitions.Def_MFHeisGibbs_Bohr
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_WildeQIT_traceNorm

open Matrix
open scoped ComplexOrder

namespace MFHeisGibbs

/-!
# The Schrödinger-picture semigroup and the mixing time at `β = ∞`

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
(2), p.3; p.36.

**Formalization Note.** `L†` is the Hilbert–Schmidt adjoint, written entrywise as
`(L†[X])_{ab} = Tr((L[E_{ab}])† X)`, which is the unique map with `⟨L†X, Y⟩ = ⟨X, LY⟩`. The semigroup
`T_t = e^{tL†}` is the matrix exponential of `L†` on `(Fin n → Bool) × (Fin n → Bool)`-indexed vectors,
because `Module.End` has no default topology. The supremum in `dL` is over the nonempty set of states,
and the values lie in a bounded set because `T_t` is trace-preserving and positive for the generators
this file is applied to.
-/

/-- The Hilbert–Schmidt adjoint `L†` of a superoperator. -/
noncomputable def hsAdjoint {n : ℕ} (L : Module.End ℂ (Op n)) : Module.End ℂ (Op n) where
  toFun X := Matrix.of fun a b => trace ((L (Matrix.single a b 1))ᴴ * X)
  map_add' X Y := by ext a b; simp [mul_add, trace_add]
  map_smul' c X := by ext a b; simp [trace_smul]

/-- The matrix of a superoperator in the matrix-unit basis:
`S_{(a,b),(c,d)} = (L[E_{cd}])_{ab}`. -/
noncomputable def superMatrix {n : ℕ} (L : Module.End ℂ (Op n)) :
    Matrix ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool)) ℂ :=
  Matrix.of fun p q => L (Matrix.single q.1 q.2 1) p.1 p.2

/-- The Schrödinger-picture evolution `T_t[η] = e^{tL†}[η]`, p.36. -/
noncomputable def schrodFlow {n : ℕ} (L : Module.End ℂ (Op n)) (t : ℝ) (η : Op n) : Op n :=
  Matrix.of fun a b =>
    ∑ q, (NormedSpace.exp ((t : ℂ) • superMatrix (hsAdjoint L))) (a, b) q * η q.1 q.2

/-- `η` is a quantum state: positive semidefinite of trace one. -/
def IsState {n : ℕ} (η : Op n) : Prop := η.PosSemidef ∧ trace η = 1

/-- The ground energy `min spec(H_n)`. -/
noncomputable def groundEnergy (n : ℕ) : ℝ := ⨅ k, (Hn_isHermitian n).eigenvalues k

/-- The projection onto the ground space of `H_n`. -/
noncomputable def groundProj (n : ℕ) : Op n := specProj (Hn_isHermitian n) (groundEnergy n)

/-- The zero-temperature state: "the maximally mixed state on the ground space of `H_n`", p.3. -/
noncomputable def rhoInf (n : ℕ) : Op n := (trace (groundProj n))⁻¹ • groundProj n

/-- `d_L(t) = sup_η ½∥T_t η − ρ_∞∥₁`, the supremum over states, p.36. -/
noncomputable def dL {n : ℕ} (L : Module.End ℂ (Op n)) (t : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ η : Op n, IsState η ∧
    r = (1 / 2) * WildeQIT.traceNorm (schrodFlow L t η - rhoInf n)}

/-- `t_{mix,L}(ε) = inf{t ≥ 0 : d_L(t) ≤ ε}`, p.36. -/
noncomputable def tmix {n : ℕ} (L : Module.End ℂ (Op n)) (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ dL L t ≤ ε}

/-- The conclusion of Theorem 3 for one generator: the unique stationary state is `ρ_∞`, the gap is
between `c/n` and `C/n`, and the mixing time is between `c n log(1/ε)` and `C n log(1/ε)`. -/
def ZeroTempBounds (c C : ℝ) {n : ℕ} (L : Module.End ℂ (Op n)) : Prop :=
  (∀ η : Op n, IsState η → (hsAdjoint L η = 0 ↔ η = rhoInf n)) ∧ IsState (rhoInf n) ∧
  c / (n : ℝ) ≤ specGap L ∧ specGap L ≤ C / (n : ℝ) ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    c * ((n : ℝ) * Real.log (1 / ε)) ≤ tmix L ε ∧ tmix L ε ≤ C * ((n : ℝ) * Real.log (1 / ε))

end MFHeisGibbs


