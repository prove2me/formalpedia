-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_diamondDist
-- name    : UnitaryQIPPSPACE_diamondDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:54.549756+00:00
-- url     : https://prove2.me/theorems/23193a4f-c3a4-4526-a49f-6f9ff66fea56
-- title:
--   Diamond distance $D_\diamond$
-- statement:
--   The **diamond distance** between two maps $\mathcal E,\mathcal F:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ is
--   $$D_\diamond(\mathcal E,\mathcal F)=\sup_{\mathcal H_R}\max_{|\psi\rangle\in\mathcal H_A\otimes\mathcal H_R}\mathrm{TD}\big((\mathcal E\otimes I_R)(\psi),(\mathcal F\otimes I_R)(\psi)\big),$$
--   the supremum over all finite-dimensional reference spaces and unit vectors.
--
--   It is the error measure for channels (Corollary 4.8) and for unnormalized accepted maps (Lemmas 4.16, 4.18).
--
--   **Formalization Note** The supremum runs over every reference dimension $k$; for linear maps the set is bounded. The $\tfrac12$ of the trace distance is built in.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2, Quantum information theory, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ShadowBootstrap_braket

open Matrix

namespace UnitaryQIPPSPACE

/-- `Φ ⊗ id_R`: a map `Φ : L(ℂ^α) → L(ℂ^β)` applied to the first factor of `L(ℂ^α ⊗ ℂ^γ)`, entry
`((b, r), (b', r'))` equal to `Φ(X^{(r, r')})_{b, b'}` with `X^{(r,r')}(a, a') = X((a, r), (a', r'))`
(the linear extension `∑_{r,r'} Φ(X^{(r,r')}) ⊗ |r⟩⟨r'|`). -/
def tensorId {α β γ : Type} (Φ : Matrix α α ℂ → Matrix β β ℂ) (X : Matrix (α × γ) (α × γ) ℂ) :
    Matrix (β × γ) (β × γ) ℂ :=
  fun x x' => Φ (fun a a' => X (a, x.2) (a', x'.2)) x.1 x'.1

/-- **Diamond distance** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held
version sha256 9e357a00…, §2, p. 9 (PDF p. 11)): "The diamond distance between two quantum channels
`E, F : L(H_A) → L(H_B)` is defined as
`D⋄(E, F) = sup_{H_R} max_{|ψ⟩ ∈ H_A ⊗ H_R} TD((E ⊗ I_R)(ψ), (F ⊗ I_R)(ψ))`."

Here the supremum runs over every finite reference dimension `k` and every unit vector `ψ` on
`H_A ⊗ ℂ^k`. As in the paper (Lemmas 4.16, 4.18), the formula is applied to linear maps that need
not be trace preserving.

**Formalization Note** For linear `E, F` the set is nonempty (`k = 1`) and bounded above (the trace
norm of `(E ⊗ id_k)(ψ)` is bounded uniformly in `k`), so the real `sSup` is the true supremum. The
`½` of the trace distance is built in, as in the paper. -/
noncomputable def diamondDist {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (E F : Matrix α α ℂ → Matrix β β ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (k : ℕ) (ψ : α × Fin k → ℂ), ShadowBootstrap.IsUnitVec ψ ∧
    r = DimFreeShadow.traceDistance (tensorId E (ObliviousRSP.pureState ψ)) (tensorId F (ObliviousRSP.pureState ψ))}

end UnitaryQIPPSPACE


