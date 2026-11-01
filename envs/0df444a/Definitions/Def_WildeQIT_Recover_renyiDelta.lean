-- Prove2me | Definitions.Def_WildeQIT_Recover_renyiDelta
-- name    : WildeQIT_Recover_renyiDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:21:12.318979+00:00
-- url     : https://prove2.me/theorems/a2b482e6-66af-472d-abe8-b5b2fd6e8943
-- title:
--   The Rényi relative entropy difference $\widetilde\Delta_\alpha(\rho,\sigma,\mathcal N)$
-- statement:
--   Let $\rho$ be a density operator, $\sigma$ positive semi-definite and $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ a quantum channel with Kraus operators $\{V_l\}$. Its **isometric extension** $U:\mathcal H\to\mathcal H'\otimes\mathcal H_E$ is $U|\psi\rangle=\sum_l V_l|\psi\rangle\otimes|l\rangle_E$; it satisfies $U^\dagger U=I_{\mathcal H}$ and $\operatorname{Tr}_E\{U(\cdot)U^\dagger\}=\mathcal N(\cdot)$.
--
--   For $\alpha\in(0,1)\cup(1,\infty)$ define
--
--   $$
--   \widetilde Q_\alpha(\rho,\sigma,\mathcal N)=\left\|\left([\mathcal N(\rho)]^{\frac{1-\alpha}{2\alpha}}[\mathcal N(\sigma)]^{\frac{\alpha-1}{2\alpha}}\otimes I_E\right)U\sigma^{\frac{1-\alpha}{2\alpha}}\rho^{1/2}\right\|_{2\alpha}^{2\alpha},
--   \qquad
--   \widetilde\Delta_\alpha(\rho,\sigma,\mathcal N)=\frac{1}{\alpha-1}\ln\widetilde Q_\alpha(\rho,\sigma,\mathcal N),
--   $$
--
--   where all powers are taken on the support and $\|X\|_{p}^{p}=\operatorname{Tr}\{|X|^{p}\}$ with $|X|=\sqrt{X^\dagger X}$.
--
--   The quantity $\widetilde\Delta_\alpha$ is a Rényi generalization of the relative entropy difference $D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))$ (Lemma 12.4.1); at $\alpha=1/2$ it equals $-\ln F(\rho,\mathcal P_{\sigma,\mathcal N}(\mathcal N(\rho)))$.
--
--   **Formalization Note** $\widetilde Q_\alpha$ is computed as $\operatorname{Tr}\{(X^\dagger X)^{\alpha}\}$. The isometric extension is the canonical one built from the Kraus family; the book notes that $\widetilde Q_\alpha$ does not depend on that choice. The logarithm is natural, as in the book. Values at $\alpha\le0$ and $\alpha=1$ are junk values that no statement uses.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 5.2.1, p. 190; §12.4, (12.56)–(12.57), pp. 373–374

import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_Recover_spectralFun

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §12.4, (12.56)–(12.57),
pp. 373–374: the Rényi generalization `Δ̃_α(ρ, σ, 𝒩)` of a relative entropy difference, built
from an isometric extension of the channel (Definition 5.2.1, p. 190).
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.Recover

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- **Isometric extension of a channel** (Wilde, arXiv:1106.1445v8, Definition 5.2.1, p. 190):
for `𝒩(X) = Σₗ Vₗ X Vₗ†`, the isometry `U : ℋ → ℋ' ⊗ ℋ_E`, `U|ψ⟩ = Σₗ Vₗ|ψ⟩ ⊗ |l⟩_E`, with
environment `ℋ_E` spanned by the Kraus index. It satisfies `U†U = I` and `Tr_E{U X U†} = 𝒩(X)`.

**Formalization Note** Rows are indexed by `ℋ' × ℋ_E`, the Kronecker convention. The book notes
(p. 374) that `Q̃_α` below does not depend on the choice of isometric extension, so this canonical
choice is an encoding. -/
def isometricExt (N : QChannel a b) : Matrix (b × N.ι) a ℂ :=
  Matrix.of fun p k => N.K p.2 p.1 k

/-- **The operator inside `Q̃_α`** (Wilde, arXiv:1106.1445v8, (12.57), p. 373):
`X_α = ([𝒩(ρ)]^{(1−α)/(2α)} [𝒩(σ)]^{(α−1)/(2α)} ⊗ I_E) U σ^{(1−α)/(2α)} ρ^{1/2}`,
with all powers taken on the support (§12.2.3, p. 369). -/
noncomputable def renyiOp (ρ σ : Matrix a a ℂ) (N : QChannel a b) (α : ℝ) :
    Matrix (b × N.ι) a ℂ :=
  letI : DecidableEq N.ι := Classical.decEq _
  ((supportPow (N.apply ρ) (((1 - α) / (2 * α) : ℝ) : ℂ) *
      supportPow (N.apply σ) (((α - 1) / (2 * α) : ℝ) : ℂ)) ⊗ₖ (1 : Matrix N.ι N.ι ℂ)) *
    isometricExt N * supportPow σ (((1 - α) / (2 * α) : ℝ) : ℂ) * supportPow ρ (1 / 2)

/-- **`Q̃_α(ρ, σ, 𝒩)`** (Wilde, arXiv:1106.1445v8, (12.57), p. 373): `‖X_α‖_{2α}^{2α}` with
`X_α = renyiOp ρ σ N α`.

**Formalization Note** `‖X‖_{2α}^{2α} = Tr{|X|^{2α}} = Tr{(X†X)^α}` ((12.4)); the power `α > 0`
is taken on the support, which changes nothing since `0^α = 0`. The real part of the trace is
taken; the trace is real and nonnegative. -/
noncomputable def renyiQ (ρ σ : Matrix a a ℂ) (N : QChannel a b) (α : ℝ) : ℝ :=
  (supportPow ((renyiOp ρ σ N α)ᴴ * renyiOp ρ σ N α) (α : ℂ)).trace.re

/-- **Rényi generalization of a relative entropy difference** (Wilde, arXiv:1106.1445v8, (12.56),
p. 373): `Δ̃_α(ρ, σ, 𝒩) = (1/(α − 1)) ln Q̃_α(ρ, σ, 𝒩)`, for `α ∈ (0, 1) ∪ (1, ∞)`.

**Formalization Note** The logarithm is natural, as in (12.56). The book defines `Δ̃_α` only for
`α ∈ (0, 1) ∪ (1, ∞)`; the Lean value at other `α` is a junk value that no statement uses. -/
noncomputable def renyiDelta (ρ σ : Matrix a a ℂ) (N : QChannel a b) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (renyiQ ρ σ N α)

end WildeQIT.Recover


