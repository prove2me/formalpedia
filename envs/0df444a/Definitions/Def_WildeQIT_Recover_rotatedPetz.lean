-- Prove2me | Definitions.Def_WildeQIT_Recover_rotatedPetz
-- name    : WildeQIT_Recover_rotatedPetz
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:21:15.352755+00:00
-- url     : https://prove2.me/theorems/8137ccdf-7de7-4c14-afee-d66c96f8ead2
-- title:
--   The Petz recovery map $\mathcal P_{\sigma,\mathcal N}$ and the rotated Petz map $\mathcal R^t_{\sigma,\mathcal N}$
-- statement:
--   Let $\sigma$ be a positive semi-definite operator on $\mathcal H$ and $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ a quantum channel with Kraus operators $\{V_l\}$, $\mathcal N(X)=\sum_l V_lXV_l^\dagger$. Its adjoint is $\mathcal N^\dagger(Y)=\sum_l V_l^\dagger Y V_l$.
--
--   The **Petz recovery map** $\mathcal P_{\sigma,\mathcal N}:\mathcal L(\mathcal H')\to\mathcal L(\mathcal H)$ is
--
--   $$
--   \mathcal P_{\sigma,\mathcal N}(Q)=\sigma^{1/2}\,\mathcal N^\dagger\!\left([\mathcal N(\sigma)]^{-1/2}\,Q\,[\mathcal N(\sigma)]^{-1/2}\right)\sigma^{1/2},
--   $$
--
--   the **partial isometric map** is $\mathcal U_{\sigma,t}(M)=\sigma^{it}M\sigma^{-it}$ for $t\in\mathbb R$, and the **rotated Petz map** is
--
--   $$
--   \mathcal R^t_{\sigma,\mathcal N}=\mathcal U_{\sigma,-t}\circ\mathcal P_{\sigma,\mathcal N}\circ\mathcal U_{\mathcal N(\sigma),t},
--   \qquad
--   \mathcal R^t_{\sigma,\mathcal N}(Q)=\sigma^{-it}\,\mathcal P_{\sigma,\mathcal N}\!\left([\mathcal N(\sigma)]^{it}Q[\mathcal N(\sigma)]^{-it}\right)\sigma^{it}.
--   $$
--
--   All powers are taken on the support, so $[\mathcal N(\sigma)]^{-1/2}$ is the inverse square root on $\operatorname{supp}(\mathcal N(\sigma))$ and $\sigma^{it}\sigma^{-it}=\Pi_\sigma$.
--
--   The average of the rotated Petz maps against the density $\beta_0$ is the universal recovery channel of the chapter.
--
--   **Formalization Note** The channel is given in Choi–Kraus form (the published `QChannel`); every channel has one (Theorem 4.4.1), and the adjoint does not depend on the Kraus family.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.4.6, p. 157; Definition 12.3.1, (12.30), p. 371; (12.35), p. 372; Definition 12.3.2, (12.37), p. 372

import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_Recover_spectralFun

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §12.3, pp. 371–372:
the Petz recovery map (Definition 12.3.1), the partial isometric map `𝒰_{σ,t}` ((12.35)) and the
rotated Petz map (Definition 12.3.2).
-/

open Matrix

namespace WildeQIT.Recover

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- **Adjoint of a channel** `𝒩†(Y) = Σₗ Vₗ† Y Vₗ` for `𝒩(X) = Σₗ Vₗ X Vₗ†` (Wilde,
arXiv:1106.1445v8, Definition 4.4.6, p. 157, recalled on p. 374): the adjoint
with respect to the Hilbert–Schmidt inner product. -/
noncomputable def adjointMap (N : QChannel a b) (Y : Matrix b b ℂ) : Matrix a a ℂ :=
  ∑ i, (N.K i)ᴴ * Y * N.K i

/-- **Petz recovery map** (Wilde, arXiv:1106.1445v8, Definition 12.3.1, (12.30), p. 371): for a
positive semi-definite `σ` and a channel `𝒩`,
`𝒫_{σ,𝒩}(Q) = σ^{1/2} 𝒩†([𝒩(σ)]^{-1/2} Q [𝒩(σ)]^{-1/2}) σ^{1/2}`.

**Formalization Note** `[𝒩(σ)]^{-1/2}` is taken on the support of `𝒩(σ)` (Definition 3.3.1,
§12.2.1, p. 367), via `supportPow`. -/
noncomputable def petzMap (σ : Matrix a a ℂ) (N : QChannel a b) (Q : Matrix b b ℂ) :
    Matrix a a ℂ :=
  supportPow σ (1 / 2) *
    adjointMap N (supportPow (N.apply σ) (-(1 / 2)) * Q * supportPow (N.apply σ) (-(1 / 2))) *
    supportPow σ (1 / 2)

/-- **Partial isometric map** `𝒰_{σ,t}(M) = σ^{it} M σ^{-it}` (Wilde, arXiv:1106.1445v8, (12.35),
p. 372), with `σ^{it}` taken on the support of `σ`, so that `σ^{it} σ^{-it} = Π_σ`. -/
noncomputable def rotU {n : Type} [Fintype n] [DecidableEq n]
    (σ : Matrix n n ℂ) (t : ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  supportPow σ ((t : ℂ) * Complex.I) * M * supportPow σ (-((t : ℂ) * Complex.I))

/-- **Rotated Petz map** (Wilde, arXiv:1106.1445v8, Definition 12.3.2, (12.37), p. 372):
`ℛ^t_{σ,𝒩} = 𝒰_{σ,−t} ∘ 𝒫_{σ,𝒩} ∘ 𝒰_{𝒩(σ),t}`, i.e.
`ℛ^t_{σ,𝒩}(Q) = σ^{-it} 𝒫_{σ,𝒩}([𝒩(σ)]^{it} Q [𝒩(σ)]^{-it}) σ^{it}`. -/
noncomputable def rotatedPetz (σ : Matrix a a ℂ) (N : QChannel a b) (t : ℝ) (Q : Matrix b b ℂ) :
    Matrix a a ℂ :=
  rotU σ (-t) (petzMap σ N (rotU (N.apply σ) t Q))

end WildeQIT.Recover


