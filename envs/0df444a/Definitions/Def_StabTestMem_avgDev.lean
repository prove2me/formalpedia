-- Prove2me | Definitions.Def_StabTestMem_avgDev
-- name    : StabTestMem_avgDev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:44.33759+00:00
-- url     : https://prove2.me/theorems/8d6a26a8-8a0d-4052-9baa-1d13c9baf314
-- title:
--   Average likelihood-ratio deviation $\mathbb E_{x\sim P_{\mathrm{mm}}}|L(x)-1|$
-- statement:
--   For a protocol with transcript functional $Y\mapsto\operatorname{Tr}[E_xY]$ and an operator $\sigma$ on $t$ copies, let $P_{\mathrm{mm}}(x)=\operatorname{Tr}[E_x\rho_{\mathrm{mm}}]$, $P_\sigma(x)=\operatorname{Tr}[E_x\sigma]$ and $L(x)=P_\sigma(x)/P_{\mathrm{mm}}(x)$. Then
--
--   $$\mathbb E_{x\sim P_{\mathrm{mm}}}\big[|L(x)-1|\big]=\sum_x P_{\mathrm{mm}}(x)\,\Big|\frac{P_\sigma(x)}{P_{\mathrm{mm}}(x)}-1\Big| .$$
--
--   With $\sigma=\sigma_P$ it is the quantity of Theorem 5.9; with $\sigma=\rho_H$ that of Theorem B.3.
--
--   **Formalization Note** Terms with $P_{\mathrm{mm}}(x)=0$ contribute $0$ (Lean's $a/0=0$), as in an expectation under $P_{\mathrm{mm}}$; such $x$ have $E_x=0$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Eqs. (76)–(77), p. 37; Eq. (103), p. 41; Eq. (224), p. 64

import Definitions.Def_StabTestMem_MemProtocol
import Definitions.Def_StabTestMem_rhoMM

namespace StabTestMem

open QAlgorithms

/-- **Average likelihood-ratio deviation `E_{x∼P_mm}[|L(x) − 1|]` of a protocol.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Eqs. (76),
(77), p. 37 ("P_mm(x) = Tr[E_x]/2^{nt} … L(x) = 2^{nt} µ_2(x)/Tr[E_x]"), Eq. (103), p. 41
(`L(x) = P_{σ_P}(x)/P_mm(x)`), Eq. (224), p. 64 (`L(x) = P_H(x)/P_mm(x)`).

For a protocol `P` and a `t`-copy operator `σ`, with `P_mm(x) = Re Tr[E_x ρ_mm]` and
`P_σ(x) = Re Tr[E_x σ]`: `avgDev P σ = Σ_x P_mm(x) · |P_σ(x)/P_mm(x) − 1|`.

**Formalization Note.** The ratio is literal; Lean's `a / 0 = 0` makes the terms with
`P_mm(x) = 0` vanish, which is what the expectation under `P_mm` means (and `P_mm(x) = 0` forces
`E_x = 0`, hence `P_σ(x) = 0`). -/
noncomputable def avgDev {n k t : ℕ} {X : Type} [Fintype X] (P : MemProtocol n k t X)
    (σ : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ) : ℝ :=
  ∑ x, (P.weight (rhoMM n t) x).re *
    |(P.weight σ x).re / (P.weight (rhoMM n t) x).re - 1|

end StabTestMem


