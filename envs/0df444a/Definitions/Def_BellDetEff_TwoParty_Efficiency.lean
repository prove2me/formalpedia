-- Prove2me | Definitions.Def_BellDetEff_TwoParty_Efficiency
-- name    : BellDetEff_TwoParty_Efficiency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:55.34265+00:00
-- url     : https://prove2.me/theorems/003659b7-d30b-4bbd-a8a5-d8cadd7bea96
-- title:
--   Behaviour under detector efficiency η (2), the threshold e(p^NS) and the efficiency bound η*_NS (A3) (pp. 2, 5)
-- statement:
--   This file defines the detection-efficiency layer of Cao and Peng.
--
--   Let $p$ be a behaviour with finite output alphabets $O_A,O_B$ and inputs $x\in\{1,\dots,M_A\}$, $y\in\{1,\dots,M_B\}$, and let $\eta$ be the detector efficiency. Each party's output alphabet is enlarged by an empty output $\Phi$ (a failed detection).
--
--   1. **Behaviour under efficiency $\eta$ (eq. (2)).** For $a\in O_A$, $b\in O_B$,
--   $$\begin{aligned} p_\eta(a,b\mid x,y)&=\eta^2\,p(a,b\mid x,y), & p_\eta(a,\Phi\mid x,y)&=\eta(1-\eta)\textstyle\sum_b p(a,b\mid x,y),\\ p_\eta(\Phi,b\mid x,y)&=\eta(1-\eta)\textstyle\sum_a p(a,b\mid x,y), & p_\eta(\Phi,\Phi\mid x,y)&=(1-\eta)^2.\end{aligned}$$
--   2. **Efficiency threshold (Appendix A).** $e(p)$ is the largest efficiency at which $p_\eta$ can still be simulated by a local hidden variable model:
--   $$e(p):=\sup\{\eta\in[0,1] : p_\eta \text{ can be simulated by an LHV model}\}.$$
--   The set always contains $\eta=0$ (both parties always output $\Phi$), so $0\le e(p)\le 1$.
--   3. **Efficiency bound (eq. (A3)).** With the numbers of inputs fixed,
--   $$\eta^*_{NS}(M_A,M_B):=\inf\{\,e(p) : p \text{ a no-signaling behaviour with } M_A, M_B \text{ inputs and any finite output alphabets}\,\}.$$
--
--   $\eta^*_{NS}$ is the smallest detector efficiency above which some no-signaling behaviour can no longer be explained by local hidden variables; it is the quantity bounded by Theorems 1 and 2 of the paper.
--
--   **Formalization Note** The empty output $\Phi$ is `none` in `Option OA`, `Option OB`. The marginals in $p_\eta(a,\Phi)$ and $p_\eta(\Phi,b)$ are those of $p$ at the actual inputs $(x,y)$; for a no-signaling $p$ they are the paper's $p(a\mid x)$ and $p(b\mid y)$. "Maximal efficiency" is a real supremum `sSup` over a set that is nonempty (it contains $0$) and bounded above by $1$; the paper's infimum is `sInf` of the set of values $e(p)$, where the output alphabets range over `Fin KA`, `Fin KB` for all $K_A,K_B\in\mathbb N$ separately. The set is nonempty whenever $M_A,M_B\ge 1$ (the one-outcome box belongs to it) and bounded below by $0$; it is written as a set, not as an iterated infimum, so no empty index can contribute a junk value $0$.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 2, eq. (2); p. 5, Appendix A, definition of e(p^NS) and eq. (A3)

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Behaviour

namespace BellDetEff.TwoParty

/-- The behaviour `p^NS_η` under detector efficiency `η`, eq. (2), p. 2. Outputs are
`Option OA`, `Option OB`, with `none` the empty output `Φ` of a failed detection:
`p_η(a, b|x, y) = η² p(a, b|x, y)`, `p_η(a, Φ|x, y) = η(1 − η) ∑_b p(a, b|x, y)`,
`p_η(Φ, b|x, y) = η(1 − η) ∑_a p(a, b|x, y)`, `p_η(Φ, Φ|x, y) = (1 − η)²`. The marginals are
those of `p` itself at the actual inputs. -/
noncomputable def withEff {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) (η : ℝ) :
    Option OA → Option OB → Fin MA → Fin MB → ℝ
  | some a, some b, x, y => η ^ 2 * p a b x y
  | some a, none, x, y => η * (1 - η) * ∑ b, p a b x y
  | none, some b, x, y => η * (1 - η) * ∑ a, p a b x y
  | none, none, _, _ => (1 - η) ^ 2

/-- `e(p^NS)` (Appendix A, p. 5): the maximal efficiency `η ∈ [0, 1]` for which `p^NS_η` can be
simulated by an LHV model, taken as a supremum. The set always contains `0`. -/
noncomputable def effThreshold {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) : ℝ :=
  sSup {η : ℝ | 0 ≤ η ∧ η ≤ 1 ∧ LHVSimulable (withEff p η)}

/-- The efficiency bound `η*_NS = inf_{p^NS} e(p^NS)`, eq. (A3), p. 5, with the numbers of inputs
`MA`, `MB` fixed: the infimum of `e(p)` over every no-signaling behaviour `p` with any finite
output alphabets `Fin KA`, `Fin KB`. -/
noncomputable def etaStarNS (MA MB : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ (KA KB : ℕ) (p : Fin KA → Fin KB → Fin MA → Fin MB → ℝ),
    IsBehaviour p ∧ NoSignaling p ∧ e = effThreshold p}

end BellDetEff.TwoParty


