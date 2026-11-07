-- Prove2me | Definitions.Def_HeilmanMax3Cut_Qstab
-- name    : HeilmanMax3Cut_Qstab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:04.180966+00:00
-- url     : https://prove2.me/theorems/fb686913-abf1-4397-9bbf-5a1f667643f2
-- title:
--   Bilinear noise stability $Q^{(n)}_\rho(A,B)$
-- statement:
--   For two triples $A=(A_1,A_2,A_3)$, $B=(B_1,B_2,B_3)$ of subsets of $\mathbb R^n$ and a correlation $\rho$,
--
--   $$Q^{(n)}_\rho(A,B)=\sum_{i=1}^3\int_{\mathbb R^n}1_{A_i}(x)\,T_\rho 1_{B_i}(x)\,d\gamma_n(x).$$
--
--   For a partition $\Omega$, $Q^{(n)}_\rho(\Omega,\Omega)$ is its noise stability: the probability that two $\rho$-correlated standard Gaussian vectors lie in the same cell.
--
--   **Formalization Note** The cells are indexed $0,1,2$ for the paper's $1,2,3$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (52), p.21

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_ouOp
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **Bilinear Gaussian noise stability of two three-set partitions.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (52), p.21:
for partitions `A = (A₁, A₂, A₃)` and `B = (B₁, B₂, B₃)` of `ℝⁿ`,

`Q_ρ^{(n)}(A, B) := ∑_{i=1}^3 ∫_{ℝⁿ} 1_{Aᵢ}(x) T_ρ 1_{Bᵢ}(x) γₙ(x) dx`.

`Q_ρ^{(n)}(Ω, Ω)` is the noise stability of the partition `Ω` at correlation `ρ`.

**Formalization Note.** Cells are indexed by `Fin 3` (the paper's `1, 2, 3` are `0, 1, 2`). The
integrand is a product of an indicator and `T_ρ` of an indicator, both with values in `[0, 1]`,
against a probability measure, so the Bochner integrals are of integrable functions. The value is
defined for any three sets; the theorems apply it to partitions. -/
noncomputable def Qstab (n : ℕ) (ρ : ℝ) (A B : Fin 3 → Set (Space n)) : ℝ :=
  ∑ i, ∫ x, (A i).indicator (fun _ => (1 : ℝ)) x *
    ouOp n ρ ((B i).indicator (fun _ => (1 : ℝ))) x ∂(gaussian n)

end HeilmanMax3Cut


