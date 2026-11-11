-- Prove2me | Definitions.Def_PermInvCC_multislice
-- name    : PermInvCC_multislice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:19.832375+00:00
-- url     : https://prove2.me/theorems/70806812-0342-4bf9-b53d-d4917d5a771b
-- title:
--   Multislices $X_\rho$ and uniform $L^2$ norms
-- statement:
--   For an integer histogram $\rho=(\rho_a)_{a\in[q]}$ of total $N$, the **multislice** is
--   $$X_\rho:=\{x\in[q]^N:\ |\{i:x_i=a\}|=\rho_a\text{ for every }a\}.$$
--   It carries the uniform probability measure, with inner product and norm
--   $$\langle u,v\rangle_X=\frac1{|X|}\sum_{x\in X}u(x)v(x),\qquad \|u\|_{L^2(X)}=\langle u,u\rangle_X^{1/2}.$$
--
--   These are the spaces on which the averaging operators $B_S$ act (Appendix B).
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), App. B.1, p.40, and App. B.3, p.44

import Mathlib
import Definitions.Def_PermInvCC_jointType

namespace PermInvCC

/-- The **multislice** `X_ρ = {x ∈ Σ^N : |{i : x_i = a}| = ρ_a for every a}` of a histogram `ρ`
(Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, App. B.1, p.40), here with
alphabet `Σ = [q]`. -/
def multislice {q : ℕ} (N : ℕ) (ρ : Fin q → ℕ) : Finset (Fin N → Fin q) :=
  Finset.univ.filter fun x => hist x = ρ

/-- The inner product of `L²(X)` for the **uniform probability measure** on a finite set `X`
(App. B.3, p.44): `⟨u, v⟩_X = (1/|X|) ∑_{x∈X} u(x) v(x)`. -/
noncomputable def msInner {α : Type} (X : Finset α) (u v : α → ℝ) : ℝ :=
  (1 / (X.card : ℝ)) * ∑ x ∈ X, u x * v x

/-- The norm `‖u‖_{L²(X)} = ⟨u, u⟩_X^{1/2}` for the uniform probability measure on `X`. -/
noncomputable def msNorm {α : Type} (X : Finset α) (u : α → ℝ) : ℝ :=
  Real.sqrt (msInner X u u)

end PermInvCC


