-- Prove2me | Definitions.Def_TimeSpaceMA_lambdaForm
-- name    : TimeSpaceMA_lambdaForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:08.23429+00:00
-- url     : https://prove2.me/theorems/d5764d4c-7c21-4db2-a896-d034a48252c2
-- title:
--   The NAND and lookup forms $\gamma$, $\Psi$, $\Lambda$
-- statement:
--   For integers, $b(w):=w(w-1)$ and
--   $$\gamma(w_1,w_2,z):=b(w_1)+b(w_2)+b(w_1+w_2+2z-2).$$
--   For an $H\times H$ bit matrix $X$, the wrong-claim matrix $J_X$ has rows $(a,o)\in[H]\times\{0,1\}$ and columns $b\in[H]$, with $(J_X)_{(a,o),b}=1$ if $o\neq X_{ab}$ and $0$ otherwise. For an integer vector $z$,
--   $$\Psi(z):=\sum_j z_j(z_j-1)+2\Bigl(\sum_j z_j-1\Bigr)^2,$$
--   and for $r\in\mathbb Z^{2H}$, $c\in\mathbb Z^{H}$,
--   $$\Lambda(r,c):=(2H+1)\bigl(\Psi(r)+\Psi(c)\bigr)+2r^{\mathsf T}J_Xc.$$
--   These quadratic forms vanish exactly on correct NAND gates and on correct input lookups (Lemmas 3.2, 3.3).
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), p.9

import Mathlib

namespace TimeSpaceMA

/-- `b(w) := w(w − 1)`; p.9. -/
def bForm (w : ℤ) : ℤ := w * (w - 1)

/-- `γ(w₁, w₂, z) := b(w₁) + b(w₂) + b(w₁ + w₂ + 2z − 2)`; Lemma 3.2, p.9. -/
def gammaForm (w₁ w₂ z : ℤ) : ℤ :=
  bForm w₁ + bForm w₂ + bForm (w₁ + w₂ + 2 * z - 2)

/-- The wrong-claim matrix `J_X`, rows indexed by `(a, o) ∈ [H] × {0,1}`, columns by `b ∈ [H]`:
the entry is `1` if `o ≠ X_{ab}` and `0` otherwise; p.9. -/
def wrongClaim {H : ℕ} (X : Fin H → Fin H → Bool) (p : Fin H × Bool) (b : Fin H) : ℤ :=
  if p.2 ≠ X p.1 b then 1 else 0

/-- The unit-vector form `Ψ(z) := Σ_j z_j(z_j − 1) + 2(Σ_j z_j − 1)²`; p.9. -/
def psiForm {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℤ :=
  ∑ j, z j * (z j - 1) + 2 * (∑ j, z j - 1) ^ 2

/-- The lookup form `Λ(r, c) := (2H + 1)(Ψ(r) + Ψ(c)) + 2 rᵀ J_X c` (Williams, Xi, STOC 2027
submission, manuscript sha256 184c2f95…, p.9). -/
def lambdaForm {H : ℕ} (X : Fin H → Fin H → Bool) (r : Fin H × Bool → ℤ) (c : Fin H → ℤ) : ℤ :=
  (2 * (H : ℤ) + 1) * (psiForm r + psiForm c) + 2 * ∑ p, ∑ b, r p * wrongClaim X p b * c b

end TimeSpaceMA


