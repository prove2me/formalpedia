-- Prove2me | Definitions.Def_LindbladShallow_lam
-- name    : LindbladShallow_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:19:06.736141+00:00
-- url     : https://prove2.me/theorems/f30561e8-d91f-47ff-8fef-09e8a66fbc21
-- title:
--   Strengths $\lambda_e$, the strength parameter $\lambda$ and the accuracy parameter $X$
-- statement:
--   For a retained term let $\alpha_e$ (Hamiltonian) and $\beta_e$ (dissipative) be the least dyadic numbers $2^k$, $k\in\mathbb Z$, with
--   $$\alpha_e^2\ge 4\|H_e\|_F^2,\qquad \beta_e^2\ge 4\|J_e\|_F^2,\qquad \|J_e\|_F^2=\sum_\mu\|L_{e\mu}\|_F^2,$$
--   and set $\lambda_e=\alpha_e$ for $e\in I_H$, $\lambda_e=\beta_e^2$ for $e\in I_J$ ($\lambda_e=0$ for a removed term). Then
--   $$\lambda:=\max_{x\in\Lambda}\sum_{e:\,x\in X_e}\lambda_e,\qquad a:=\lambda T,\qquad X:=\max\{2,\ n(1+a)/\epsilon\}.$$
--
--   These are the strength and accuracy parameters of Eq. (2), in terms of which every resource bound of Theorem 2.1 is stated.
--
--   **Formalization Note** The least $k$ with $4^k\ge 4F$ is $\lceil\log_4(4F)\rceil$. The maximum over sites is a fold of $\max$ from $0$; since every load is nonnegative and $n\ge1$, it equals the maximum.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Eq. (2) and the preceding paragraph, p.9

import Mathlib
import Definitions.Def_LindbladShallow_Instance

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The squared Frobenius norm `‖A‖_F² = Tr A†A = Σ |A_{ij}|²` of a `ℚ + iℚ` matrix, a rational
(arXiv:2610.05362, held version sha256 8f4637ef…, p.9). -/
def frobSqQ {d0 m : ℕ} (A : QIMat d0 m) : ℚ :=
  ∑ i, ∑ j, ((A i j).1 ^ 2 + (A i j).2 ^ 2)

/-- The squared Frobenius norm of the term's local operator: `‖H_e‖_F²` for a Hamiltonian term,
and `‖J_e‖_F² = Σ_µ ‖L_eµ‖_F²` for the stacked jump map `J_e ψ = Σ_µ |µ⟩ L_eµ ψ` of a dissipative
term (p.9). -/
def Term.frobSq {P : Params} (t : Term P) : ℚ :=
  match t.data with
  | .ham H => frobSqQ H
  | .jump L => (L.map frobSqQ).sum

/-- The least dyadic scale `2^k`, `k ∈ ℤ`, whose square is at least `4F` (for `F > 0`):
`α_e` with `F = ‖H_e‖_F²`, `β_e` with `F = ‖J_e‖_F²` (arXiv:2610.05362, p.9:
`α_e² ≥ 4‖H_e‖_F²`, `β_e² ≥ 4‖J_e‖_F²`, least in `{2^k : k ∈ ℤ}`).

**Formalization Note** `(2^k)² ≥ 4F ⟺ k ≥ log₄(4F)`, so the least such `k` is `⌈log₄(4F)⌉`
(exact at powers of four). It is used only for `F > 0` (retained terms). -/
noncomputable def dyadicScale (F : ℝ) : ℝ :=
  (2 : ℝ) ^ (⌈Real.logb 4 (4 * F)⌉)

/-- The strength `λ_e` of a term (p.9): `λ_e = α_e` for a retained Hamiltonian term,
`λ_e = β_e²` for a retained dissipative term, and `0` for a removed term. -/
noncomputable def lamE {P : Params} (I : Instance P) (e : Fin I.nT) : ℝ :=
  open Classical in
  if (I.term e).Retained then
    match (I.term e).data with
    | .ham _ => dyadicScale ((I.term e).frobSq : ℝ)
    | .jump _ => dyadicScale ((I.term e).frobSq : ℝ) ^ 2
  else 0

/-- The load `Σ_{e : x ∈ X_e} λ_e` of site `x = Λ[j]`. -/
noncomputable def siteLoad {P : Params} (I : Instance P) (j : Fin I.n) : ℝ :=
  open Classical in
  ∑ e : Fin I.nT, if I.sites.get j ∈ (I.term e).supp then lamE I e else 0

/-- The strength parameter `λ := max_{x ∈ Λ} Σ_{e : x ∈ X_e} λ_e` (arXiv:2610.05362, Eq. (2), p.9).

**Formalization Note** The maximum is a fold of `max` starting at `0`; as every load is `≥ 0` and
`n ≥ 1` for valid inputs, this is the maximum over the sites. -/
noncomputable def lam {P : Params} (I : Instance P) : ℝ :=
  ((List.finRange I.n).map (siteLoad I)).foldr max 0

/-- The accuracy parameter `X := max{2, n(1 + a)/ϵ}` with `a := λT` (arXiv:2610.05362, Eq. (2),
p.9). -/
noncomputable def bigX {P : Params} (I : Instance P) : ℝ :=
  max 2 ((I.n : ℝ) * (1 + lam I * (I.T : ℝ)) / (I.ε : ℝ))

end LindbladShallow


