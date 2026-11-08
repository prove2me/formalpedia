-- Prove2me | Definitions.Def_AffDisp4n_SimpleOutput
-- name    : AffDisp4n_SimpleOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:32.673434+00:00
-- url     : https://prove2.me/theorems/0f1cad45-340a-48e2-aa63-1e712c3b1d46
-- title:
--   The two output forms of Lemma 2.2, given by their affine functions
-- statement:
--   An affine function is given by its coefficients: $\ell(u) = \sum_j \lambda_j u_j + \kappa$. An output form is either (i) an affine function $\ell$, or (ii) $(\ell_1 + \alpha)(\ell_2 + \beta) + \gamma$, with $\ell_1, \ell_2$ affine and $\alpha, \beta, \gamma \in \mathbb F_2$. Each form computes a function of the parameters.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), Lemma 2.2 and its proof, p.17

import Mathlib

namespace AffDisp4n

/-- An **affine function of the parameters given by its coefficients** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), proof of Lemma 2.2, p.17: "We represent an affine function by its coefficients, that is, we write
ℓ(u) = ∑ⱼ λⱼuⱼ + κ"). -/
structure AffForm (m : ℕ) where
  /-- the coefficients `λⱼ` -/
  coef : Fin m → ZMod 2
  /-- the constant term `κ` -/
  κ : ZMod 2

/-- The value of an affine function given by its coefficients. -/
def AffForm.eval {m : ℕ} (ℓ : AffForm m) (u : Fin m → ZMod 2) : ZMod 2 :=
  ∑ j, ℓ.coef j * u j + ℓ.κ

/-- The **two output forms of Lemma 2.2, given by their affine functions** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), Lemma 2.2, p.17: "(i) an affine function of the parameters, or (ii) a literal of an AND-type
gate whose two parents are affine functions of the parameters. Given these affine functions, …"). -/
inductive SimpleOutput (m : ℕ) where
  /-- form (i): the affine function `ℓ` -/
  | affine (ℓ : AffForm m)
  /-- form (ii): `(ℓ₁ + α)(ℓ₂ + β) + γ` -/
  | andType (ℓ₁ ℓ₂ : AffForm m) (α β γ : ZMod 2)

/-- The function of the parameters computed by an output of one of the two forms. -/
def SimpleOutput.eval {m : ℕ} : SimpleOutput m → (Fin m → ZMod 2) → ZMod 2
  | .affine ℓ, u => ℓ.eval u
  | .andType ℓ₁ ℓ₂ α β γ, u => (ℓ₁.eval u + α) * (ℓ₂.eval u + β) + γ

end AffDisp4n


