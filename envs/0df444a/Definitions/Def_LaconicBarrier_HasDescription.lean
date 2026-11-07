-- Prove2me | Definitions.Def_LaconicBarrier_HasDescription
-- name    : LaconicBarrier_HasDescription
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:41.511492+00:00
-- url     : https://prove2.me/theorems/81231a31-0135-41fa-863d-659e934bb1bb
-- title:
--   Advice description complexity
-- statement:
--   A string $D$ **describes a sampler** of a distribution $\mu$ on strings if $D$ is the description of a circuit $C$ with $m$ inputs such that $C(r)$, for uniform $r \in \{0,1\}^m$ and read as a string, has distribution exactly $\mu$.
--
--   An advice mapping $F$ has **description complexity $s_F(\lambda, n)$ on $X$** if for every $\lambda$ and every $x \in X$ the distribution $F(1^\lambda, x)$ has such a description of length at most $s_F(\lambda, |x|)$.
--
--   **Formalization Note** A uniform reduction (Definition 4.16, empty advice) is covered: the circuit without inputs whose single output is the constant $1$ samples the empty string.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.15, p.22; Definition 4.16, p.22

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace LaconicBarrier

/-- The string `D` **describes a sampler** of the distribution `μ`: `D` is the code of a circuit
`C` with `n` inputs such that `C(r)`, for uniform `r ∈ {0,1}ⁿ` and read as a string (`unpadOut`),
has distribution exactly `μ` (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Definition 4.15, p.22: "the map `r ↦ F(1^λ, x; r)` has a Boolean-circuit
description"). -/
def IsSamplerCode (D : List Bool) (μ : PMF (List Bool)) : Prop :=
  ∃ (n : ℕ) (C : MCircuit n), C.code = D ∧
    (PMF.uniformOfFintype (Fin n → Bool)).map (fun r => unpadOut (C.eval (bits r))) = μ

/-- **Advice description complexity** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript
sha256 1af78662…), Definition 4.15, p.22): for every `λ` and `x ∈ X`, the advice distribution
`F(1^λ, x)` has a sampler description of length at most `s_F(λ, |x|)`.

**Formalization Note** A uniform reduction (empty advice, Definition 4.16) is the case
`F(1^λ, x) = δ_ε`, which a circuit without inputs whose single output is the constant `1` samples. -/
def HasDescription (F : ℕ → List Bool → PMF (List Bool)) (X : Set (List Bool))
    (sF : ℕ → ℕ → ℕ) : Prop :=
  ∀ (lam : ℕ), ∀ x ∈ X, ∃ D : List Bool, D.length ≤ sF lam x.length ∧ IsSamplerCode D (F lam x)

end LaconicBarrier


