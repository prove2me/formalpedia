-- Prove2me | Definitions.Def_LatticePrepro_Tables_FieldSetup
-- name    : LatticePrepro_Tables_FieldSetup
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:18.726639+00:00
-- url     : https://prove2.me/theorems/7c0182fa-aa4b-453f-aca9-eaf75d832c34
-- title:
--   Field setups: a sample field $\mathbb{S}$ and an extension $K=\mathbb{S}(\gamma)$ of degree $\delta$ (Lemma A.3, Construction A.4)
-- statement:
--   For a prime $p$ and natural numbers $d,\delta$, a *field setup* (`FieldSetup p d δ`) consists of
--
--   1. a finite field $\mathbb{S}$, the *sample field*, which is an $\mathbb{F}_p$-algebra and has exactly $p^d$ elements;
--   2. a field $K$, the *moment field*, which is an algebra over $\mathbb{F}_p$ and over $\mathbb{S}$, compatibly (the scalar actions form a tower $\mathbb{F}_p\to\mathbb{S}\to K$);
--   3. an element $\gamma\in K$ such that
--      - every $x\in K$ equals $f(\gamma)$ for some $f\in\mathbb{S}[X]$ with $\deg f<\delta$, and
--      - $1,\gamma,\dots,\gamma^{\delta-1}$ are linearly independent over $\mathbb{S}$.
--
--   Thus $K=\mathbb{S}(\gamma)$ is an extension of $\mathbb{S}$ of degree $\delta$, with power basis $1,\gamma,\dots,\gamma^{\delta-1}$.
--
--   These are the fields of step 1 of Construction A.4, whose existence (and, in the paper, explicit construction) is Lemma A.3. All the explicit evaluation tables of Appendix A are defined relative to a field setup: coordinates are indexed by $\mathbb{S}$, and moments are evaluations at $\gamma$.
--
--   **Formalization Note**: The structure bundles the two types with their algebraic instances (`Field`, `Fintype`, `DecidableEq`, `Algebra`, `IsScalarTower`). Finiteness of $K$ is not a separate field; it follows from the first property of $\gamma$. Unlike the paper, $\mathbb{S}$ is not presented as $\mathbb{F}_p[X]/(f)$ with a fixed basis, and $\delta$ is not required to be a power of $p$. The degree condition is stated with `natDegree`. The paper writes $\mathbb{K},e,c,\zeta,\mathbb{E}$ for $\mathbb{S},d,\delta,\gamma,K$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma A.3 (\label{lem:explicit-fields}) and Construction A.4, step 1 (\label{step:moment-fields}); Lean: LatticePrepro/Tables/FieldSetup.lean, LatticePrepro.FieldSetup

import Mathlib

/-!
# Field setups for the explicit construction (Lemma A.3, existence part)

The explicit evaluation tables use a *sample field* `𝕊` of size `q = p^d` and an extension
`K = 𝕊(γ)` of degree `δ`, so that every element of `K` is a polynomial of degree `< δ` in `γ`
with coefficients in `𝕊`, and `1, γ, …, γ^{δ-1}` are `𝕊`-linearly independent.

We only need the *existence* of such fields (the paper's Lemma A.3 additionally constructs
them in polynomial time, which we do not formalize).
-/

namespace LatticePrepro

/-- A sample field `𝕊` of size `p^d` and an extension `K = 𝕊(γ)` of degree `δ`. -/
structure FieldSetup (p : ℕ) [Fact p.Prime] (d δ : ℕ) where
  /-- The sample field. -/
  𝕊 : Type
  [field𝕊 : Field 𝕊]
  [fintype𝕊 : Fintype 𝕊]
  [decEq𝕊 : DecidableEq 𝕊]
  [alg𝕊 : Algebra (ZMod p) 𝕊]
  card_𝕊 : Fintype.card 𝕊 = p ^ d
  /-- The moment field. -/
  K : Type
  [fieldK : Field K]
  [algK : Algebra (ZMod p) K]
  [alg𝕊K : Algebra 𝕊 K]
  [tower : IsScalarTower (ZMod p) 𝕊 K]
  /-- The generator `γ`. -/
  γ : K
  /-- Every element of `K` is a polynomial of degree `< δ` in `γ`. -/
  exists_aeval : ∀ x : K, ∃ f : Polynomial 𝕊, f.natDegree < δ ∧ Polynomial.aeval γ f = x
  /-- The powers `1, γ, …, γ^{δ-1}` are `𝕊`-linearly independent. -/
  linearIndependent_pow : LinearIndependent 𝕊 (fun i : Fin δ => γ ^ (i : ℕ))

namespace FieldSetup

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}

attribute [instance] field𝕊 fintype𝕊 decEq𝕊 alg𝕊 fieldK algK alg𝕊K tower

variable (FS : FieldSetup p d δ)

end FieldSetup

end LatticePrepro


