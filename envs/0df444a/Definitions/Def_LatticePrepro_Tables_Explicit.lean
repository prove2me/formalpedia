-- Prove2me | Definitions.Def_LatticePrepro_Tables_Explicit
-- name    : LatticePrepro_Tables_Explicit
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:23:24.433852+00:00
-- url     : https://prove2.me/theorems/84c80b33-336b-4add-9d4c-2e228ea1ce1a
-- title:
--   Explicit moment representations (the output of Theorem A.8)
-- statement:
--   Let $p$ be a prime and $S,m,B$ natural numbers. An *explicit moment representation* (`ExplicitMomentRepresentation p S m B`) consists of
--
--   1. a field $K$ that is an $\mathbb{F}_p$-algebra (so $K$ has characteristic $p$), the moment field;
--   2. an encoding tuple of length $S$ over $K$: elements $E_0=0,E_1,\dots,E_S\in K$ with $E_1,\dots,E_S$ linearly independent over $\mathbb{F}_p$;
--   3. a moment representation $R$ over $K$ in the sense of Definition 4.4, whose represented coefficient functions are finitely supported functions $f\colon\overline{K}\to\mathbb{F}_p$ on an algebraic closure $\overline{K}$ of $K$;
--   4. a natural number $q$ (the sample field size) such that
--      $$r=B^m,\qquad D=q,\qquad \text{block size}=q^m,\qquad q=p^d\ \text{for some } d\ge1,\qquad B\le q<8p^3\,m\,S\,B,$$
--      where $r$ is the moment parameter of $R$ and $D$ its number of blocks.
--
--   Recall that a moment representation consists of a moment parameter $r\ge2$, evaluation tables $y\in\mathbb{F}_p^{\iota}$ on a finite coordinate set partitioned into $D$ blocks of equal size, an $\mathbb{F}_p$-linear constraint map $C$, and $\mathbb{F}_p$-linear moment maps $\hat\mu_k$ into $K$ for $0\le k\le2r-2$. It satisfies *completeness* (every $\alpha\in K$ has a binary table $y$ with exactly one nonzero entry per block, $C(y)=0$ and $\hat\mu_k(y)=\alpha^k$) and *soundness* (every $y$ with $C(y)=0$ and $2\,\mathrm{wt}(y)<rD$ has a coefficient function $f$ with $\hat\mu_k(y)=\mu_k(f)$ for all $k$ and $D\cdot|\mathrm{supp}\,f|\le2\,\mathrm{wt}(y)$).
--
--   This is the data produced by Construction A.4, with the representation and size guarantees of Theorem A.8. Theorem 4.8 feeds it into the fixed-verifier system of Construction 4.5 and Theorem 4.6.
--
--   **Formalization Note**: Existence is expressed as `Nonempty (ExplicitMomentRepresentation p S m B)`. The Lean encoding tuple is indexed by `Fin (S + 1)` with a leading entry $E_0=0$; the paper's tuple $(\beta_1,\dots,\beta_N)$ corresponds to $(E_1,\dots,E_S)$. The structure records neither that $K$ is finite nor the concrete shape of the construction ($K=\mathbb{S}(\gamma)$, encoding tuple $(0,1,\gamma,\dots,\gamma^{S-1})$, minimal choices of $\delta$ and $q$); these hold for the object built in the proof. Coefficient functions live on the single field $\overline{K}$ (Mathlib's `AlgebraicClosure K`) instead of a finite extension chosen per table, and the constraint matrix is an $\mathbb{F}_p$-linear map. The paper writes $\kappa,\tau,Q,D_{\mathrm{tab}},N,\mathbb{E},\mathsf d,\mathsf a$ for $r,q,q^m,D,S,K,B,m$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem A.8 (\label{thm:moment-representation-construction}), with Definition 4.4 (\label{def:moment-representation}); Lean: LatticePrepro/Tables/Explicit.lean, LatticePrepro.ExplicitMomentRepresentation

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness

/-!
# Explicit moment representations (Construction A.4, Theorem A.8)

For a prime `p` and integers `S ≥ 2`, `m ≥ 1`, `B ≥ 2`, we construct a finite field `K` of
characteristic `p`, an encoding tuple `ε` of length `S` over `K`, and a moment representation
over `K` with

* moment parameter `r = B^m`,
* `D = q` blocks of size `b = q^m`, where `q` is a power of `p` with
  `B ≤ q < 8 · p^3 · m · S · B`.

As in Construction A.4, `K = 𝕊(γ)` has degree `δ` over the sample field `𝕊` of size `q`, where
`δ` is the least power of `p` with `δ ≥ S` and `q` is the least power of `p` with
`q ≥ 8 p m B δ`. The represented coefficient functions live on an algebraic closure `Ω` of `K`.
The output is bundled as an `ExplicitMomentRepresentation`.

The ingredients are the construction (`Tables/Construction.lean`), completeness through the
element tables (`Tables/ElementTable.lean`), the rank analysis of the polynomial matrix
(`Tables/TableSoundness.lean`), and the Hankel reconstruction theorem (`Tables/Hankel.lean`).
-/

namespace LatticePrepro

open Polynomial

/-- The output of Theorem A.8: a field `K` of characteristic `p`, an encoding tuple of length `S`
over `K`, and a moment representation over `K` with `r = B^m` and `q` blocks of size `q^m`, where
`q` is a power of `p` with `B ≤ q < 8 p^3 m S B`. -/
structure ExplicitMomentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ) where
  /-- The moment field. -/
  K : Type
  [fieldK : Field K]
  [algK : Algebra (ZMod p) K]
  /-- The encoding tuple `(0, 1, γ, …, γ^{S-1})`. -/
  ε : EncodingTuple p K S
  /-- The moment representation; coefficient functions live on an algebraic closure of `K`. -/
  R : MomentRepresentation p K (AlgebraicClosure K)
  /-- The sample field size `q`, which is the number of blocks. -/
  q : ℕ
  r_eq : R.r = B ^ m
  numBlocks_eq : R.numBlocks = q
  blockSize_eq : R.blockSize = q ^ m
  q_eq_pow : ∃ d : ℕ, 1 ≤ d ∧ q = p ^ d
  le_q : B ≤ q
  q_lt : q < 8 * p ^ 3 * m * S * B

attribute [instance] ExplicitMomentRepresentation.fieldK ExplicitMomentRepresentation.algK

end LatticePrepro


