-- Prove2me | Definitions.Def_LowErrExt_IsRobStrongRegular
-- name    : LowErrExt_IsRobStrongRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:17.737462+00:00
-- url     : https://prove2.me/theorems/78b2903a-c015-4423-b71d-5bd4b749ed6c
-- title:
--   $\delta$-robust and strong $\varepsilon$-multi-regularity
-- statement:
--   Let $f:A\times B\to G'$ with $G'$ a finite abelian group, and let $\mathbf X$, $\mathbf Y$ be independent sources on $A$, $B$.
--
--   1. $\Psi$ is **$\delta$-robustly and strongly $\varepsilon$-biased** on $(\mathbf X,\mathbf Y)$ if for all events $A'$, $B'$ with $\Pr[\mathbf X\in A']\ge\delta$ and $\Pr[\mathbf Y\in B']\ge\delta$, writing $\mathbf X'=\mathbf X|_{\mathbf X\in A'}$, $\mathbf Y'=\mathbf Y|_{\mathbf Y\in B'}$,
--   $$\mathbb E_{y\sim\mathbf Y'}\big[|\mathbb E[\Psi(\mathbf X',y)]|\big]\le\varepsilon\quad\text{and}\quad\mathbb E_{x\sim\mathbf X'}\big[|\mathbb E[\Psi(x,\mathbf Y')]|\big]\le\varepsilon .$$
--   2. $f$ is **$\delta$-robustly and strongly $\varepsilon$-regular** on $(\mathbf X,\mathbf Y)$ if for **every** character $\psi:G'\to\mathbb C^\times$, either $|\mathbb E[\psi(f(\mathbf X,\mathbf Y))]|=1$ (structure), or $\psi\circ f$ is $\delta$-robustly and strongly $\varepsilon$-biased on $(\mathbf X,\mathbf Y)$ (randomness).
--
--   **Formalization Note** A subsource of deficiency $\log(1/\delta)$ is a conditioning on an event of probability at least $\delta$ (Definition 2.2). Characters are additive characters $G'\to\mathbb C$, whose values are roots of unity.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definitions 7.2–7.4, pp.51–52

import Mathlib
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_strongBias

namespace LowErrExt

/-- **`δ`-robustly and strongly `ε`-biased.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 7.2, p.52: "We say that Ψ is δ-robustly and strongly ε-biased on (X, Y) if for all
X′ ⊆_{log(1/δ)} X and Y′ ⊆_{log(1/δ)} Y, E_{y∼Y′}[|E[Ψ(X′, y)]|] ≤ ε, and E_{x∼X′}[|E[Ψ(x, Y′)]|] ≤ ε."

**Formalization Note.** A subsource of deficiency `log(1/δ)` is `X | X ∈ A′` for an event with
`Pr[X ∈ A′] ≥ 2^{−log(1/δ)} = δ` (Definition 2.2, p.10). Conditioning only depends on
`A′ ∩ supp(X)`, so `A′` ranges over all sets. -/
def IsRobStrongBiased {A B : Type*} (δ ε : ℝ) (X : PMF A) (Y : PMF B) (Ψ : A → B → ℂ) : Prop :=
  ∀ (A' : Set A) (B' : Set B), δ ≤ probOf X A' → δ ≤ probOf Y B' →
    strongBiasRight (condOn X A') (condOn Y B') Ψ ≤ ε ∧
      strongBiasLeft (condOn X A') (condOn Y B') Ψ ≤ ε

/-- **`δ`-robust and strong `ε`-multi-regularity.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definitions 7.3–7.4, p.52: "We say f is … ε-regular on (X, Y) with respect to ψ if: • Structure:
ψ ◦ f is constant on (X, Y); or • Randomness: ψ ◦ f is (… δ-robustly and strongly) ε-biased on
(X, Y)", and multi-regularity asks this "with respect to every character ψ : G → C×". "Constant"
means |E[Ψ(X, Y)]| = 1 (p.52).

`IsRobStrongRegular δ ε f X Y`: for every character `ψ` of `G′`, either `|E ψ(f(X, Y))| = 1` or
`ψ ∘ f` is `δ`-robustly and strongly `ε`-biased on `(X, Y)`.

**Formalization Note.** Characters are `AddChar G′ ℂ`; on a finite group their values are roots
of unity, i.e. they are the paper's homomorphisms `G′ → C×`. The disjunction is inside `∀ ψ`. -/
def IsRobStrongRegular {A B G' : Type*} [AddCommGroup G'] (δ ε : ℝ) (f : A × B → G')
    (X : PMF A) (Y : PMF B) : Prop :=
  ∀ ψ : AddChar G' ℂ,
    ‖pairExp X Y (fun x y => ψ (f (x, y)))‖ = 1 ∨
      IsRobStrongBiased δ ε X Y (fun x y => ψ (f (x, y)))

end LowErrExt


