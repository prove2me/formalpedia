-- Prove2me | Definitions.Def_TolProdTest_fprod
-- name    : TolProdTest_fprod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:32.32118+00:00
-- url     : https://prove2.me/theorems/32a27087-0036-44a4-9e71-62c5c7d39abd
-- title:
--   Maximum product fidelity $F_{\mathrm{prod}}(\rho)$
-- statement:
--   Let $\rho$ be an operator on $n$ qudits, $(\mathbb C^d)^{\otimes n}$, written in the computational basis $\{|x\rangle : x\in[d]^n\}$. Its **maximum product fidelity** is
--
--   $$
--   F_{\mathrm{prod}}(\rho)=\max_{|\pi_i\rangle\in\mathbb C^d,\ \||\pi_i\rangle\|_2=1}\ \langle\pi_1|\otimes\cdots\otimes\langle\pi_n|\,\rho\,|\pi_1\rangle\otimes\cdots\otimes|\pi_n\rangle ,
--   $$
--
--   the largest overlap of $\rho$ with a pure product state. For a pure state $|v\rangle$ (identified with $|v\rangle\langle v|$) it is $\max_\pi|\langle\pi|v\rangle|^2$. The module also fixes the basis type `Config n d` of $n$ qudits, unit vectors, and product vectors $(\pi_1\otimes\cdots\otimes\pi_n)(x)=\prod_i\pi_i(x_i)$.
--
--   This is the quantity the tester decides about: Problem 1.1 asks whether $F_{\mathrm{prod}}(\rho)\ge a$ or $\le b$.
--
--   **Formalization Note** The sites form any finite type `S` (the paper's $[n]$ is `Fin n`). The maximum is written as `sSup` of the real part of the quadratic form over unit families; the set is nonempty and bounded and the supremum is attained, so it is the printed maximum.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (2), p.2; §2.1, p.8

import Mathlib

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- The computational basis of `n` qudits of local dimension `d`: a basis string assigns a level
`x i ∈ Fin d` to every site `i : Fin n`. Operators on `(ℂ^d)^{⊗n}` are matrices indexed by `Config n d`
(Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), §2.1, p.7: `H_i = ℂ^d`). -/
abbrev Config (n d : ℕ) : Type := Fin n → Fin d

/-- A vector `v : X → ℂ` is a unit vector: `Σ_x |v x|² = 1` (Euclidean norm, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), §2.1, p.8). -/
def IsUnitVec {X : Type} [Fintype X] (v : X → ℂ) : Prop :=
  ∑ x, ‖v x‖ ^ 2 = 1

/-- The product vector `|π_1⟩ ⊗ ⋯ ⊗ |π_n⟩`, with amplitudes `(prodVec π)(x) = ∏_i π_i(x_i)`. -/
def prodVec {S : Type} [Fintype S] {d : ℕ} (π : S → Fin d → ℂ) : (S → Fin d) → ℂ :=
  fun x => ∏ i, π i (x i)

/-- **Maximum product fidelity**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (2), p.2:
"F_prod(ρ) := max_{|π_i⟩∈C^d, ∥|π_i⟩∥_2=1} ⟨π_1| ⊗ · · · ⊗ ⟨π_n| ρ |π_1⟩ ⊗ · · · ⊗ |π_n⟩."

The sites form a finite type `S` (the paper's `[n]` is `S = Fin n`), and each site has local dimension `d`.

**Formalization Note** The maximum is written as `sSup` over unit families `π` of the real part of the
quadratic form `⟨π|ρ|π⟩ = Σ_{x,y} conj(π(x)) ρ_{xy} π(y)`. For `d ≥ 1` the set is nonempty and bounded (unit
vectors form a compact set), and the supremum is attained, so it is the printed maximum; for a positive
semidefinite `ρ` the quadratic form is real. For a pure state `v` the paper's `F_prod(v)` is
`fprod (Matrix.vecMulVec v (star v))`, the value at `|v⟩⟨v|` (p.8), i.e. `max_π |⟨π|v⟩|²`. Sites are
indexed from `0`. -/
noncomputable def fprod {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (ρ : Matrix (S → Fin d) (S → Fin d) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ π : S → Fin d → ℂ, (∀ i, IsUnitVec (π i)) ∧
    r = (star (prodVec π) ⬝ᵥ (ρ *ᵥ prodVec π)).re}

end TolProdTest


