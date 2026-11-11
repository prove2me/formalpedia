-- Prove2me | Definitions.Def_UnitalMIP_omegaInf
-- name    : UnitalMIP_omegaInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:48.084197+00:00
-- url     : https://prove2.me/theorems/a1aba4cc-ae5d-45aa-a2c7-72d6b5fa478f
-- title:
--   Game value $\mathrm{Val}$, the fixed-resource values $\omega^*_n(G,\psi)$, $\omega^*_\infty(G,\psi)$, $\omega^*(G)$, classical and EPR values
-- statement:
--   A nonlocal game $G=(\mathcal X,\mathcal Y,\mathcal A,\mathcal B,p_G,V)$ has finite question and answer sets, a distribution $p_G$ on $\mathcal X\times\mathcal Y$ and a predicate $V(a,b\mid x,y)\in\{0,1\}$; its question marginals are $p_X(x)=\sum_yp_G(x,y)$, $p_Y(y)=\sum_xp_G(x,y)$. For a bipartite operator $\rho$ and operator families $\mathcal A=(A^x_a)$ for Alice and $\mathcal B=(B^y_b)$ for Bob, the **value** is
--
--   $$
--   \mathrm{Val}^\rho_G(\mathcal A,\mathcal B)=\sum_{x,y,a,b}p_G(x,y)\,V(a,b\mid x,y)\,\mathrm{Tr}\bigl[(A^x_a\otimes(B^y_b)^{T})\rho\bigr],
--   $$
--
--   Bob's operators entering transposed. For a fixed state $\psi$,
--
--   $$
--   \omega^*_n(G,\psi)=\sup_{\mathcal A,\mathcal B}\mathrm{Val}^{\psi^{\otimes n}}_G(\mathcal A,\mathcal B),\qquad \omega^*_\infty(G,\psi)=\sup_{n\ge1}\omega^*_n(G,\psi),
--   $$
--
--   the first supremum over local POVM strategies on $n$ copies. The module also defines the entangled value $\omega^*(G)$ (supremum over all finite-dimensional states and POVMs), the classical value (best deterministic strategy $a=f(x)$, $b=g(y)$), the maximally entangled state $\Phi_d$ and the finite-EPR value (supremum over strategies on finitely many EPR pairs).
--
--   $\omega^*_\infty(G,\psi)$ is the value of a game when the provers share any number of copies of the noisy resource $\psi$ and nothing else.
--
--   **Formalization Note** $\psi^{\otimes n}$ is regrouped so that Alice holds the first factor of every copy (`tensorPow`). The value formula is defined for arbitrary matrix families (the source applies it to approximate strategies, (22)); it takes the real part of the trace. Games and POVMs are the published `MIPRE.Game` and `MIPRE.POVM`. $\omega^*(G)$ allows mixed states on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ for all $d_A,d_B$; $m$ EPR pairs are $\Phi_{2^m}$ on $(\mathbb C^2)^{\otimes m}\otimes(\mathbb C^2)^{\otimes m}$.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), §2.3, (15)–(17), p.15; (22), p.23; (56), p.72; Theorem 5.5, p.73; Proposition 3.9, p.31

import Mathlib
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals

open scoped Matrix

namespace UnitalMIP

/-- The `n`-fold tensor power `ψ^{⊗n}` of a bipartite operator `ψ` on `ℂ^{dA} ⊗ ℂ^{dB}`,
**regrouped** so that Alice holds the first factor of every copy (arXiv:2609.39318, version of
2026-11-03, sha256 56ebc59e…, §2.3, (17), p.15: "the players may use ψ^{⊗n}"). Its rows and columns
are indexed by pairs `(a, b)` with `a : Fin n → dA` (Alice's `n` registers) and `b : Fin n → dB`
(Bob's), and
`ψ^{⊗n}_{(a,b),(a',b')} = ∏_i ψ_{(a_i,b_i),(a'_i,b'_i)}`.

**Formalization Note** The plain Kronecker power `ψ ⊗ ψ ⊗ ⋯` would interleave Alice's and Bob's
registers; this is the same operator after the permutation that collects Alice's registers first. -/
def tensorPow {dA dB : Type} (ψ : Matrix (dA × dB) (dA × dB) ℂ) (n : ℕ) :
    Matrix ((Fin n → dA) × (Fin n → dB)) ((Fin n → dA) × (Fin n → dB)) ℂ :=
  Matrix.of fun p q => ∏ i, ψ (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- The **value** of a strategy (arXiv:2609.39318, version of 2026-11-03, (16), p.15, and (22),
p.23): for a game `G = (𝒳, 𝒴, 𝒜, ℬ, p_G, V)`, a bipartite operator `ρ` and families of operators
`A^x_a` on Alice's space and `B^y_b` on Bob's,
`Val^ρ_G(A, B) = ∑_{x,y,a,b} p_G(x,y) V(a,b|x,y) Tr[(A^x_a ⊗ (B^y_b)^T) ρ]`.
Bob's operators enter transposed (footnote 2, p.15).

**Formalization Note** The families are arbitrary matrix families, not only POVMs, because the
source applies the same formula (22) to the approximate strategies `((Q^x_a)†Q^x_a)_a` of block
approximants ("although its value need not be a probability"). The game is the published
`MIPRE.Game` (`μ` = `p_G`, `D` = `V` with `true` = 1). The value is the real part of the trace,
which is the trace itself for positive semidefinite families and a state `ρ`. -/
noncomputable def val {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {dA dB : Type} [Fintype dA] [Fintype dB] (G : MIPRE.Game X Y A B)
    (ρ : Matrix (dA × dB) (dA × dB) ℂ) (SA : X → A → Matrix dA dA ℂ)
    (SB : Y → B → Matrix dB dB ℂ) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
    (Matrix.trace (Matrix.kronecker (SA x a) (SB y b)ᵀ * ρ)).re

/-- The operators of a family of POVMs (`MIPRE.POVM`), as matrices. -/
def povmMats {X A d : Type} [Fintype A] [Fintype d] [DecidableEq d] (S : X → MIPRE.POVM A d) :
    X → A → Matrix d d ℂ :=
  fun x a => ((S x).mats a : Matrix d d ℂ)

/-- The question marginals `p_X(x) := ∑_y p_G(x,y)` and `p_Y(y) := ∑_x p_G(x,y)`
(arXiv:2609.39318, version of 2026-11-03, (15), p.15). This is `p_X`. -/
def pX {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) (x : X) : ℝ := ∑ y, G.μ x y

/-- The question marginal `p_Y(y) := ∑_x p_G(x,y)` (arXiv:2609.39318, (15), p.15). -/
def pY {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) (y : Y) : ℝ := ∑ x, G.μ x y

/-- `ω*_n(G, ψ) := sup_{𝒜,ℬ} Val^{ψ^{⊗n}}_G(𝒜, ℬ)` (arXiv:2609.39318, version of 2026-11-03,
sha256 56ebc59e…, (17), p.15): the supremum over all local POVM strategies on `n` copies of the
fixed resource `ψ`, Alice measuring her `n` registers (`Fin n → dA`) and Bob his (`Fin n → dB`).

**Formalization Note** The POVMs are the published `MIPRE.POVM` (positive semidefinite operators
summing to the identity), with arbitrary finite outcome sets `A`, `B`. The supremum is the real
`iSup`; for a state `ψ` the values lie in `[0, 1]`, so it is the supremum of a bounded set (when
the answer sets are nonempty; with an empty answer set there is no strategy and the value is `0`). -/
noncomputable def omegaN {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (G : MIPRE.Game X Y A B) (ψ : Matrix (dA × dB) (dA × dB) ℂ) (n : ℕ) : ℝ :=
  ⨆ (SA : X → MIPRE.POVM A (Fin n → dA)) (SB : Y → MIPRE.POVM B (Fin n → dB)),
    val G (tensorPow ψ n) (povmMats SA) (povmMats SB)

/-- `ω*_∞(G, ψ) := sup_{n ≥ 1} ω*_n(G, ψ)` (arXiv:2609.39318, version of 2026-11-03, sha256
56ebc59e…, (17), p.15): the value of `G` when the provers may share any finite number `n ≥ 1` of
copies of the fixed state `ψ` and nothing else.

**Formalization Note** The supremum ranges over `n ≥ 1` only, as printed (`n = 0` would allow no
shared state at all). -/
noncomputable def omegaInf {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (G : MIPRE.Game X Y A B) (ψ : Matrix (dA × dB) (dA × dB) ℂ) : ℝ :=
  ⨆ n : {n : ℕ // 1 ≤ n}, omegaN G ψ n.1

/-- The entangled value `ω*(G)` (arXiv:2609.39318, version of 2026-11-03, §2.3, p.15: "the
supremum of its acceptance probabilities over all finite-dimensional bipartite shared states and
all local POVM strategies").

**Formalization Note** The shared state is any density matrix on `ℂ^{dA} ⊗ ℂ^{dB}` with
`dA, dB` arbitrary natural numbers (`Fin dA × Fin dB`), mixed states allowed; the measurements are
POVMs (`MIPRE.POVM`). This is not the published `MIPRE.quantumValue`, which uses pure states and
projective measurements. -/
noncomputable def omegaStar {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v : ℝ | ∃ (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (SA : X → MIPRE.POVM A (Fin dA)) (SB : Y → MIPRE.POVM B (Fin dB)),
    QAlgorithms.IsDensityMatrix ρ ∧ v = val G ρ (povmMats SA) (povmMats SB)}

/-- The **classical value** of a game: the largest acceptance probability of a deterministic
classical strategy `a = f(x)`, `b = g(y)` (arXiv:2609.39318, version of 2026-11-03, Proposition 3.9,
p.31, and its proof, p.70: "the optimal deterministic classical value of the game").

**Formalization Note** Written as `sSup` over the finitely many pairs `(f, g)`; for nonempty
answer sets this is a maximum. Shared randomness does not increase it (a convex combination). -/
noncomputable def classicalValue {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v : ℝ | ∃ (f : X → A) (g : Y → B),
    v = ∑ x, ∑ y, G.μ x y * (if G.D x y (f x) (g y) then 1 else 0)}

/-- The maximally entangled state `Φ_d = |Φ_d⟩⟨Φ_d|`, `|Φ_d⟩ = d^{−1/2} ∑_i |i, i⟩`, on
`ℂ^d ⊗ ℂ^d` with `d = |ι|` (arXiv:2609.39318, version of 2026-11-03, (56), p.72). For
`ι = Fin m → Fin 2` (so `d = 2^m`) it is a tensor product of `m` EPR pairs, regrouped as in
`tensorPow`. -/
noncomputable def maxEnt (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then ((Fintype.card ι : ℂ))⁻¹ else 0

/-- The **finite-EPR value** of a game: the supremum of the acceptance probabilities of POVM
strategies that share finitely many EPR pairs, i.e. the state `Φ_{2^m}` for some `m`
(arXiv:2609.39318, version of 2026-11-03, Theorems 5.5 and 5.6, p.73: "strategies using finitely
many EPR pairs").

**Formalization Note** `m` EPR pairs are `maxEnt (Fin m → Fin 2)`; `m = 0` (no shared pair) is
included, which does not change the supremum since a pair can always be ignored. -/
noncomputable def eprValue {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v : ℝ | ∃ (m : ℕ) (SA : X → MIPRE.POVM A (Fin m → Fin 2))
    (SB : Y → MIPRE.POVM B (Fin m → Fin 2)),
    v = val G (maxEnt (Fin m → Fin 2)) (povmMats SA) (povmMats SB)}

end UnitalMIP


