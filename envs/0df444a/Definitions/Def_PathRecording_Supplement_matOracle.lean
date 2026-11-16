-- Prove2me | Definitions.Def_PathRecording_Supplement_matOracle
-- name    : PathRecording_Supplement_matOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:28:27.451227+00:00
-- url     : https://prove2.me/theorems/553e94aa-3230-4e40-a1d1-0764ecd5e892
-- title:
--   The purified oracle $Q_M$ of a continuous matrix-valued function; $Q_{\rho^\top}$, $Q_{\rho^*}$, $Q_{\rho^\dagger}$
-- statement:
--   Let $G$ be a compact group with a finite Borel measure, let $V$ have a finite orthonormal basis $B(V)$, and let $M:G\to\mathrm{End}(V)$ be continuous. The **purified oracle** of $M$ acts on $V\otimes L^2(G)$ by
--   $$Q_M\Big(|x\rangle\otimes\int_G f(g)\,|g\rangle\,dg\Big)=\int_G f(g)\,M(g)|x\rangle\otimes|g\rangle\,dg ,$$
--   that is, writing a vector of $V\otimes L^2(G)$ as $\sum_x |x\rangle\otimes\varphi_x$, the $|y\rangle$-component of $Q_M\varphi$ is $\sum_x \langle y|M(\cdot)|x\rangle\,\varphi_x$.
--
--   For a continuous unitary representation $\rho:G\to U(N)$ this gives the uncompressed oracle $Q_\rho$ of Eq. (4.1) and its three variants: the **transpose** oracle $Q_{\rho^\top}$, which applies $\rho(g)^\top$ (transpose in the fixed basis $B(V)$, so $\langle y|\rho(g)^\top|x\rangle=\langle x|\rho(g)|y\rangle$), the **conjugate** oracle $Q_{\rho^*}$, which applies the entrywise complex conjugate $\rho(g)^*$, and the **inverse** oracle $Q_{\rho^\dagger}$, which applies $\rho(g)^\dagger=\rho(g^{-1})$.
--
--   These are the oracles that the paper's simulators for transpose, conjugate and inverse queries must reproduce.
--
--   **Formalization Note** $V\otimes L^2(G)$ is a function from the basis of $V$ to $L^2(G)$; the entries of $M$ act as $L^\infty$ multipliers. With $M=\rho$ and basis $\{1,\dots,N\}$ the oracle is the published `PathRecording.oracle`.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, §4.1, Eq. (4.1), p.47; Theorem 5.8, p.67 (Q_{ρ⊤}); §3.3.1, p.33 (ρ(g)*)

import Mathlib
import Definitions.Def_PathRecording_UnitaryRep

set_option autoImplicit false

namespace PathRecording.Supplement

/-!
# The purified oracle `Q_M` of a continuous matrix-valued function

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, §4.1, Eq. (4.1), p.47 (`Q_ρ(|x⟩ ⊗ |f⟩) = ∫_G f(g) ρ(g)|x⟩ ⊗ |g⟩ dg`) and
Theorem 5.8, p.67 (`Q_{ρ⊤}(|x⟩ ⊗ ∫ f(g)|g⟩dg) = ∫ f(g) ρ(g)⊤|x⟩ ⊗ |g⟩dg`).

**Formalization Note.**
* For a continuous `M : G → Matrix n n ℂ` (`n` a finite basis of the query register `V`), the
  oracle `Q_M` acts on `V ⊗ L²(G) = n → L²(G)` by `(Q_M φ)_y = Σ_x M(·)_{y x} · φ_x`, the pointwise
  multiplication by the continuous entry functions (as `L^∞` functions). This is (4.1) with `ρ`
  replaced by `M`, extended linearly. For `n = Fin N` and `M = ρ` it is the published
  `PathRecording.oracle`.
* The three variants of §4.1 and §1 (p.9) are `ρ(g)⊤` (`transposeMap`, transpose in the fixed
  basis `B(V)`), `ρ(g)*` (`conjMap`, entrywise complex conjugate) and `ρ(g)†` (`adjMap`).
-/

open Matrix MeasureTheory
open scoped ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasure μ] [CompactSpace G]

/-- The entry function `g ↦ M(g)_{y x}` as an element of `L^∞(G)`. -/
noncomputable def entryLinf' {n : Type*} (M : C(G, Matrix n n ℂ)) (y x : n) : Lp ℂ ∞ μ :=
  ContinuousMap.toLp ∞ μ ℂ
    ⟨fun g => M g y x, (continuous_apply x).comp ((continuous_apply y).comp M.continuous)⟩

/-- The purified oracle `Q_M` on `V ⊗ L²(G)`: `(Q_M φ)_y = Σ_x M(·)_{y x} · φ_x`, i.e.
`Q_M(|x⟩ ⊗ ∫ f(g)|g⟩dg) = ∫ f(g) M(g)|x⟩ ⊗ |g⟩ dg` (arXiv:2606.30281v2, Eq. (4.1), p.47; p.67). -/
noncomputable def matOracle {n : Type*} [Fintype n] (M : C(G, Matrix n n ℂ))
    (φ : n → Lp ℂ 2 μ) : n → Lp ℂ 2 μ :=
  fun y => ∑ x, (entryLinf' μ M y x • φ x : Lp ℂ 2 μ)

variable {N : ℕ}

/-- `g ↦ ρ(g)` as a continuous matrix-valued map. -/
def repMap (ρ : UnitaryRep G N) : C(G, Matrix (Fin N) (Fin N) ℂ) :=
  ⟨fun g => ρ.mat g, continuous_subtype_val.comp ρ.continuous_toHom⟩

/-- `g ↦ ρ(g)⊤`, the transpose in the fixed basis `B(V)` (arXiv:2606.30281v2, p.67):
`⟨y|ρ(g)⊤|x⟩ = ⟨x|ρ(g)|y⟩`. -/
def transposeMap (ρ : UnitaryRep G N) : C(G, Matrix (Fin N) (Fin N) ℂ) :=
  ⟨fun g => (ρ.mat g)ᵀ, Continuous.matrix_transpose (repMap ρ).continuous⟩

/-- `g ↦ ρ(g)*`, the entrywise complex conjugate (arXiv:2606.30281v2, p.33):
`⟨y|ρ(g)*|x⟩ = \overline{⟨y|ρ(g)|x⟩}`. -/
def conjMap (ρ : UnitaryRep G N) : C(G, Matrix (Fin N) (Fin N) ℂ) :=
  ⟨fun g => (ρ.mat g).map star, Continuous.matrix_map (repMap ρ).continuous continuous_star⟩

/-- `g ↦ ρ(g)†`, the conjugate transpose: `⟨y|ρ(g)†|x⟩ = \overline{⟨x|ρ(g)|y⟩}`. -/
def adjMap (ρ : UnitaryRep G N) : C(G, Matrix (Fin N) (Fin N) ℂ) :=
  ⟨fun g => (ρ.mat g)ᴴ, Continuous.matrix_conjTranspose (repMap ρ).continuous⟩

end PathRecording.Supplement


