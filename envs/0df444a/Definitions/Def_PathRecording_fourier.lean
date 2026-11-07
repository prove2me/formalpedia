-- Prove2me | Definitions.Def_PathRecording_fourier
-- name    : PathRecording_fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:08:13.874817+00:00
-- url     : https://prove2.me/theorems/fbf58090-95a2-40d2-a920-d5d1dd0a70e3
-- title:
--   $L^2(G)$, the oracle $Q_\rho$, the matrix-element map $\Theta_t$ and the truncated Fourier transform
-- statement:
--   Let $G$ be a compact group with a finite Borel measure $\mu$ (in the theorems, the Haar probability measure), and $L^2(G)=L^2(G,\mu)$ with $\langle f_1|f_2\rangle=\int_G\overline{f_1(g)}f_2(g)\,d\mu(g)$.
--
--   1. The initial recording state is $|1\rangle$, the constant function $1$.
--   2. The **uncompressed oracle** on $V\otimes L^2(G)$ is $Q_\rho(|x\rangle\otimes|f\rangle)=\int_G f(g)\,\rho(g)|x\rangle\otimes|g\rangle\,dg$, i.e. the $|y\rangle$-component of $Q_\rho\varphi$ is $\sum_x\langle y|\rho(\cdot)|x\rangle\,\varphi_x$. (4.1)
--   3. The **matrix-element map** $\Theta_t:\mathrm{Path}_t\to L^2(G)$ is
--   $$\Theta_t|\vec x,\vec y\rangle=\int_G\langle\vec y|\rho^{\otimes t}(g)|\vec x\rangle\,|g\rangle\,dg,\qquad(5.13)$$
--   the function $g\mapsto\prod_i\langle y_i|\rho(g)|x_i\rangle$.
--   4. For Schur–Weyl data at $t$, the Fourier basis functions are $F^{-1}|\lambda,X,Y\rangle=\sqrt{d_\lambda}\,\langle Y|\rho_\lambda(\cdot)|X\rangle$ (Definition 3.7), $\lambda\in\widehat G_t$; $F^{-1}(\mathrm{Tab}_t)$ is their span, and the truncated Fourier transform $F_t f=\sum_{\lambda,X,Y}\langle F^{-1}|\lambda,X,Y\rangle\,|\,f\rangle\,|\lambda,X,Y\rangle$ is the $\mathrm{Tab}_t$-component of $Ff$.
--   5. $\Gamma_tF$ denotes $\Gamma_t\circ F_t:L^2(G)\to\mathrm{Path}_t$.
--
--   These are the objects on the uncompressed side of Theorem 5.3.
--
--   **Formalization Note** $L^2(G)$ is `Lp ℂ 2 μ` and $V\otimes L^2(G)$ is `Fin N → Lp ℂ 2 μ`. All functions are continuous and enter $L^2$ through `ContinuousMap.toLp`, so no default value arises. Peter–Weyl's $F$ is not formalized: since $F$ is unitary, the $|\lambda,X,Y\rangle$-coefficient of $Ff$ is $\langle F^{-1}|\lambda,X,Y\rangle\,|\,f\rangle$, and $\Gamma_t$ vanishes outside $\mathrm{Tab}_t$, so $\Gamma_t\cdot F=\Gamma_t\cdot F_t$.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Definitions 3.2–3.3, p.31; Definition 3.7, p.32; §4.1, Eq. (4.1), p.47; Eq. (5.13), p.64; Tab_t, p.62

import Mathlib
import Definitions.Def_PathRecording_Gamma

set_option autoImplicit false

namespace PathRecording

/-!
# `L²(G)`, the uncompressed oracle `Q_ρ`, the matrix-element map `Θ_t` and the truncated Fourier map

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2:

* Definitions 3.2–3.3, p.31: `|f⟩ = ∫_G f(g)|g⟩ dg`, `⟨f₁|f₂⟩ = ∫_G \overline{f₁(g)} f₂(g) dg`; `L²(G)` is
  the space of square-integrable functions.
* §4.1, p.47: the recording register is `L²(G)`, initialized to `|1⟩` (the constant function `1`);
  a query is `Q_ρ(|x⟩ ⊗ |f⟩) = ∫_G f(g) · ρ(g)|x⟩ ⊗ |g⟩ dg` (4.1), i.e. `Q_ρ = ∫_G ρ(g) ⊗ |g⟩⟨g| dg` (4.2).
* Eq. (5.13), p.64: `Θ_t |x⃗, y⃗⟩ := ∫_G ⟨y⃗|ρ^{⊗t}(g)|x⃗⟩ |g⟩ dg`.
* Definition 3.7, p.32: `F⁻¹|λ, X, Y⟩ = √d_λ ∫_G ⟨Y|ρ_λ(g)|X⟩ |g⟩ dg`.
* p.62: `Tab_t = ⨁_{λ∈Ĝ_t} V^λ_G ⊗ \overline{V^λ_G}`; Theorem 5.3 restricts inputs to `F⁻¹(Tab_t)`.

**Formalization Note.**
* `G` is a compact topological group with Borel σ-algebra and a measure `μ` (in the theorems: the
  Haar probability measure). `L²(G)` is `Lp ℂ 2 μ`; Mathlib's inner product
  `⟪f₁, f₂⟫ = ∫ conj(f₁) f₂ dμ` is the paper's `⟨f₁|f₂⟩`.
* `V ⊗ L²(G)` is `Fin N → Lp ℂ 2 μ` (the component of `|x⟩` is a function of `g`). `Q_ρ` acts by
  `(Q_ρ φ)_y = Σ_x ρ(·)_{y x} · φ_x`, the pointwise multiplication by the continuous matrix entry
  `g ↦ ⟨y|ρ(g)|x⟩` (an `L^∞` function); this is (4.1) extended linearly.
* `Θ_t` and the matrix coefficients are built from continuous functions through
  `ContinuousMap.toLp`, so no junk value enters.
* Peter–Weyl's `F` is not formalized. `F⁻¹(Tab_t)` is `matrixCoeffSpace S`, the span of
  `c_{λXY} = F⁻¹|λ,X,Y⟩ = √(dim V^λ_G) · ⟨Y|ρ_λ(·)|X⟩` for `λ ∈ Ĝ_t`, and `fourierTrunc S f` is the
  `Tab_t` part of `F f`: its `|λ, X, Y⟩` coefficient is `⟨F⁻¹|λ,X,Y⟩ | f⟩ = ⟪c_{λXY}, f⟫` (`F` is
  unitary). Since `Γ_t` vanishes outside `Tab_t`, `Γ_t · F = Γ_t · fourierTrunc`.
-/

open Matrix MeasureTheory
open scoped ENNReal InnerProductSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ}

/-- The constant function `1 ∈ L²(G)`, the initial recording state `|1⟩` (p.47). -/
noncomputable def oneLp : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ (ContinuousMap.const G (1 : ℂ))

/-- The matrix entry `g ↦ ⟨y|ρ(g)|x⟩` as an element of `L^∞(G)`. -/
noncomputable def entryLinf (ρ : UnitaryRep G N) (y x : Fin N) : Lp ℂ ∞ μ :=
  ContinuousMap.toLp ∞ μ ℂ ⟨fun g => ρ.mat g y x, ρ.continuous_mat_apply y x⟩

/-- The uncompressed oracle `Q_ρ` on `V ⊗ L²(G)`: `(Q_ρ φ)_y = Σ_x ⟨y|ρ(·)|x⟩ · φ_x`, i.e.
`Q_ρ(|x⟩ ⊗ |f⟩) = ∫_G f(g) ρ(g)|x⟩ ⊗ |g⟩ dg` (arXiv:2606.30281v2, Eq. (4.1), p.47). -/
noncomputable def oracle (ρ : UnitaryRep G N) (φ : Fin N → Lp ℂ 2 μ) : Fin N → Lp ℂ 2 μ :=
  fun y => ∑ x, (entryLinf μ ρ y x • φ x : Lp ℂ 2 μ)

/-- The path matrix element `g ↦ ⟨y⃗|ρ^{⊗t}(g)|x⃗⟩` for `p = (x⃗, y⃗)`, as an element of `L²(G)`:
`Θ_t|x⃗, y⃗⟩` (arXiv:2606.30281v2, Eq. (5.13), p.64). -/
noncomputable def thetaVec (ρ : UnitaryRep G N) (t : ℕ) (p : PathIdx N t) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ
    ⟨fun g => tensorPow ρ t g p.2 p.1,
      by
        simp only [tensorPow, WildeQIT.Schumacher.tensorPow, Matrix.of_apply]
        exact continuous_finsetProd _ fun i _ => ρ.continuous_mat_apply (p.2 i) (p.1 i)⟩

/-- The matrix-element map `Θ_t : Path_t → L²(G)`, `Θ_t v = Σ_{x⃗,y⃗} v_{x⃗,y⃗} Θ_t|x⃗, y⃗⟩`
(arXiv:2606.30281v2, Eq. (5.13), p.64). -/
noncomputable def theta (ρ : UnitaryRep G N) (t : ℕ) (v : PathIdx N t → ℂ) : Lp ℂ 2 μ :=
  ∑ p, v p • thetaVec μ ρ t p

variable {ρ : UnitaryRep G N} {t : ℕ}

/-- The Fourier basis function `c_{λXY} = F⁻¹|λ, X, Y⟩ = √(dim V^λ_G) · ⟨Y|ρ_λ(·)|X⟩` for
`λ ∈ Ĝ_t` (arXiv:2606.30281v2, Definition 3.7, p.32). -/
noncomputable def matrixCoeff (S : SchurWeylData ρ t) (b : S.TabIdx) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ
    ⟨fun g => ((Real.sqrt (S.dG b.1 : ℝ) : ℝ) : ℂ) * (S.irrep b.1).mat g b.2.2 b.2.1,
      continuous_const.mul ((S.irrep b.1).continuous_mat_apply b.2.2 b.2.1)⟩

/-- `F⁻¹(Tab_t)`: the span of the Fourier basis functions `F⁻¹|λ,X,Y⟩` with `λ ∈ Ĝ_t`
(arXiv:2606.30281v2, p.62–63). -/
noncomputable def matrixCoeffSpace (S : SchurWeylData ρ t) : Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ (Set.range (matrixCoeff μ S))

/-- The truncated Fourier transform `F_t : L²(G) → Tab_t`, the `Tab_t` component of `F f`:
`F_t f = Σ_{λ∈Ĝ_t, X, Y} ⟨F⁻¹|λ,X,Y⟩ | f⟩ |λ, X, Y⟩` (arXiv:2606.30281v2, Definition 3.7, p.32). -/
noncomputable def fourierTrunc (S : SchurWeylData ρ t) (f : Lp ℂ 2 μ) : S.TabIdx → ℂ :=
  fun b => ⟪matrixCoeff μ S b, f⟫_ℂ

/-- The recording-register map `Γ_t · F : L²(G) → Path_t` (arXiv:2606.30281v2, Theorem 5.3, p.63). -/
noncomputable def gammaF (S : SchurWeylData ρ t) (f : Lp ℂ 2 μ) : PathIdx N t → ℂ :=
  S.Gamma *ᵥ fourierTrunc μ S f

end PathRecording


