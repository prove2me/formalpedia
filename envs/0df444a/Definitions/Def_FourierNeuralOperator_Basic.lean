-- Prove2me | Definitions.Def_FourierNeuralOperator_Basic
-- name    : FourierNeuralOperator_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T04:34:14.767211+00:00
-- url     : https://prove2.me/theorems/213a03a8-a709-4573-aef5-779a706439bc
-- title:
--   Fourier neural operators, $\Psi$-FNOs and Sobolev spaces on the torus
-- statement:
--   Objects of Sections 2 and 3.1 and Appendix B of Kovachki, Lanthaler and Mishra (2021).
--
--   1. **Torus and Fourier coefficients.** The torus $\mathbb T^d$ is identified with the box $[0,2\pi]^d$, with Lebesgue measure $dx$. A function $v:\mathbb T^d\to\mathbb R^{\iota}$ (finitely many components) has Fourier coefficients $\hat v_k=(2\pi)^{-d}\int_{\mathbb T^d}v(x)e^{-i\langle k,x\rangle}\,dx$, $k\in\mathbb Z^d$ (eq. B.1), and $\mathcal K_N=\{k\in\mathbb Z^d:|k|_\infty\le N\}$ (eq. 2.10).
--   2. **Function spaces (Appendix B).** $v\in L^2$ if every component is square integrable, with $\|v\|_{L^2}=(\int_{\mathbb T^d}|v(x)|^2dx)^{1/2}$. For $s\ge0$, $\|v\|_{H^s}^2=\frac{(2\pi)^d}{2}\sum_{k\in\mathbb Z^d}(1+|k|^{2s})|\hat v_k|^2$ (eq. B.3, $|k|$ Euclidean), and $H^s=\{v\in L^2:\|v\|_{H^s}<\infty\}$. $L^2_N$ is the space of real trigonometric polynomials $\sum_{|k|_\infty\le N}c_ke^{i\langle k,x\rangle}$ (eq. B.5). A continuous operator $G:H^s\to H^{s'}$ maps $H^s$ into $H^{s'}$ and is continuous for the two norms; a compact $K\subset H^s$ is a subset of $H^s$ in which every sequence has a subsequence converging in $H^s$ to a point of $K$.
--   3. **Projections.** $P_Nv=\sum_{|k|_\infty\le N}\hat v_ke^{i\langle k,x\rangle}$ (eq. B.6). On the grid $x_j=2\pi j/(2N+1)$, $j\in\mathcal J_N=\{0,\dots,2N\}^d$, the discrete Fourier transform is $\mathcal F_N(v)(k)=(2N+1)^{-d}\sum_{j\in\mathcal J_N}v(x_j)e^{-i\langle k,x_j\rangle}$, and the pseudo-spectral projection $\mathcal I_Nv=\sum_{|k|_\infty\le N}\mathcal F_N(v)(k)e^{i\langle k,x\rangle}$ is the trigonometric polynomial of degree $\le N$ that interpolates $v$ on the grid (eqs. B.9-B.14).
--   4. **Activation (Assumption 2.4).** $\sigma:\mathbb R\to\mathbb R$ is not a polynomial, is globally Lipschitz and is $C^3$.
--   5. **FNO (eqs. 2.1, 2.2, 2.5-2.7, Definition 2.13).** An FNO of finite width with lift $d_v$, depth $L$ and width $W$ is
--   $$\mathcal N(a)=\mathcal Q\circ\mathcal L_L\circ\cdots\circ\mathcal L_1\circ\mathcal R(a),\quad \mathcal R(a)(x)=Ra(x),\quad\mathcal Q(v)(x)=Qv(x),$$
--   $$\mathcal L_\ell(v)(x)=\sigma\Big(W_\ell v(x)+b_\ell(x)+\mathcal F^{-1}\big(P_\ell(k)\,\hat v_k\big)(x)\Big),$$
--   with $R\in\mathbb R^{d_v\times d_a}$, $Q\in\mathbb R^{d_u\times d_v}$, $W_\ell\in\mathbb R^{d_v\times d_v}$, biases $b_\ell\in L^2(\mathbb T^d;\mathbb R^{d_v})$ and Fourier multipliers $P_\ell(k)\in\mathbb C^{d_v\times d_v}$ with $P_\ell(k)=0$ for $|k|_\infty>W$.
--   6. **$\Psi$-FNO (Definitions 2.11, 2.12).** For $N\ge1$, $\mathcal N(a)=\mathcal Q\circ\mathcal I_N\circ\mathcal L_L\circ\mathcal I_N\circ\cdots\circ\mathcal L_1\circ\mathcal I_N\circ\mathcal R(a)$, with $\mathrm{depth}=L$, $\mathrm{lift}=d_v$ and $\mathrm{width}=(2N+1)^dd_v$.
--   7. **Universal approximation properties.** $\mathrm{UA}_{\mathrm{FNO}}(s,s')$: for every continuous $G:H^s\to H^{s'}$, compact $K\subset H^s$ and $\varepsilon>0$ there is an FNO $\mathcal N$, continuous $H^s\to H^{s'}$, with $\sup_{a\in K}\|G(a)-\mathcal N(a)\|_{H^{s'}}\le\varepsilon$. $\mathrm{UA}_{\Psi}(s,s')$: for every such $G$, compact $K\subset H^s$ of continuous functions and $\varepsilon>0$ there is $N_0$ such that for every $N\ge N_0$ some $\Psi$-FNO on the grid of degree $N$ satisfies $\sup_{a\in K}\|G(a)-\mathcal N(a)\|_{H^{s'}}\le\varepsilon$.
--   8. **Darcy problem (eq. 3.5, Setting 3.4).** $\dot H^s$ is the subspace of $H^s$ with $\hat v_0=0$. $C_t$ is the norm of the embedding $H^t\hookrightarrow L^\infty$. $\mathcal A^s_\lambda$ is the set of $a=1+\tilde a\in H^s$ with $\|a\|_{H^s}\le\lambda^{-1}$ and $\|\tilde a\|_{L^\infty}\le C_{d/2+\delta}\|\tilde a\|_{H^{d/2+\delta}}\le1-\lambda$. $u$ solves $-\nabla\cdot(a\nabla u)=f$, $\fint u=0$, if $u\in\dot H^1$, $\nabla u\in L^2$, and $-\sum_j ik_j\,\widehat{(a\,\partial_ju)}_k=\hat f_k$ for every $k\in\mathbb Z^d$.
--
--   **Formalization Note** A function on $\mathbb T^d$ is a function on $\mathbb R^d$ and only its values on $[0,2\pi]^d$ matter. The norms $\|\cdot\|_{L^2}$, $\|\cdot\|_{H^s}$ and $\|\cdot\|_{L^\infty}$ take values in $[0,\infty]$. The paper requires $P_\ell(-k)=P_\ell(k)^\dagger$ for real outputs. The correct condition is $P_\ell(-k)=\overline{P_\ell(k)}$, and the layers take the real part of $\mathcal F^{-1}(P_\ell\hat v)$ instead. Over all $P_\ell$ this gives exactly the class of layers satisfying the correct condition. FNOs are taken of finite width (Definition 2.13); the proofs construct only such FNOs. $\mathcal F_N$ uses the phase $\langle k,x_j\rangle=2\pi\langle j,k\rangle/(2N+1)$ of the grid. The paper's eq. (B.13) prints $2\pi\langle j,k\rangle/N$, which does not give an inverse pair with (B.14).
-- source:
--   Kovachki, Lanthaler and Mishra, On universal approximation and error bounds for Fourier Neural Operators, arXiv:2107.07562v1 (2021), Section 2.3 (eqs. (2.1), (2.2), (2.5)-(2.7)), Assumption 2.4, Definitions 2.11-2.13, Section 3.1 (eq. (3.5), Setting 3.4), Appendix B (eqs. (B.1)-(B.14))

import Mathlib

/-!
Kovachki, Lanthaler and Mishra, *On universal approximation and error bounds for Fourier Neural
Operators*, arXiv:2107.07562v1 (2021): the periodic setting of Appendix B (Fourier coefficients,
`L²`, the Sobolev spaces `H^s(𝕋^d)`, Fourier and pseudo-spectral projections), Fourier neural
operators (Section 2.3, eqs. (2.1), (2.2), (2.5)-(2.7), Definition 2.13), `Ψ`-FNOs
(Definitions 2.11 and 2.12), the activation hypotheses (Assumption 2.4) and the Darcy setting of
Section 3.1 (eq. (3.5), Setting 3.4).

The torus `𝕋^d` is identified with the box `[0, 2π]^d`, as in Section 2.3: a function on the
torus is a function on `ℝ^d`, and only its values on the box enter the norms below. A vector-valued
function `𝕋^d → ℝ^ι` is a map `(Fin d → ℝ) → ι → ℝ`.
-/

open MeasureTheory

noncomputable section

namespace FourierNeuralOperator

/-- Functions on the torus `𝕋^d` with values in `ℝ^ι`. -/
abbrev TorusFun (d : ℕ) (ι : Type) : Type := (Fin d → ℝ) → ι → ℝ

/-- Section 2.3 and Appendix B: the torus `𝕋^d` identified with the box `[0, 2π]^d`. -/
def torusBox (d : ℕ) : Set (Fin d → ℝ) := Set.Icc 0 (fun _ => 2 * Real.pi)

/-- Lebesgue measure on the box `[0, 2π]^d`, the measure `dx` of Appendix B. -/
abbrev torusMeasure (d : ℕ) : Measure (Fin d → ℝ) := volume.restrict (torusBox d)

/-- Eq. (2.10): the wavenumbers `𝒦_N = {k ∈ ℤ^d : |k|_∞ ≤ N}`. -/
def freqBox (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- The pairing `⟨k, x⟩ = ∑_i k_i x_i` of a wavenumber and a point. -/
def pairing {d : ℕ} (k : Fin d → ℤ) (x : Fin d → ℝ) : ℝ := ∑ i, (k i : ℝ) * x i

/-- The Fourier mode `e^{i⟨k, x⟩}` of Appendix B. -/
def fourierChar {d : ℕ} (k : Fin d → ℤ) (x : Fin d → ℝ) : ℂ :=
  Complex.exp ((pairing k x : ℂ) * Complex.I)

/-- Eq. (B.1): the `k`-th Fourier coefficient
`v̂_k = (2π)^{-d} ∫_{𝕋^d} v(x) e^{-i⟨k, x⟩} dx`, taken componentwise. -/
def fourierCoeff {d : ℕ} {ι : Type} (v : TorusFun d ι) (k : Fin d → ℤ) (i : ι) : ℂ :=
  ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ x in torusBox d, (v x i : ℂ) * fourierChar (-k) x

/-- `v ∈ L²(𝕋^d; ℝ^ι)`: every component is square integrable on the torus. -/
def MemL2 {d : ℕ} {ι : Type} (v : TorusFun d ι) : Prop :=
  ∀ i, MemLp (fun x => v x i) 2 (torusMeasure d)

/-- The norm of `L²(𝕋^d; ℝ^ι)`, `‖v‖_{L²} = (∫_{𝕋^d} |v(x)|² dx)^{1/2}` with the Euclidean norm
on `ℝ^ι`, as an extended real (it is `∞` when `v ∉ L²`). -/
def l2Norm {d : ℕ} {ι : Type} [Fintype ι] (v : TorusFun d ι) : ENNReal :=
  (∫⁻ x in torusBox d, ∑ i, ENNReal.ofReal (v x i ^ 2)) ^ ((1 : ℝ) / 2)

/-- Eq. (B.3): the Sobolev norm
`‖v‖_{H^s}² = ((2π)^d / 2) ∑_{k ∈ ℤ^d} (1 + |k|^{2s}) |v̂_k|²`, with `|k|` the Euclidean norm of
`k` and `|v̂_k|² = ∑_i |v̂_{k,i}|²`, as an extended real (it is `∞` when the series diverges). -/
def sobolevNorm {d : ℕ} {ι : Type} [Fintype ι] (s : ℝ) (v : TorusFun d ι) : ENNReal :=
  (∑' k : Fin d → ℤ,
      ENNReal.ofReal ((2 * Real.pi) ^ d / 2 * (1 + (∑ j, ((k j : ℝ)) ^ 2) ^ s)) *
        ∑ i, (‖fourierCoeff v k i‖₊ : ENNReal) ^ 2) ^ ((1 : ℝ) / 2)

/-- Appendix B: `v ∈ H^s(𝕋^d; ℝ^ι)`, i.e. `v ∈ L²` and `‖v‖_{H^s} < ∞`. -/
def MemSobolev {d : ℕ} {ι : Type} [Fintype ι] (s : ℝ) (v : TorusFun d ι) : Prop :=
  MemL2 v ∧ sobolevNorm s v < ⊤

/-- Theorem 2.5: `G` is a continuous operator `H^s(𝕋^d; ℝ^{ι_a}) → H^{s'}(𝕋^d; ℝ^{ι_u})`: it maps
`H^s` into `H^{s'}` and is continuous for the `H^s` and `H^{s'}` norms. -/
def SobolevContinuous {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu] (s s' : ℝ)
    (G : TorusFun d ιa → TorusFun d ιu) : Prop :=
  (∀ a, MemSobolev s a → MemSobolev s' (G a)) ∧
    ∀ a, MemSobolev s a → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ b, MemSobolev s b →
      sobolevNorm s (b - a) < ENNReal.ofReal δ → sobolevNorm s' (G b - G a) < ENNReal.ofReal ε

/-- Theorem 2.5: `K` is a compact subset of `H^s(𝕋^d; ℝ^ι)`: `K ⊆ H^s`, and every sequence in `K`
has a subsequence converging in `H^s` to a point of `K`. -/
def IsSobolevCompact {d : ℕ} {ι : Type} [Fintype ι] (s : ℝ) (K : Set (TorusFun d ι)) : Prop :=
  (∀ a ∈ K, MemSobolev s a) ∧
    ∀ u : ℕ → TorusFun d ι, (∀ n, u n ∈ K) → ∃ a ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => sobolevNorm s (u (φ n) - a)) Filter.atTop (nhds 0)

/-- Eq. (B.5): `v ∈ L²_N(𝕋^d; ℝ^ι)`, i.e. every component of `v` is a (real-valued)
trigonometric polynomial `∑_{|k|_∞ ≤ N} c_k e^{i⟨k, x⟩}`. -/
def IsTrigPoly {d : ℕ} {ι : Type} (N : ℕ) (v : TorusFun d ι) : Prop :=
  ∀ i, ∃ c : (Fin d → ℤ) → ℂ, ∀ x, (v x i : ℂ) = ∑ k ∈ freqBox d N, c k * fourierChar k x

/-- Eq. (B.6): the `L²`-orthogonal Fourier projection
`P_N v = ∑_{|k|_∞ ≤ N} v̂_k e^{i⟨k, x⟩}` (real for real `v`; the real part is taken). -/
def fourierProj {d : ℕ} {ι : Type} (N : ℕ) (v : TorusFun d ι) : TorusFun d ι :=
  fun x i => (∑ k ∈ freqBox d N, fourierCoeff v k i * fourierChar k x).re

/-- Eqs. (B.11)-(B.12): the grid point `x_j = 2πj / (2N+1)`, `j ∈ 𝒥_N = {0, …, 2N}^d`. -/
def gridPoint {d : ℕ} (N : ℕ) (j : Fin d → Fin (2 * N + 1)) : Fin d → ℝ :=
  fun i => 2 * Real.pi * ((j i : ℕ) : ℝ) / (2 * N + 1)

/-- Eq. (B.13): the discrete Fourier transform
`𝓕_N(v)(k) = (2N+1)^{-d} ∑_{j ∈ 𝒥_N} v(x_j) e^{-i⟨k, x_j⟩}`, written with the phase
`⟨k, x_j⟩ = 2π⟨j, k⟩/(2N+1)` of the grid (B.11). -/
def dft {d : ℕ} {ι : Type} (N : ℕ) (v : TorusFun d ι) (k : Fin d → ℤ) (i : ι) : ℂ :=
  ((((2 * N + 1 : ℝ) ^ d)⁻¹ : ℝ) : ℂ) *
    ∑ j : Fin d → Fin (2 * N + 1), (v (gridPoint N j) i : ℂ) * fourierChar (-k) (gridPoint N j)

/-- Eqs. (B.9)-(B.10): the pseudo-spectral projection `ℐ_N v`, the trigonometric polynomial
of degree `≤ N` that interpolates `v` on the grid `{x_j}_{j ∈ 𝒥_N}`, written as
`∑_{|k|_∞ ≤ N} 𝓕_N(v)(k) e^{i⟨k, x⟩}` (real for real `v`; the real part is taken). -/
def interp {d : ℕ} {ι : Type} (N : ℕ) (v : TorusFun d ι) : TorusFun d ι :=
  fun x i => (∑ k ∈ freqBox d N, dft N v k i * fourierChar k x).re

/-- Assumption 2.4: the activation `σ` is non-polynomial, globally Lipschitz and `C³`. -/
def IsActivation (σ : ℝ → ℝ) : Prop :=
  (¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x) ∧ (∃ L : NNReal, LipschitzWith L σ) ∧
    ContDiff ℝ 3 σ

/-- Eq. (2.5): the Fourier multiplier `𝓕^{-1}(P(k) · 𝓕(v)(k))` with coefficients supported in
`|k|_∞ ≤ W`; the real part is taken, which realises the reality condition on `P` (see the
Formalization Note of the definitions). -/
def fourierMultiplier {d n : ℕ} (W : ℕ) (P : (Fin d → ℤ) → Matrix (Fin n) (Fin n) ℂ)
    (v : TorusFun d (Fin n)) : TorusFun d (Fin n) :=
  fun x i => (∑ k ∈ freqBox d W, ∑ j, P k i j * fourierCoeff v k j * fourierChar k x).re

/-- Eqs. (2.1), (2.2), (2.6), (2.7) and Definition 2.13: a Fourier neural operator of finite
width `𝒩 = 𝒬 ∘ ℒ_L ∘ ⋯ ∘ ℒ_1 ∘ ℛ`, with lifting `ℛ(a)(x) = R a(x)`, projection
`𝒬(v)(x) = Q v(x)`, and layers `ℒ_ℓ(v)(x) = σ(W_ℓ v(x) + b_ℓ(x) + 𝓕^{-1}(P_ℓ(k) 𝓕(v)(k))(x))`
whose Fourier multipliers vanish for `|k|_∞ > modes`. The biases are `L²` functions on the
torus. -/
structure FNO (d : ℕ) (ιa ιu : Type) [Fintype ιa] [Fintype ιu] where
  /-- The lifting dimension `d_v`. -/
  lift : ℕ
  /-- The depth `L`. -/
  depth : ℕ
  /-- The width `W` of Definition 2.13: `P_ℓ(k) = 0` for `|k|_∞ > W`. -/
  modes : ℕ
  /-- The lifting matrix `R ∈ ℝ^{d_v × d_a}`. -/
  R : Matrix (Fin lift) ιa ℝ
  /-- The projection matrix `Q ∈ ℝ^{d_u × d_v}`. -/
  Q : Matrix ιu (Fin lift) ℝ
  /-- The weight matrices `W_ℓ ∈ ℝ^{d_v × d_v}`. -/
  W : Fin depth → Matrix (Fin lift) (Fin lift) ℝ
  /-- The bias functions `b_ℓ(x)`. -/
  b : Fin depth → TorusFun d (Fin lift)
  /-- The Fourier multipliers `P_ℓ(k) ∈ ℂ^{d_v × d_v}`. -/
  P : Fin depth → (Fin d → ℤ) → Matrix (Fin lift) (Fin lift) ℂ
  /-- The biases belong to `L²(𝕋^d; ℝ^{d_v})`. -/
  b_memL2 : ∀ ℓ, MemL2 (b ℓ)

/-- Eq. (2.7): the `ℓ`-th layer `ℒ_ℓ` of an FNO with activation `σ`. -/
def FNO.layer {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu] (Nn : FNO d ιa ιu)
    (σ : ℝ → ℝ) (ℓ : Fin Nn.depth) (v : TorusFun d (Fin Nn.lift)) : TorusFun d (Fin Nn.lift) :=
  fun x i => σ ((Nn.W ℓ).mulVec (v x) i + Nn.b ℓ x i + fourierMultiplier Nn.modes (Nn.P ℓ) v x i)

/-- Eq. (2.6): the operator `𝒩(a) = 𝒬 ∘ ℒ_L ∘ ⋯ ∘ ℒ_1 ∘ ℛ(a)` defined by an FNO. -/
def FNO.eval {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu] (Nn : FNO d ιa ιu)
    (σ : ℝ → ℝ) (a : TorusFun d ιa) : TorusFun d ιu :=
  let v₀ : TorusFun d (Fin Nn.lift) := fun x => Nn.R.mulVec (a x)
  let vL := (List.finRange Nn.depth).foldl (fun v ℓ => Nn.layer σ ℓ v) v₀
  fun x => Nn.Q.mulVec (vL x)

/-- Definition 2.11: a `Ψ`-FNO, i.e. the parameters of an FNO together with the degree
`N ≥ 1` of the pseudo-spectral projections inserted between its layers. -/
structure PsiFNO (d : ℕ) (ιa ιu : Type) [Fintype ιa] [Fintype ιu] extends FNO d ιa ιu where
  /-- The degree `N` of the grid `{x_j}_{j ∈ 𝒥_N}`. -/
  grid : ℕ
  /-- `N ∈ ℕ`, `N ≥ 1`. -/
  grid_pos : 0 < grid

/-- Eq. (2.14): the operator `𝒩(a) = 𝒬 ∘ ℐ_N ∘ ℒ_L ∘ ℐ_N ∘ ⋯ ∘ ℒ_1 ∘ ℐ_N ∘ ℛ(a)` defined by a
`Ψ`-FNO. -/
def PsiFNO.eval {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu] (Np : PsiFNO d ιa ιu)
    (σ : ℝ → ℝ) (a : TorusFun d ιa) : TorusFun d ιu :=
  let v₀ : TorusFun d (Fin Np.lift) := interp Np.grid (fun x => Np.R.mulVec (a x))
  let vL := (List.finRange Np.depth).foldl
    (fun v ℓ => interp Np.grid (Np.toFNO.layer σ ℓ v)) v₀
  fun x => Np.Q.mulVec (vL x)

/-- Definition 2.12: `width(𝒩) = d_v |𝒥_N| = (2N+1)^d d_v`. -/
def PsiFNO.width {d : ℕ} {ιa ιu : Type} [Fintype ιa] [Fintype ιu] (Np : PsiFNO d ιa ιu) : ℕ :=
  (2 * Np.grid + 1) ^ d * Np.lift

/-- Theorem 2.5 and Lemma 2.6: the universal approximation property of FNOs for operators
`H^s → H^{s'}` with activation `σ` (the conclusion of Theorem 2.5): for every continuous
`G : H^s → H^{s'}`, compact `K ⊆ H^s` and `ε > 0` there is an FNO `𝒩`, continuous as an operator
`H^s → H^{s'}`, with `sup_{a ∈ K} ‖G(a) - 𝒩(a)‖_{H^{s'}} ≤ ε`. -/
def UniversalApproxFNO (σ : ℝ → ℝ) (d : ℕ) (ιa ιu : Type) [Fintype ιa] [Fintype ιu]
    (s s' : ℝ) : Prop :=
  ∀ G : TorusFun d ιa → TorusFun d ιu, SobolevContinuous s s' G →
    ∀ K : Set (TorusFun d ιa), IsSobolevCompact s K → ∀ ε : ℝ, 0 < ε →
      ∃ Nn : FNO d ιa ιu, SobolevContinuous s s' (Nn.eval σ) ∧
        ∀ a ∈ K, sobolevNorm s' (G a - Nn.eval σ a) ≤ ENNReal.ofReal ε

/-- Theorem 2.15, in the form used in the proof of Lemma 2.16 (Appendix D.6): for every
continuous `G : H^s → H^{s'}`, compact `K ⊆ H^s` (of continuous functions) and `ε > 0` there is
`N₀` such that for every `N ≥ N₀` some `Ψ`-FNO on the grid of degree `N` approximates `G` on `K`
to accuracy `ε` in `H^{s'}`. -/
def UniversalApproxPsiFNO (σ : ℝ → ℝ) (d : ℕ) (ιa ιu : Type) [Fintype ιa] [Fintype ιu]
    (s s' : ℝ) : Prop :=
  ∀ G : TorusFun d ιa → TorusFun d ιu, SobolevContinuous s s' G →
    ∀ K : Set (TorusFun d ιa), IsSobolevCompact s K → (∀ a ∈ K, ContinuousOn a (torusBox d)) →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ Np : PsiFNO d ιa ιu, Np.grid = N ∧
        ∀ a ∈ K, sobolevNorm s' (G a - Np.eval σ a) ≤ ENNReal.ofReal ε

/-- Appendix B: `v̂_0 = 0`, i.e. `v` has mean zero (`v ∈ L̇²`, `Ḣ^s`). -/
def MeanZero {d : ℕ} {ι : Type} (v : TorusFun d ι) : Prop := ∀ i, fourierCoeff v 0 i = 0

/-- The norm `‖v‖_{L^∞(𝕋^d)}` (essential supremum on the torus of the largest component). -/
def linftyNorm {d : ℕ} {ι : Type} [Fintype ι] (v : TorusFun d ι) : ENNReal :=
  eLpNorm v ⊤ (torusMeasure d)

/-- Setting 3.4: the norm `C` of the embedding `H^t(𝕋^d) ↪ L^∞(𝕋^d)`,
`C = sup {‖v‖_{L^∞} : ‖v‖_{H^t} ≤ 1}`. -/
def sobolevEmbConst (d : ℕ) (t : ℝ) : ENNReal :=
  ⨆ (v : TorusFun d (Fin 1)) (_ : MemSobolev t v) (_ : sobolevNorm t v ≤ 1), linftyNorm v

/-- Setting 3.4: the set `𝒜^s_λ(𝕋^d)` of `λ`-coercive coefficients `a = 1 + ã ∈ H^s` with
`‖a‖_{H^s} ≤ λ⁻¹` and `‖ã‖_{L^∞} ≤ C ‖ã‖_{H^{d/2+δ}} ≤ 1 - λ`, `C` the norm of
`H^{d/2+δ} ↪ L^∞`. -/
def darcyCoeffSet (d : ℕ) (s δ lam : ℝ) : Set (TorusFun d (Fin 1)) :=
  {a | MemSobolev s a ∧ sobolevNorm s a ≤ ENNReal.ofReal lam⁻¹ ∧
    linftyNorm (fun x i => a x i - 1) ≤
      sobolevEmbConst d ((d : ℝ) / 2 + δ) * sobolevNorm ((d : ℝ) / 2 + δ) (fun x i => a x i - 1) ∧
    sobolevEmbConst d ((d : ℝ) / 2 + δ) * sobolevNorm ((d : ℝ) / 2 + δ) (fun x i => a x i - 1) ≤
      ENNReal.ofReal (1 - lam)}

/-- Eq. (3.5) and Setting 3.4: `u ∈ Ḣ¹(𝕋^d)` solves the periodic Darcy problem
`-∇ · (a ∇u) = f`, `⨍ u = 0`: `u` has weak gradient `g = ∇u ∈ L²` (`ĝ_{j,k} = i k_j û_k`), and the
Fourier coefficients of `-∇ · (a g)` equal those of `f`: `-∑_j i k_j (a g_j)^_k = f̂_k` for all `k`. -/
def IsDarcySolution {d : ℕ} (a f u : TorusFun d (Fin 1)) : Prop :=
  MemSobolev 1 u ∧ MeanZero u ∧
    ∃ g : Fin d → TorusFun d (Fin 1), (∀ j, MemL2 (g j)) ∧
      (∀ j k, fourierCoeff (g j) k 0 = Complex.I * (k j : ℂ) * fourierCoeff u k 0) ∧
      ∀ k, -(∑ j, Complex.I * (k j : ℂ) * fourierCoeff (fun x i => a x i * g j x i) k 0) =
        fourierCoeff f k 0

end FourierNeuralOperator


